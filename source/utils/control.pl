%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-01-20
%
%     This file contains misc. utility predicates to control execution flow
%     (the ones depending on modules outside of utilities shouldn't be here!)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(utils_control,
            [
               do_finally/3,
               bk_call_goal/2,
               uniqueInterpretations/3,
               measure_resources/4
            ]
         ).

% GILPS modules
:- use_module('goal_solutions', [collect_solutions/4, call_n/2]).
:- use_module('clause', [signature2PredArity/2]).
:- use_module('list', [n_randomElems/3]).
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [example/5]).
:- use_module('../mode declarations/mode_declarations', [mode_head/1, recursive_mode_declarations/1]).

% YAP modules
:- use_module(library(lists), [member/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% do_finally(+Goal, +Action, -Result)
%   Executes Action, no matter whether Goal succeeds or not
%
% Given:
%   Goal: a goal to execute
%   Action: an action to execute
%
% Returns:
%   Result: 'true' in case Goal has succeed, 'fail' otherwise
%
% Notes:
%  Just the first solution of Goal is returned, hence Goal should be determined.
%  Normally Action will be some cleanup predicate that needs to be executed no matter Goal
%  succeeds or not
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate do_finally(:, :, ?).

do_finally(Goal, Action, true):-
  Goal,!,
  Action.

do_finally(_, Action, S):-
  Action,
  S=fail.% it's important to just bind S to 'fail' after Action is executed
         % otherwise this do_finally wouldn't be executed

% consider Goals that are positive examples... we do not consider the number of resolutions to evaluate them
bk_call_atom(Goal, _, _):-
  recursive_mode_declarations(true), % if we are not in recursive mode, there is no need to check this
  signature2PredArity(Goal, Name/Arity),
  mode_head(Head_Signature),
  signature2PredArity(Head_Signature, Name/Arity),% Goal is a recursive call
  setting(sample, Sample),
  example(_, Goal, Weight, _Fold, Rand), % we should be careful about the Fold...
  Rand=<Sample, Weight>0.

% call a single atom from the background knowledge using up to Depth and MaxResolutions
bk_call_atom(Goal, MaxDepth, MaxResolutions):-
  %call(user:Goal). %why depth_bound_call/2 doesn't work here?
  resource_bound_call(Goal, MaxDepth, MaxResolutions, true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% resource_bound_call(+Goal, +MaxDepth, +MaxResolutions, -Status)
%
% Given:
%   Goal: a Prolog goal (maybe a term comma ',' separated)
%   MaxDepth: max depth to prove it
%   MaxResolutions: max resolutions allowed
%
% Returns:
%   Status: either 'true', 'fail' or 'resolutions_exceeded'
%           (false may mean that proof depth was exceeded)
%
% Notes:
%   +1 because MaxResolutions is exclusive
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% it's not true that we will use 0 resolutions when the limit is max_resolutions, but since it doesn't
% matter we return 0
resource_bound_call(Goal, MaxDepth, +inf, Status):-
  !,
  %depth_bound_call(user:Goal, MaxDepth). % why doesn't depth_bound_call/2 work here?
  resource_bound_call_aux(Goal, MaxDepth, +inf, Status).

resource_bound_call(Goal, MaxDepth, MaxResolutions, Status):-
  MaxResolutions1 is MaxResolutions+1,
  call_count(_, _, MaxResolutions1),
  catch((depth_bound_call(user:Goal, MaxDepth)),
        call_and_retry_counter, (Status=resolutions_exceeded)),% catch/3 Action must succeed
  call_count_reset,% to stop counting the resolutions
  (var(Status)-> Status=true ; true).

resource_bound_call(_, _, _, Status):-
  call_count_reset,% to stop counting the resolutions
  Status=fail.% it's important to just bind Status to 'fail' after call_count_reset is executed
              % otherwise the head could fail immediately if Status was bound already to true

resource_bound_call_aux(Goal, _MaxDepth, +inf, true):-
  call_count_reset,
  call(user:Goal).
resource_bound_call_aux(_, _, +inf, fail).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% bk_call_goal(+Goal, +MaxResolutionsGoal)
%
% Given:
%    Goal: a proper Prolog goal to execute (i.e. literals separated by ',')
%
% Returns:
%   MinResolutionsGoal: maximum number of resolutions allowed for goal to succeed
%
% Notes:
%    Goal is to be executed in user space, likely with some variables instantiated, and bounded
%  resources. Goal fails if maximum depth or maximum resolution is exceeded. On success bk_call_goal
%  returns with Goals variables bound.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bk_call_goal(Goal, MaxResolutionsGoal):-
  setting(recall_bound_on_evaluation, +inf),!,
  setting(depth, MaxDepth),
  resource_bound_call(Goal, MaxDepth, MaxResolutionsGoal, true).

bk_call_goal(Goal, MaxResolutionsGoal):-
  setting(recall_bound_on_evaluation, Recall),
  %setting(depth, MaxDepth), % ignore depth
  (MaxResolutionsGoal=(+inf) ->
     bk_call_goal_recall_bounded(Goal)
   ;
     call_count(_, _, MaxResolutionsGoal),
     catch(bk_call_goal_recall_bounded(Goal, Recall), call_and_retry_counter, (Status=resolutions_exceeded)),
     call_count_reset,
     (Status==resolutions_exceeded -> fail ; true)
  ).
/*
bk_call_goal(_, _):-
  !,
  call_count_reset, % to reset the call counter
  fail.
*/

%bk_call_goal_recall_bounded(+Goals, +Recall)
bk_call_goal_recall_bounded((G1,Gs), Recall):-
  !,
  call_n(user:G1, Recall),
  bk_call_goal_recall_bounded(Gs, Recall).
bk_call_goal_recall_bounded(Goal, Recall):-%Goal is a single Goal here
  call_n(user:Goal, Recall).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% uniqueInterpretations(+MaxSolutions, +Predicate, -SolutionsForPredicate)
%
% Given:
%   MaxSolutions: a positive integer
%   Predicate: a user predicate to be called (with input variables instantiated)
%
% Returns:
%   SolutionsForPredicate: a list of the first Recall interpretations for predicate Predicate
%                          where each element has a ground interpretation of Predicate
%
% Notes:
%   Each predicate is called up to depth Depth (user defined setting)
%   SolutionsForPredicate is sorted at the end so that no repeated solutions are returned.
%
%   Suppose Recall=2, Predicate=f(m,X), BK={f1(A), f2(A), f(A,1):-f1(A), f(A,1):-f2(A)}
%
%   Then raw SolutionsForPredicate would be: {f(m,1),f(m,1)}, since we want to return the unique
%   interpretations, we sort SolutionsForPredicate and return {f(m,1)}
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

uniqueInterpretations(MaxSols, Predicate, SolsForPredCall):-
  setting(depth, MaxDepth),
  setting(min_resolutions, MaxResolutions), % we don't need to compute max resolutions allowed as Predicate is a single literal
  uniqueInterpretationsAux(MaxSols, MaxDepth, MaxResolutions, Predicate, SolsForPredCall).

%uniqueInterpretationsAux(+MaxSols, +MaxDepth, +MaxResolutions, +Predicate, -SSolsForPredCall)
uniqueInterpretationsAux(MaxSols, MaxDepth, MaxResolutions, Predicate, SolsForPredCall):-
  setting(randomize_recall, false),!,
  collect_solutions(Predicate,
                    bk_call_atom(Predicate, MaxDepth, MaxResolutions),
                    MaxSols,
                    TSolsForPredCall), % execute Predicate Recall times up to depth bound Depth, in user module
  sort(TSolsForPredCall, SolsForPredCall). % sort to remove repetitions
uniqueInterpretationsAux(MaxSols, MaxDepth, MaxResolutions, Predicate, SolsForPredCall):-
  setting(randomize_recall, true),!,
  findall(Predicate, bk_call_atom(Predicate, MaxDepth, MaxResolutions), TSolsForPredCall), % execute Predicate Recall times up to depth bound Depth, in user module
  sort(TSolsForPredCall, SSolsForPredCall), % eliminate repetitions
  n_randomElems(SSolsForPredCall, MaxSols, SolsForPredCall).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% measure_resources(+Predicate, +NumTimes, -Milliseconds, -RamInBytes)
%
% Given:
%   Predicate: a predicate to execute (possibly in a different module)
%   NumTimes: number of times to execute Predicate
%
% Returns:
%   Milliseconds: number of milliseconds of cpu time required to execute Predicate NumTimes
%   RamInBytes: extra bytes of memory allocated because of Predicate execution
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate measure_resources(:, ?, ?, ?). % first argument must be expanded...

measure_resources(Pred, N, Ms, Ram):-
  statistics(program, [MemUsedBeforeCall, MemFreeBeforeCall]),
  statistics(cputime, [MsBeforeCall, _]),
  measure_resources_aux(N, Pred),
  statistics(cputime, [MsAfterCall, _]), % we could have used the last argument of this list since it is the number of ms before the last call to cputime
                                                           % however, we don't do it because we want the measure to still work if Pred calls itself statistics(cputime, _)
  statistics(program, [MemUsedAfterCall, MemFreeAfterCall]),
  Ms is MsAfterCall - MsBeforeCall, 
  Ram is ((MemUsedAfterCall + MemFreeAfterCall) - (MemUsedBeforeCall + MemFreeBeforeCall)).

:- meta_predicate measure_resources_aux(?, :). % second argument must be expanded

measure_resources_aux(0, _):- !.
measure_resources_aux(N, Pred):-
  call(Pred),!,
  N1 is N-1,
  measure_resources_aux(N1, Pred).
measure_resources_aux(N, Pred):-
  N1 is N-1,%if it fails we want to continue counting
  measure_resources_aux(N1, Pred).
