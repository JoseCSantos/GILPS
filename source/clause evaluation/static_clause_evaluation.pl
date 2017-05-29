%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-09-12
%
%     This module implements predicates for static clause evaluation
%     (static clause evaluation is Prolog's default left to right evaluation)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(static_clause_evaluation,
            [
              identifyFirstFailingLiteralLinear/3,
              static_clause_evaluation/2,
              static_clause_evaluation_on_examples/5,
              % fast_static_clause_evaluation/2 is only to be called by module common_clause_evaluation
              % (it would have package visibility only in Java
              fast_static_clause_evaluation/2
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [example/5]).
:- use_module('../mode declarations/mode_declarations', [recursive_mode_declarations/1]).
:- use_module('../utils/clause', [signature2PredArity/2, list2Body/2, firstNLiterals/3, literals2clause/2]).
:- use_module('../utils/control', [bk_call_goal/2]).
:- use_module('../clause evaluation/common_clause_evaluation', [evaluate_literal/1]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% identifyFirstFailingLiteralLinear(+Clause, +Atom, -LitPos)
%
% Given:
%   Clause: a clause as a list of literals
%   Atom: atom we want to identify the first failing literal
%
% Returns:
%   LitPos: position (1 based) of the first failing literal in ground body (between StartLit and LastLit)
%
% Notes:
%   Notice we do call_count/3 globally and call the literals with just depth_bound_call/2, that's because
%   it's far simpler (and more efficient!) to control the number of resolutions globally.
%   If there is no failing literal, LitPos=0
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

identifyFirstFailingLiteralLinear([Head|_], Atom, 1):-
  Head\=Atom,!.

%identifyFirstFailingLiteralLinear(+Clause, +Atom, -LitPos)
identifyFirstFailingLiteralLinear(Clause, Atom, LitPos):-
  copy_term(Clause, [Atom|Body]),
  nb_setval(static_fail_lit_pos, 0),
  (setting(min_resolutions, +inf) ->
      identifyFirstFailingLiteralLinearAux(Body, 2)
    ;
      setting(min_resolutions, MaxResolutionsAllowed),
      call_count(_, _, MaxResolutionsAllowed),
      catch(identifyFirstFailingLiteralLinearAux(Body, 2), call_and_retry_counter, (Status=resolutions_exceeded)),
      call_count_reset
  ),!,
  (Status==resolutions_exceeded ->
     retrieve_static_fail_lit_pos(LitPos)
    ;
     nb_delete(static_fail_lit_pos),
     LitPos=0
  ).

identifyFirstFailingLiteralLinear(_, _, LitPos):-
  % this is activated only if min_resolutions=+inf and the clause fails to be proved
  call_count_reset,
  retrieve_static_fail_lit_pos(LitPos).

%retrieve_static_fail_lit_pos(-LitPos)
retrieve_static_fail_lit_pos(LitPos):-
  nb_getval(static_fail_lit_pos, LitPos),
  nb_delete(static_fail_lit_pos).

%identifyFirstFailingLiteralLinearAux(+Lits, +Index)
identifyFirstFailingLiteralLinearAux([], _):-!. %format("Failing literal pos=~w~n", [LitPos]),!. %StartLit=LastLit
identifyFirstFailingLiteralLinearAux([Lit|Lits], Index):-
  %call(user:Lit),
  evaluate_literal(Lit), % why doesn't depth_bound_call/2 work here ?
  Index1 is Index+1,
  identifyFirstFailingLiteralLinearAux(Lits, Index1).
identifyFirstFailingLiteralLinearAux(_, Index):-
  nb_getval(static_fail_lit_pos, OldIndex),
  Index>OldIndex,
  nb_setval(static_fail_lit_pos, Index), % update failing index
  fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% static_clause_evaluation(+Hypothesis, +Example)
%
% Given:
%   Hypothesis: an hypothesis as a list of literals
%   Example: a ground fact
%
% Succeeds:
%   If Hypothesis entails Example until proof depth ProofDepth. Does not succeed otherwise
%
% Notes:
%   Free variables in Hypothesis do not get bind with constants in Example. We consider that Hypothesis
%   entails example if the proof depth required is <=ProofDepth and <=MaxResolutions
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

static_clause_evaluation(Hypothesis, Example):-
  recursive_mode_declarations(true),!,
  %if hypothesis is recursive, testing entailment is more expensive as we need to assert it
  literals2clause(Hypothesis, HypClause),  %HypClause is hypothesis as a proper well formed clause
  % we could assert the clause once per hypothesis coverage, rather than once per example...
  % but we would have to make sure to retract it later
  % when hypothesis is recursive we have to assert the hypothesis, notice that it's assertz to go to end
  assertz(user:HypClause, Ref), %and then erase(Ref) rather than retract(user:HypClause)
  setting(min_resolutions, MinResolutions),
  (once(bk_call_goal(Example, MinResolutions)) ->
    erase(Ref)
   ;
    erase(Ref),% we have to retract the hypothesis in both cases
    fail
  ).

static_clause_evaluation(Hypothesis, Example):-
  %recursive_mode_declarations(false), %we can ommit this, it's a non recursive Hypothesis
  %format("Testing example:~w~n", [Example]),
  setting(min_resolutions, MinResolutions),
  static_clause_evaluation_aux(Hypothesis, MinResolutions, Example).

static_clause_evaluation_aux([Hypothesis], _, Example):-
  \+(\+(Hypothesis=Example)),!. % if hypothesis is a bodyless clause
static_clause_evaluation_aux([Head|Body], MinResolutions, Example):-
  \+(\+((Head=Example,  % the \+\+ is to don't bind free variables in hypothesis with example
         list2Body(Body, BodyAsGoal),
         once(bk_call_goal(BodyAsGoal, MinResolutions))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% fast_static_clause_evaluation(+Clause, +Example)
%
% Given:
%   Clause: clause to evaluate as a valid Prolog clause (i.e. Head:-Body)
%   Example: example to check for entailment
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fast_static_clause_evaluation(_, Example):-
  recursive_mode_declarations(true),!,
  setting(min_resolutions, MaxResolutions),
  once(bk_call_goal(Example, MaxResolutions)).

fast_static_clause_evaluation(ClauseAsGoal, Example):- %Clause is bodyless
  \+(ClauseAsGoal\=Example), !.

fast_static_clause_evaluation((Head:-Body), Example):-
  \+(\+((
        Head=Example,%Body will get bound with examples
        setting(min_resolutions, MaxResolutions),
        once(bk_call_goal(Body, MaxResolutions))))).
