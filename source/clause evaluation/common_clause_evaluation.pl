%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-09-12
%
%     This module implements predicates that are common for static and dynamic clause evaluation
%     (static clause evaluation is Prolog's default left to right evaluation)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(common_clause_evaluation,
            [
                apply_clause_transformations/3,
                can_use_heuristic_clause_evaluation/1,
                clause_examples_coverage/6,
                entails/3,
                evaluate_literal/1,
                identifyFirstFailingLiteral/4,
                identifyFirstFailingLiteral/5
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]).
:- use_module('../utils/goal_solutions', [call_n/2]).
:- use_module('../utils/clause', [literals2clause/2, cut_transformation/2, once_transformation/2]).
:- use_module('../utils/control', [do_finally/3]).
:- use_module('../examples/examples', [example/5, id2example/2]).
:- use_module('../mode declarations/mode_declarations', [recursive_mode_declarations/1, determinate_transformation/2]).
:- use_module('spd_clause_evaluation', [spd_clause_evaluation/3, spd_preprocess/3, spd_lits_evaluation/1, spd_update_litsinfo/3]).
:- use_module('svd_clause_evaluation', [svd_clause_evaluation/3, svd_preprocess/3, svd_vars_evaluation/1, svd_update_varsinfo/3]).
:- use_module('adv_clause_evaluation', [adv_clause_evaluation/3, adv_clause_evaluation/1, adv_preprocess/3, adv_update_clause_eval_ds/3]).
:- use_module('theta_subsumption', [first_failing_literal/4, theta_subsumes_exampleids/5]).
:- use_module('static_clause_evaluation', [identifyFirstFailingLiteralLinear/3, static_clause_evaluation/2, fast_static_clause_evaluation/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% apply_clause_transformations(+Hypothesis, +HypothesisSignature, -TransfHypothesis)
%
% Given:
%  Hypothesis: a clause as a list of literals
%  HypothesisSignature: Hypothesis signature
%
% Returns:
%  TransfHypothesis: list of literals transformed to take into account the transformations that are active
%  MinResolutionsNeeded: minimum number of resolutions it would take to evaluate TransfHypothesis
%
% Notes:
%   If clause is recursive don't apply any transformation (this is a quick fix to the once/1)
%   where we can't retract the clause previously asserted. i.e. asserta((a:-once(b)) adds
%   clause: a:-once(user:b) to the BK
%
%              apply_clause_transformations/3  % change this predicate to another module (which?)
%                                              % the ideal candidate would be utils/clause but determinate_transformation needs mode declarations...
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

apply_clause_transformations(Hypothesis, HypSig, Hypothesis):-
  can_use_heuristic_clause_evaluation(HypSig),!. % if we can use dynamic clause evaluation, we cannot transform the clause
apply_clause_transformations(Hypothesis, _, Hypothesis):-
  recursive_mode_declarations(true),!.
apply_clause_transformations(Hypothesis, _, Hyp2):-
  (setting(determinate_transformation, true) ->
     determinate_transformation(Hypothesis, Hyp1)
   ;
     Hyp1=Hypothesis),
  (setting(cut_transformation, true) ->
     %cut_transformation(Hyp1, Hyp2)
     once_transformation(Hyp1, Hyp2)
   ;
     Hyp2=Hyp1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% can_use_heuristic_clause_evaluation(+ClauseSig)
%
% Succeeds if it's safe to use spd clause evaluation
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

can_use_heuristic_clause_evaluation(ClauseSig):-
  recursive_mode_declarations(false),
  setting(clause_evaluation, ClauseEvaluation),
  ClauseEvaluation\=left_to_right,
  (ground(ClauseSig);ClauseEvaluation=theta_subsumption).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% evaluate_literal(+Literal)
%
% Given:
%  Literal: a normal Prolog literal
%
% Literal succedes up to recall_bound_on_evaluation times
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

evaluate_literal(Literal):-
  setting(recall_bound_on_evaluation, +inf),!,
  call(user:Literal).
evaluate_literal(Literal):-
  setting(recall_bound_on_evaluation, Recall),
  call_n(user:Literal, Recall).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% identifyFirstFailingLiteral(+Clause, +ClauseSig, +Atom, -FailLitPos)
% identifyFirstFailingLiteral(+Clause, +ClauseSig, +Atom, +AfterPos, -FailLitPos)
%
%
% Given:
%   Clause: list of literals (with head variables needed to be instantiated)
%   ClauseSig: Clause's signatures
%   Atom: atom to test for fail with Clause
%   (optional) AfterPos: indicates where to start the search for the failing literal (inclusive)
%
% Returns:
%   FailLitPos: position (1 based) of the first failing literal of Clause when matched with Atom
%               (between 1 and Length, or between AfterPos and Length), if AfterPos is defined
%               If there is no failing literal 0 is returned. If head is the failing literal 1 is returned,
%               if it's a literal in the body its index is returned (first literal in the body has index 2)
%
% Notes:
%   Defining AfterPos, wherever possible, makes the identification quicker. However, one should only define
%   after pos if it is guaranteed there is no failing literal before AfterPos (exclusive)
%
%   Notice that in many cases the next failing literal is precisely AfterPos. If we set the interval
%   [AfterPos, ClauseLen], the AfterPos would only be tested after log2(ClauseLen-AfterPos) steps
%   making it in average even worse (10% slower) than starting from the initial interval [1,Length]. With
%   this in mind we adjust initial position, so that the first value tested is precisely AfterPos
%   (this is about 10% better than starting from [1,Length])
%
%   This predicate assumes Clause is not recursive. If it were recursive and had not failing literal 
%   before the recursive call, the recursive literal would be returned as the failing literal as the
%   clause is not being asserted to the BK before evaluation. (should we fix this?)
%
%   Cut transformations are disabled because it would complicate this predicate very significantly
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

identifyFirstFailingLiteral(Clause, ClauseSig, Atom, FailLitPos):-
  identifyFirstFailingLiteral(Clause, ClauseSig, Atom, 1, FailLitPos).

%identifyFirstFailingLiteral(+Clause, +ClauseSig, +Atom, +AfterPos, -FailLitPos)
identifyFirstFailingLiteral(Clause, ClauseSig, ExampleID, AfterPos, FailLitPos):-
  id2example(ExampleID, Example),
  (setting(clause_evaluation, theta_subsumption) ->
     first_failing_literal(Clause, ExampleID, AfterPos, FailLitPos)
   ;
     identifyFirstFailingLiteralAux(Clause, ClauseSig, Example, AfterPos, FailLitPos)
  ).

%identifyFirstFailingLiteralAux(+Clause, +ClauseSig, +Atom, +AfterPos, -FailLitPos)
identifyFirstFailingLiteralAux([Head|_], _, Atom, _, 1):- %Atom and head do not match, FailLitPos is 1
  Head\=Atom,!.
identifyFirstFailingLiteralAux(Clause, ClauseSig, Atom, AfterPos, FailLitPos):-
  length(Clause, Len),
  (AfterPos>Len ->  % we have reached end of clause, no further test
     FailLitPos=0
   ;
     AfterPos1 is max(1, min(2*AfterPos-Len, Len)),
     (can_use_heuristic_clause_evaluation(ClauseSig) ->
       identify_first_failing_literal_heuristic(Clause, ClauseSig, Atom, AfterPos1, Len, FailLitPos)
     ;
       %unfortunately it's not easy to conciliate clause transformations and identify first failing literal
       identifyFirstFailingLiteralLinear(Clause, Atom, FailLitPos)
     )
     %format("Failing literal pos for Atom ~w is ~w~n", [Atom, FailLitPos])
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% identify_first_failing_literal_heuristic(+Clause, +ClauseSig, +Atom, +StartPos, +LastPos, -FailLitPos)
%
% Notes:
%  This is done using a binary search algorithm. Note that we only preprocess the clause once, making it
%  more efficient.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

identify_first_failing_literal_heuristic(Clause, [HeadSig|BodySig], Atom, StartLit, LastLit, LitPos):-
  copy_term(Clause, [Atom|Body]), % to don't bind Clause variables
  (setting(clause_evaluation, smallest_predicate_domain) ->
     PreprocessPred = spd_preprocess,
     EvaluatePred = spd_lits_evaluation,
     UpdateInfoPred = spd_update_litsinfo
   ;
     (setting(clause_evaluation, smallest_variable_domain) ->
        PreprocessPred = svd_preprocess,
        EvaluatePred = svd_vars_evaluation,
        UpdateInfoPred = svd_update_varsinfo
      ;
       %setting(clause_evaluation, advanced)
        EvaluatePred = adv_clause_evaluation,
        UpdateInfoPred = adv_update_clause_eval_ds
     )
  ),
  (setting(clause_evaluation, advanced)-> 
     adv_preprocess([Atom|Body], [HeadSig|BodySig], ClauseTerm) 
   ;
     call_with_args(PreprocessPred, Body, BodySig, ClauseTerm)
  ),
%  write(call_with_args(EvaluatePred, ClauseTerm)),nl,
  (\+(\+ once(call_with_args(EvaluatePred, ClauseTerm))) ->
     LitPos=0
   ;
     identify_first_failing_literal_heuristic_aux(EvaluatePred, UpdateInfoPred, ClauseTerm, StartLit, LastLit, LitPos)
  ).

%identify_first_failing_literal_heuristic_aux(+EvaluatePred, +UpdateLitsInfoPred, +ClauseEvalTerm, +StartLit, +LastLit, -LitPos
identify_first_failing_literal_heuristic_aux(_, _, _, LitPos, LitPos, LitPos):- !.%format("Failing literal pos=~w~n", [LitPos]),!. %StartLit=LastLit
identify_first_failing_literal_heuristic_aux(EP, UP, CETerm, StartLit, LastLit, LitPos):-
  LitsUntilCut is (StartLit + LastLit)//2,
  %format("StartLit:~w LastLit:~w LitsUntilCut:~w~n", [StartLit, LastLit, LitsUntilCut]),
  call_with_args(UP, CETerm, LitsUntilCut, TCETerm),
  %format("Trying:~n",[]), portray_clause(TBodyInfo),nl,
  (\+(\+ once(call_with_args(EP, TCETerm))) -> %\+\+ to avoid bounding bodyinfo
   %  format("Success~n",[]),
     NStartLit is LitsUntilCut+1,
     identify_first_failing_literal_heuristic_aux(EP, UP, CETerm, NStartLit, LastLit, LitPos)
   ;
   %  format("Failure~n",[]),
     identify_first_failing_literal_heuristic_aux(EP, UP, CETerm, StartLit, LitsUntilCut, LitPos)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% entails(+Clause, +ClauseSig, +Atom)
%
% Given:
%  Clause: a list of literals
%  ClauseSig: Clause's signature
%  Atom: atom to check for entailment from Clause
%
% Succeeds (just once) if Atom is entailed by Clause, does not bind Clause variables
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

entails(Clause, ClauseSig, Example):-
  can_use_heuristic_clause_evaluation(ClauseSig),!,
  % the \+\+ are to do not bind Hypothesis to a solution if one exists
  (setting(clause_evaluation, smallest_predicate_domain) ->
      \+(\+ once(spd_clause_evaluation(Clause, ClauseSig, Example)))
    ;
    (setting(clause_evaluation, smallest_variable_domain) ->
        \+(\+ once(svd_clause_evaluation(Clause, ClauseSig, Example)))
      ; %setting(clause_evaluation, advanced)
        \+(\+ once(adv_clause_evaluation(Clause, ClauseSig, Example)))
    )
  ).
entails(Clause, _ClauseSig, Example):-
  %\+can_use_heuristic_clause_evaluation(_ClauseSig),
  static_clause_evaluation(Clause, Example).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% clause_examples_coverage(+ExampleIDs, +Hypothesis, +HypothesisSignature, +MaxAbsWeightToCover,
%                          -AbsFinalWeightCovered, -ExampleIDsCovered)
%
% Given:
%   ExampleIDs: ordered list of example ids to test an hypothesis
%   Hypothesis: the hypothesis to test the coverage of
%   HypothesisSignature: signature of Hypothesis
%   MaxAbsWeightToCover: maximum absolute value for the total sum of weights of the examples covered
%
% Returns:
%   AbsFinalWeightcovered: final value for the maximum abs weight coverage
%   ExampleIDsCovered: the examples from ExamplesID that Hypothesis entails (up to depth ProofDepth)
%
% Notes:
%   This predicate fails if AbsCurrentWeightCovered>=MaxAbsWeightCovered.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clause_examples_coverage(ExampleIDs, Clause, _ClauseSig, MAWC, AFWC, CoveredExampleIDs):-
  setting(clause_evaluation, theta_subsumption),!,
  theta_subsumes_exampleids(Clause, ExampleIDs, MAWC, AFWC, CoveredExampleIDs).

clause_examples_coverage(ExampleIDs, Clause, ClauseSig, MAWC, AFWC, CoveredExampleIDs):-
  ((var(ClauseSig);setting(clause_evaluation, left_to_right)) ->
    literals2clause(Clause, ProperClause),  %ClauseAsGoal is a proper well formed Prolog clause
    (recursive_mode_declarations(true) -> assertz(user:ProperClause, Ref) ; true),
    Param1=ProperClause,
    EvalAlg=left_to_right
   ;
    ClauseSig=[_|BodySig],
    copy_term(Clause, [Head|Body]), % to don't bind Clause
    (setting(clause_evaluation, smallest_predicate_domain) ->
       spd_preprocess(Body, BodySig, ClauseTerm),
       EvalAlg=smallest_predicate_domain
     ;
      (setting(clause_evaluation, smallest_variable_domain) ->
         svd_preprocess(Body, BodySig, ClauseTerm),
         EvalAlg=smallest_variable_domain
       ;
         adv_preprocess([Head|Body], ClauseSig, ClauseTerm),
         EvalAlg=advanced
      )
    ),
    Param1=Head
  ),
  %ClauseTerm will not be used if clause_evaluation=left_to_right
  do_finally(clause_examples_coverage_aux(ExampleIDs, EvalAlg, Param1, ClauseTerm, 0, MAWC, AFWC, CoveredExampleIDs), %Goal to execute
             (recursive_mode_declarations(true) -> erase(Ref) ; true), %Action
             true). %succed only if clause_examples_coverage_aux succeeds

%clause_examples_coverage_aux(+ExampleIDs, +EvalAlg, +Head/ProperClause, +ClauseTerm, +CurWeight, +MaxWeight, -FinalWeight, -CoveredExampleIDs)
clause_examples_coverage_aux(_, _, _, _, CurWeight, MaxWeight, _, _):-
  CurWeight>MaxWeight,!,
  fail.
clause_examples_coverage_aux([], _, _, _, FW, _, FW, []).
clause_examples_coverage_aux([EID|EIDs], EvalAlg, Head, ClauseTerm, CW, MW, FW, [EID|CEIDs]):-
  example(EID, Example, Weight, _, _), %retrieve Example from ExampleID
%  format("Testing for entailment of ~w~n", [EID]),
  entailment_test(EvalAlg, Example, Head, ClauseTerm),!,
%  format("Entailed~n", []),
  NCW is CW + abs(Weight),
  clause_examples_coverage_aux(EIDs, EvalAlg, Head, ClauseTerm, NCW, MW, FW, CEIDs).
clause_examples_coverage_aux([_|EIDs], EvalAlg, Head, ClauseTerm, CW, MW, FW, CEIDs):-
  clause_examples_coverage_aux(EIDs, EvalAlg, Head, ClauseTerm, CW, MW, FW, CEIDs).

%entailment_test(+Example, +Head/Hypothesis, +ClauseTerm)
entailment_test(left_to_right, Example, Hypothesis, _ClauseTerm):-
  !,
  fast_static_clause_evaluation(Hypothesis, Example).
entailment_test(smallest_predicate_domain, Example, Head, ClauseTerm):-
  !,
  % bind example to head, this will cause some variables in ClauseTerm to become bound as well
  % \+\+ to avoid binding the variables  
  \+(\+((Head=Example, once(spd_lits_evaluation(ClauseTerm))))).
entailment_test(smallest_variable_domain, Example, Head, ClauseTerm):-
  !,
  \+(\+((Head=Example, once(svd_vars_evaluation(ClauseTerm))))).
entailment_test(advanced, Example, Head, ClauseTerm):-
  !,
  \+(\+((Head=Example,
         once(adv_clause_evaluation(ClauseTerm))
       ))).
