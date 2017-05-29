%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                                      %
% Author: Jose Santos <jcas81@gmail.com>                                               %
% Date: 2009-02-10                                                                     %
%                                                                                      %
%     This file centralizes all GILPS output                                           %
%                                                                                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(messages,
            [
              message/2
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]). % to access the verbosity level
:- use_module('../examples/examples', [exampleIDsWeights/2, exampleIDsWeights/3, example/5]). % to access examples weights
:- use_module('../utils/clause', [prettyPrintLiterals/1, skolemize/2]).

% YAP modules
:- use_module(library(charsio), [format_to_chars/3]).
:- use_module(library(lists), [member/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% message(+Situation, +Verbosity, +ListOfParameters)
%
% Given:
%   Situation: a string describing the situation
%   ListOfParameters: a list of the parameters required to output the proper message
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

message(Situation, ListOfParameters):-
  setting(verbose, Verbosity),
  msg(Situation, Verbosity, ListOfParameters),!.
message(_, _). % if there is no message defined for a given verbosity level, or at all, we must succeed anyway

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% msg(+Situation, +Verbosity, +ListOfParameters)
%
% Given:
%   Situation: a string describing the situation
%   Verbosity: level of verbosity (0: minimal, 1: normal, 2: max)
%   ListOfParameters: a list of the parameters required to output the proper message
%
% Notes:
%   message/3 is a system defined predicate
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

msg(examples_loaded, Verbosity, [NumExamples, NumPos, NumNeg]):-
  (Verbosity>=1 ->
    format("~w examples loaded.~n~w positives, ~w negatives.~n", [NumExamples, NumPos, NumNeg])
   ;
    true
  ).

msg(hypotheses_for_example, 0, _):-!.

msg(hypotheses_for_example, 1, [CurExample, NumExamples, _Example, _Hypotheses]):-
  !,
  (newPct(CurExample, NumExamples, Pct)->
    format("~w% (~w/~w) examples processed.~n", [Pct, CurExample, NumExamples])
  ;
    true).

msg(hypotheses_for_example, Verbosity, [CurExample, NumExamples, Example, Hypotheses]):-
  Verbosity>=0,
  Verbosity<4,!,
  length(Hypotheses, NumHypotheses),
  format("Example ~w/~w: ~k. Generated ~w hypotheses.~n", [CurExample, NumExamples, Example, NumHypotheses]).

msg(hypotheses_for_example, 4, [CurExample, NumExamples, Example, Hypotheses]):-
  !,
  msg(hypotheses_for_example, 2, [CurExample, NumExamples, Example, Hypotheses]),
  forall(member(Hypothesis, Hypotheses), prettyPrintLiterals(Hypothesis)). % show the hypothesis

msg(most_compressive_hypothesis, Verbosity, [Hypothesis, TestFold, PosEIDsCov, NegEIDsCov, PosEIDsRemain, NegEIDsRemain]):-
  Verbosity>0,
  format("The following highest scoring hypothesis was generated:~n", []),
  prettyPrintLiterals(Hypothesis),nl,
  exampleIDsWeights(PosEIDsCov, TestFold, PosWeightCov),
  exampleIDsWeights(NegEIDsCov, TestFold, NegWeightCov),
  exampleIDsWeights(PosEIDsRemain, TestFold, PosWeightRemain),
  exampleIDsWeights(NegEIDsRemain, TestFold, NegWeightRemain),
  ANegWeightCov is abs(NegWeightCov),
  ANegWeightRemain is abs(NegWeightRemain),
  format("Total ~w positive and ~w negative weights are covered by it.~n", [PosWeightCov, ANegWeightCov]),
  format("Still ~w positive and ~w negative weights.~n", [PosWeightRemain, ANegWeightRemain]).

msg(non_compressive_example, Verbosity, [ExampleID, RemainPosExampleIDs, RemainNegExampleIDs]):-
  !,Verbosity>1,
  (setting(engine, progolem), setting(progolem_mode, pairs) ->
     true % in pairs mode of progolem it does not make sense to output the example
    ;
     example(ExampleID, Example, _, _, _),
     format("Example ~k did not generate any scoring hypothesis.~n", [Example])
  ),
  length(RemainPosExampleIDs, NumPosRemaining),
  length(RemainNegExampleIDs, NumNegRemaining),
  format("Still ~w positive and ~w negative examples.~n", [NumPosRemaining, NumNegRemaining]).

msg(hypotheses_computed, Verbosity, [ListOfExamples, NumUniqueHypotheses]):-
  Verbosity>=0,
  length(ListOfExamples, NumExamples),
  format("~w unique hypotheses were generated from ~w examples.~n", [NumUniqueHypotheses, NumExamples]).

msg(total_coverage_computed, Verbosity, [NumHypotheses]):-
  Verbosity>=0,
  format("Coverage for ~w unique hypotheses has been computed.~n", [NumHypotheses]).
  %shall we do a verbose mode where we list the hypothesis and their coverage?

msg(hypothesis_coverage_computed, 0, _):-!.

msg(hypothesis_coverage_computed, 1, [CurHypNumber, TotalNumHyps, _, _, _]):-
  !,
  (newPct(CurHypNumber, TotalNumHyps, Pct)->
    format("~w% (~w/~w) hypotheses coverage computed.~n", [Pct, CurHypNumber, TotalNumHyps])
   ;
     true).

msg(hypothesis_coverage_computed, 2, [CurHypNumber, TotalNumHyps, _Hypothesis, PosExamplesIDsCovered, NegExamplesIDsCovered]):-
  !,
  length(PosExamplesIDsCovered, NumPosExamples),
  length(NegExamplesIDsCovered, NumNegExamples),
  exampleIDsWeights(PosExamplesIDsCovered, PosWeight),
  exampleIDsWeights(NegExamplesIDsCovered, NegWeight),
  AbsNegWeight is abs(NegWeight),
  format("Hypothesis ~w/~w. Coverage (weights): ~w (~w) positives, ~w (~w) negatives.~n",
         [CurHypNumber, TotalNumHyps, NumPosExamples, PosWeight, NumNegExamples, AbsNegWeight]).

msg(hypothesis_coverage_computed, Verbose, [CurHypNumber, TotalNumHyps, Hypothesis, PosExamplesIDsCovered, NegExamplesIDsCovered]):-
  Verbose>=3,
  msg(hypothesis_coverage_computed, 2, [CurHypNumber, TotalNumHyps, _, PosExamplesIDsCovered, NegExamplesIDsCovered]),
  format("Clause:~n", []),
  prettyPrintLiterals(Hypothesis),nl.
% do a level 4 where the actual examples covered are shown?

msg(hypothesis_discarded, 0, _):-!.

msg(hypothesis_discarded, 1, [CurHypNumber, TotalNumHyps, _Hypothesis]):-
  msg(hypothesis_coverage_computed, 1, [CurHypNumber, TotalNumHyps, _, _, _]),!.

msg(hypothesis_discarded, 2, [CurHypNumber, TotalNumHyps, _Hypothesis]):-
  format("Hypothesis ~w/~w discarded due to excess negative coverage or minimum accuracy not attained.~n",
         [CurHypNumber, TotalNumHyps]),!.

msg(hypothesis_discarded, Verbosity, [CurHypNumber, TotalNumHyps, Hypothesis]):-
  Verbosity>=3,
  msg(hypothesis_discarded, 2, [CurHypNumber, TotalNumHyps, Hypothesis]),
  format("Clause:~n", []),
  prettyPrintLiterals(Hypothesis),nl.

msg(compute_rmg_pairs, Verbose, []):-
  Verbose>=2,
  setting(progolem_refinement_operator, Ref_Operator),
  format("Computing ~ws pairs...~n", [Ref_Operator]).

msg(rmg_pair, Verbose, [Clause, Example1, Example2, ExID1, ExID2, (Score, NumLits, PosIDsCov, NegIDsCov)]):-
  Verbose>=3,
  setting(progolem_refinement_operator, Ref_Operator),
  exampleIDsWeights(PosIDsCov, PosWeight),
  exampleIDsWeights(NegIDsCov, NegWeight),
  ANegWeight is abs(NegWeight),
  Prec is PosWeight/(PosWeight+ANegWeight),
  format("~w (~w,~w) ([~w,~w]). Score:~w NumLits:~w NewPos:~w Neg:~w Prec:~4g~n",
         [Ref_Operator, Example1, Example2, ExID1, ExID2, Score, NumLits, PosWeight, ANegWeight, Prec]),
  (Verbose>=4->
    format("Clause:~n", []),
    prettyPrintLiterals(Clause),nl).

msg(extended_rmg, Verbosity, [PosExample, PosEID, ARMG_EIDs, NumLits, Score, [TP, FP, _FN, _TN]]):-
  (setting(theory_construction, global) -> Verb is Verbosity-2 ; Verb = Verbosity),
  Verb>=4,
  setting(progolem_refinement_operator, Ref_Operator),
  Prec is TP/(TP+FP),
  format("Extended ~w ~w with ~w (~k). Score=~w NumLits:~w NewPos:~w Neg:~w Prec:~4g~n",
        [Ref_Operator, ARMG_EIDs, PosEID, PosExample, Score, NumLits, TP, FP, Prec]).

msg(best_rmg, Verbosity, [Iter, Score, armg(core(SeedID, GenPosEIDs, Indexs), clause(Clause, ClauseSig)), PosIDsCov, NegIDsCov]):-
  !,
  (setting(theory_construction, global) -> Verb is Verbosity-2 ; Verb = Verbosity),
  (Verb>=2 ->
    length(Clause, NumLiterals),
    exampleIDsWeights(PosIDsCov, PosWeight),
    exampleIDsWeights(NegIDsCov, NegWeight),
    ANegWeight is abs(NegWeight),
    Prec is PosWeight/(PosWeight+ANegWeight),
    setting(progolem_refinement_operator, Ref_Operator),
    format("Best ~w at iter ~w:~w. Score:~4g NumLits:~w NewPos:~w Neg:~w Prec:~4g~n", [Ref_Operator, Iter, GenPosEIDs, Score, NumLiterals, PosWeight, ANegWeight, Prec]),
    (Verb>=5 -> 
        prettyPrintLiterals(Clause),nl,
        (Verb>=6 ->
          format("Indexs from the bottom clause of example ~w: ~w~n", [SeedID, Indexs]),
          (Verb>=7 -> print_clauses(Clause, ClauseSig)  ; true )
         ;
          true
        )
     ;
       true
    )
   ;
    true
  ).

%print_clauses(+Clause, +ClauseSig)
print_clauses(Clause, ClauseSig):- % this is to help parsing results later
  format("hyp(", []),
  skolemize(Clause, Clause1),
  write_term(Clause1, [quoted(true),numbervars(true)]),
  format(").~n", []),
  format("sig(~w).~n", [ClauseSig]).

msg(before_neg_reduction, Verbosity, [Clause, ClauseSig, Score, PosIDsCov, NegIDsCov]):-
  !,
  (setting(theory_construction, global) -> Verb is Verbosity-2 ; Verb = Verbosity),
  (Verb>=1 ->
     length(Clause, NumLiterals),
     exampleIDsWeights(PosIDsCov, PosWeight),
     exampleIDsWeights(NegIDsCov, NegWeight),
     ANegWeight is abs(NegWeight),
     Prec is PosWeight/(PosWeight+ANegWeight),
     format("Before neg reduction. Score:~4g NumLits:~w NewPos:~w, Neg:~w Prec:~4g~n", [Score, NumLiterals, PosWeight, ANegWeight, Prec]),
     %(Verb>=4 -> prettyPrintLiterals(Clause),nl ; true)
     (Verb>=7 -> 
        print_clauses(Clause, ClauseSig)
       ; 
        true
     )
    ;
     true
   ).
msg(after_neg_reduction, Verbosity, [Clause, ClauseSig, Score, NumLiterals, PosWeight, NegWeight]):-  
  !,
  (setting(theory_construction, global) -> Verb is Verbosity-2 ; Verb = Verbosity),
  Verb>=1,
  Prec is PosWeight/(PosWeight+NegWeight),
  format("After neg reduction. Score:~4g NumLits:~w NewPos:~w, Neg:~w Prec:~4g~n", [Score, NumLiterals, PosWeight, NegWeight, Prec]),
  %(Verb>=4 -> prettyPrintLiterals(Clause),nl ; true)
  (Verb>=7 -> 
      print_clauses(Clause, ClauseSig)
    ; 
      true
  ).
msg(theory_constructed, _, [0, _]):- % when there is a fold 0, it's the all training part of a cross_validation_series
  !,
  display_message('Theory constructed from all the training data', '*').

msg(theory_constructed, _, [1, 1]):- % cross_validation_folds=1. i.e. no cross validation
  !,
  msg(theory_constructed, 0, [0, _]).

msg(theory_constructed, 0, [TotalFolds, TotalFolds]):-
  TotalFolds>1,!,
  format("Cross-validation performed.~n",[]).

msg(theory_constructed, _, [NumFold, TotalFolds]):-
  !,
  format("Theory constructed for fold ~w/~w.~n",[NumFold, TotalFolds]).

msg(show_theory_hypotheses, Verbose, [Hypotheses, TestFold]):-
  (TestFold\=(-1)->
    Verbose>=2,
    format_to_chars("Induced Theory for fold ~w", [TestFold], MessageCodes),
    atom_codes(Message, MessageCodes)
   ;
    Verbose>=1,
    Message='Induced General Theory'
  ),
  %MessageCodes is a list of character codes, atom_codes/2 converts it to an atom Message
  display_message(Message, '*'),
  length(Hypotheses, NumHypotheses),
  showHypotheses(Hypotheses, 1, NumHypotheses).

msg(no_good_clause, Verbose, [_TP, _FP, _FN, _TN, _Score]):-
  Verbose>=1,
  format("Clause does not verify at least one constraint (minprec, minpos, cov...).~nNot added to theory.~n", []).
/*
  PosWeightRemain is TP + FN,
  NegWeightRemain is FP + TN,
  format("Considering ~w positive and ~w negative weights for coverage.~n", [PosWeightRemain, NegWeightRemain]).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showTheorySummary(+TheoryResult, +TheoryResult_STDevList,
%                   +TheoryResultMetrics, +TheoryResultMetrics_STDevList,
%                   +MessageType, +TestFold)
%
% Given:
%   TheoryResult: theory result
%   TheoryResult_STDevs: theory result standard deviations
%   TheoryResultMetrics: theory result metrics
%   TheoryResultMetrics_STDevs: theory result metrics standard deviations
%   MessageType: type of message to output
%   TestFold: the fold not used for training the theory
%
% Outputs the theory results on standard output
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

msg(show_theory_summary, Verbose, [TheoryResult, TR_STDs, TheoryResultMetrics, TRM_STDs, MessageType, TestFold]):-
  ((TestFold\=(-1), Verbose>=2);(TestFold=(-1), Verbose>=1)),
  msg(MessageType, Verbose, [TestFold]),
  showConfusionMatrix(TheoryResult, TR_STDs),
  showTheoryResultMetrics(TheoryResultMetrics, TRM_STDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showConfusionMatrix(+TheoryResult, +TheoryResult_STDev)
%
% Given:
%   TheoryResult: A TheoryResult term
%   TheoryResultSTDev: the standard deviation of each element of TheoryResult (optional argument)
%
% Outputs to stdout in the form of a confusion matrix
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

showConfusionMatrix([TruePositivesWeight, FalsePositivesWeight, TrueNegativesWeight, FalseNegativesWeight],
                    [STD_TruePositivesWeight, STD_FalsePositivesWeight, STD_TrueNegativesWeight, STD_FalseNegativesWeight]):-

  AbsTrueNegativesWeight is abs(TrueNegativesWeight), % TrueNegativesWeight is a negative value
  AbsFalsePositivesWeight is abs(FalsePositivesWeight), % FalsePositivesWeight is a negative value
  TotalPredictedPositiveWeight is TruePositivesWeight + AbsFalsePositivesWeight,
  TotalPredictedNegativeWeight is AbsTrueNegativesWeight + FalseNegativesWeight,
  TotalActualPositiveWeight is TruePositivesWeight + FalseNegativesWeight,
  TotalActualNegativeWeight is AbsFalsePositivesWeight + AbsTrueNegativesWeight,
  TotalExamplesWeight is TotalActualPositiveWeight + TotalActualNegativeWeight,% or TotalPredictedPositiveWeight + TotalPredictedNegativeWeight

  STD_TotalPredictedPositiveWeight is STD_TruePositivesWeight + STD_FalsePositivesWeight,
  STD_TotalPredictedNegativeWeight is STD_FalseNegativesWeight + STD_TrueNegativesWeight,
  STD_TotalActualPositiveWeight is STD_TruePositivesWeight + STD_FalseNegativesWeight,
  STD_TotalActualNegativeWeight is STD_FalsePositivesWeight + STD_TrueNegativesWeight,
  STD_TotalExamplesWeight is STD_TotalActualPositiveWeight + STD_TotalActualNegativeWeight,
  Separator = '-----------|-------------------|-------------------|-------------------',
  format("           |                 Actual                |~n", []), % format/2 requires [], even when no arguments are needed
  format(" Predicted |           Positive|           Negative|             Totals~n", []),
  format("~w~n", [Separator]),
  format("   Positive|~t~0f+/-~0f~31+|~t~0f+/-~0f~20+|~t~0f+/-~0f~20+~n",
         [TruePositivesWeight, STD_TruePositivesWeight, AbsFalsePositivesWeight, STD_FalsePositivesWeight,
          TotalPredictedPositiveWeight, STD_TotalPredictedPositiveWeight]),
  format("~w~n", [Separator]),
  format("   Negative|~t~0f+/-~0f~31+|~t~0f+/-~0f~20+|~t~0f+/-~0f~20+~n",
         [FalseNegativesWeight, STD_FalseNegativesWeight, AbsTrueNegativesWeight, STD_TrueNegativesWeight,
          TotalPredictedNegativeWeight, STD_TotalPredictedNegativeWeight]),
  format("~w~n", [Separator]),
  format(" Totals    |~t~0f+/-~0f~31+|~t~0f+/-~0f~20+|~t~0f+/-~0f~20+~2n",
         [TotalActualPositiveWeight, STD_TotalActualPositiveWeight,
          TotalActualNegativeWeight, STD_TotalActualNegativeWeight,
          TotalExamplesWeight, STD_TotalExamplesWeight]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showTheoryResultMetrics(+TheoryResultMetrics, +TheoryResultMetrics_StandardDeviation)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

showTheoryResultMetrics([DefaultAccuracy, ClassifierAccuracy, Recall, Specificity, Precision, CorPredNeg, F1Score, MatthewsCorrelation],
                        [STD_DefaultAccuracy, STD_ClassifierAccuracy, STD_Recall, STD_Specificity, STD_Precision, STD_CorPredNeg, STD_F1Score, STD_MatthewsCorrelation]):-
  format("Default accuracy: ~3g% +/-~1f%~n", [DefaultAccuracy, STD_DefaultAccuracy]),
  format("Classifier accuracy: ~3g% +/-~1f%~n", [ClassifierAccuracy, STD_ClassifierAccuracy]),
  format("Recall/Sensitivity: ~3g% +/-~1f% (% of correctly class. positive examples)~n", [Recall, STD_Recall]),
  format("Specificity: ~3g% +/-~1f% (% of correctly class. negative examples)~n", [Specificity, STD_Specificity]),
  format("Precision: ~3g% +/-~1f% (% of correctly predicted positive examples)~n", [Precision, STD_Precision]),
  format("CorPredNeg: ~3g% +/-~1f% (i.e. % of correctly predicted negative examples)~n", [CorPredNeg, STD_CorPredNeg]),
  format("F1-score: ~3g +/-~2f (i.e. 2*Precision*Recall/(Precision+Recall)~n", [F1Score, STD_F1Score]),
  format("Matthews correlation: ~3g +/-~2f (i.e. (TP*TN-FP*FN)/sqrt((TP+FP)*(TP+FN)*(TN+FP)*(TN+FN)))~n", [MatthewsCorrelation, STD_MatthewsCorrelation]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showHypotheses(+Hypotheses, +CurHypNum, +NumHyps)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

showHypotheses([], N, N).
showHypotheses([Hypothesis|Hypotheses], N, NumHyps):-
  format("Hypothesis ~w/~w:~n", [N, NumHyps]),
  showHypothesis(Hypothesis),
  N1 is N+1,
  showHypotheses(Hypotheses, N1, NumHyps).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showHypothesis(+Hypothesis)
%
% Given:
%   Hypothesis: an hypothesis term of the form: (Hypothesis, HypSig, NumLiterals, NPos, NNeg, NNewPos, NNewNeg)
%
% Outputs the hypothesis on standard output
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

showHypothesis((Hypothesis, _HypSig, NumLiterals, WPos, WNeg, WNewPos, WNewNeg)):-
  AbsWNeg is abs(WNeg), %WNeg is a negative integer (or 0)
  AbsWNewNeg is abs(WNewNeg), %WNewNeg is a negative integer (or 0)
  Prec is WPos*100.0/(WPos+AbsWNeg),
  NewPrec is WNewPos*100.0/(WNewPos+AbsWNewNeg),
  format("#Literals=~d, PosScore=~4g (~4g new), NegScore=~4g (~4g new) Prec=~3g% (~3g% new)~n", [NumLiterals, WPos, WNewPos, AbsWNeg, AbsWNewNeg, Prec, NewPrec]),
  prettyPrintLiterals(Hypothesis),nl.

msg(display_train_theory_results, _, [-1]):-
  !,
  display_message('Train theory statistics (using all examples as training)', '*').

msg(display_train_theory_results, _, [TestFold]):-
  format_to_chars("Train theory statistics (using examples from all folds except ~w)", [TestFold], MessageCodes),
  %MessageCodes is a list of character codes, atom_codes/2 converts it to an atom Message
  atom_codes(Message, MessageCodes),
  display_message(Message, '*').

msg(display_test_theory_results, _, [TestFold]):-
  format_to_chars("Test theory statistics (testing using examples from unseen fold ~w)", [TestFold], MessageCodes),
  %MessageCodes is a list of character codes, atom_codes/2 converts it to an atom Message
  atom_codes(Message, MessageCodes),
  display_message(Message, '*').

msg(display_avg_train_theory_results, _, [-1]):-
  display_message('Average train theory statistics', '*').

msg(display_avg_test_theory_results, _, [-1]):-
  display_message('Average test theory statistics', '*').

msg(session_saved, _, [FileName]):-
  format("Session saved to file ~w~n", [FileName]).

msg(session_loaded, _, [FileName]):-
  format("Session loaded from file ~w~n", [FileName]).

msg(program_stats, _, []):-
  program_stats.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% program_stats/0
%
% Shows some basic cputime and memory used stats
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

program_stats:-
  statistics(program, [P,_]),
  statistics(global_stack, [GS,_]),
  statistics(local_stack, [LS,_]),
  statistics(trail, [T, _]),
  statistics(cputime, [Time, _]),
  RamUsed is P+GS+LS+T,
  format("~nTotal memory used (in bytes): ~D. ", [RamUsed]),
  format("Total cputime (in ms): ~D~n", [Time]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% display_message(+Message, +Char)
%
% Given:
%   Message: a string to display
%   Char: the character to embed the message in
%
% Displays string Message in stdout embedded in a box formed by character, Char
%
% Notes:
%   display/2 is a system defined predicate
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

display_message(Message, Char):-
  atom_length(Message, LenMessage),
  BoxSize is LenMessage+4,
  atom_codes(Char, [CodeChar]),
  format("~n~*c~n",[BoxSize, CodeChar]),
  format("* ~w *~n", [Message]),
  format("~*c~n~n",[BoxSize, CodeChar]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% newPct(+CurNum, +Total, -Percentage)
%
% Given:
%   CurNum: a positive integer up to Total
%   Total: an integer
%
% Returns:
%   Pct: the percentage that CurNum/Total represents BUT
%   only if CurNum*100/Total truncated to integer is bigger than (CurNum-1)*100/Total
%   (that is, the current num is in a new percentage)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

newPct(CurNum, Total, Pct):-
  Pct is integer(CurNum*100/Total),
  Pct > integer((CurNum-1)*100/Total).
