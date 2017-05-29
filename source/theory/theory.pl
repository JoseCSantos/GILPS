%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-04-24
%
%   This file defines the type Theory, TheoryResult and some utility predicates to deal with it
%
%   A Theory is the result of learning and is a tuple of the form: (TotLiterals, PosCovered, NegCovered, Hypotheses)
%
%   where:
%      TotLiterals: total number of literals in all hypothesis in Hypotheses
%      PosCovered: ordered list of all the positive example ids covered by the theory (i.e. the union of the coverage of its hypotheses)
%      NegCovered: ordered list of all the negative example ids covered by the theory (i.e. the union of the coverage of its hypotheses)
%      Hypotheses: list of tuples of the form: (Hypothesis, NumLiterals, NPos, NNeg, NNewPos, NNewNeg)
%
%      where:
%         Hypothesis: is a unique hypothesis (with variables in clause form)
%         NumLiterals: number of literals in hypothesis
%         WPos: weight of positive examples hypothesis covered in the training data
%         WNeg: weight of negative examples hypothesis covered in the training data
%         WNewPos: weight of new positive examples covered (i.e. subtracting the ones covered by the previous hypothesis)
%         WNewNeg: weight of new negative examples covered (i.e. subtracting the ones covered by the previous hypothesis)
%
%   The order of the hypotheses in the Theory is important. The first hypotheses are the most discriminating ones
%
%
%  A TheoryResult is the summary of applying a given Theory to a set of examples. It's a list of the form:
%     [TruePositivesWeight, FalsePositivesWeight, TrueNegativesWeight, FalseNegativesWeight]
%
%  From this tuple we can calculate TheoryResultMetrics, which is a tuple of the form:
%     [DefaultAccuracy, ClassifierAccuracy, Recall, Specificity, Precision, CorPredNeg, F1Score, MatthewsCorrelation]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(theory,
           [
             output_theory2file/1,
             %predicates to deal with TheoryResult and TheoryResultMetrics 
             numElementsInTheoryResult/1,
             numElementsInTheoryResultMetrics/1,
             theoryResult2Metrics/2,
             compute_theory_result/7,

             %predicates that output stuff to stdout
             showTheory/1,
             showTheory/4,
             showTheorySummary/6
           ]
         ).

% GILPS modules
:- use_module('../examples/examples', [exampleIDsWeights/3, exampleIDsWeights/2, foldSeparate/4, exampleIDs/2]).
:- use_module('../utils/list', [createList/3]).
:- use_module('../utils/clause', [skolemize/2]).
:- use_module('../messages/messages', [message/2]).
:- use_module('../settings/settings', [setting/2]). % for output_theory_file

% YAP modules
:- use_module(library(lists), [append/3]).
:- use_module(library(ordsets), [ord_union/3, ord_intersection/3, ord_subtract/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% output_theory2file(+Theory)
%
% Given:
%  Theory: a term of the form: (TotLiterals, PosCovered, NegCovered, Hypotheses)
%          where Hypotheses is a list of terms of the form (Hypothesis, HypSig, NumLiterals, NPos, NNeg, NNewPos, NNewNeg),
%          where:
%           Hypothesis: is a unique hypothesis as a list of literals
%           HypSig: Hypothesis signature
%           NumLiterals: number of literals in hypothesis
%           WPos: weight of positive examples hypothesis covered in the training data
%           WNeg: weight of negative examples hypothesis covered in the training data
%           WNewPos: weight of new positive examples covered (i.e. subtracting the ones covered by the previous hypothesis)
%           WNewNeg: weight of new negative examples covered (i.e. subtracting the ones covered by the previous hypothesis)
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

output_theory2file((_,_,_,Hyps)):-
  setting(output_theory_file, Theory_FileName),
  open(Theory_FileName, write, Stream),
  output_hyps2stream(Hyps, Stream),
  close(Stream).

%output_hyps2stream(+Hyps, +Stream)
output_hyps2stream([], _).
output_hyps2stream([(Hyp,HypSig,_,_,_,_)|T], Stream):-
  % we should output the clause signature as well, otherwise we cannot do dynamic clause evaluation
  skolemize(Hyp, HypSkolem), % skolemize to output a prettier version of Hyp with short variables
  format(Stream, "theory_clause(~q,~w).~n", [HypSkolem, HypSig]),%we have to quote the string but not display the $VAR(0), this is what 'q' does
  output_hyps2stream(T, Stream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% numElementsInTheoryResult(-N)
%
% Given:
%   N: number of elements in a theory result list
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

numElementsInTheoryResult(4). %  [TruePositivesWeight, FalsePositivesWeight, TrueNegativesWeight, FalseNegativesWeight]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% numElementsInTheoryResultMetrics(-N)
%
% Given:
%   N: number of elements in a theory result metrics list
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

numElementsInTheoryResultMetrics(8). %  [DefaultAccuracy, ClassifierAccuracy, Recall, Specificity, Precision, CorPredNeg, F1Score, MatthewsCorrelation]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showTheory(+Theory) %use all examples
% showTheory(+Theory, +PositiveExampleIDs, +NegativeExampleIDs, +TestFold)
%
% Given:
%   Theory: a Theory term as described in the header
%   PositiveExampleIDs: a list of the positive example ids to consider (important for cross fold validation)
%   NegativeExampleIDs: a list of the negative example ids to consider
%   TestFold: the fold not used to train Theory
%
% Outputs to stdout
%   The hypotheses that constitute the theory
%   Its confusion matrix
%   Basic stats (accuracy, sensitivity, recall,...)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

showTheory(Theory):-
  exampleIDs(PosExampleIDs, NegExampleIDs),
  showTheory(Theory, PosExampleIDs, NegExampleIDs, -1).

showTheory((_TotLiterals, PosCovered, NegCovered, Hypotheses), PosExampleIDs, NegExampleIDs, TestFold):-
  message(show_theory_hypotheses, [Hypotheses, TestFold]),
  compute_theory_result(PosCovered, NegCovered, PosExampleIDs, NegExampleIDs,
                        TestFold, TheoryResultTrain, TheoryResultTest),
  theoryResult2Metrics(TheoryResultTrain, TheoryResultTrainMetrics),

  % get default standard deviations...
  numElementsInTheoryResult(TR_N), createList(TR_N, 0, TR_STDevList),
  numElementsInTheoryResultMetrics(TRM_N), createList(TRM_N, 0, TRM_STDevList),

  % do display
  showTheorySummary(TheoryResultTrain, TR_STDevList, TheoryResultTrainMetrics, TRM_STDevList,
                    display_train_theory_results, TestFold),

  (TestFold\=(-1)-> % the model was built with some fold left out, thus it makes sense to look at TheoryResultTest
    theoryResult2Metrics(TheoryResultTest, TheoryResultTestMetrics),
    showTheorySummary(TheoryResultTest, TR_STDevList, TheoryResultTestMetrics, TRM_STDevList,
                      display_test_theory_results, TestFold)
  ;
    true
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_theory_result(+TheoryPosCovered, +TheoryNegCovered, +AllPositives, +AllNegatives, +TestFold,
%                       -TheoryResultTrain, -TheoryResultTest)
%
% Given:
%    TheoryPosCovered: ordered list of positive example ids that the theory covers
%    TheoryNegCovered: ordered list of negative example ids that the theory covers
%    TestFold: the fold to which examples from AllPositives and AllNegatives belong
%    AllPositives: ordered list of all positive example ids to consider (i.e. if the theory covers examples outside this set they are not considered)
%    AllNegatives: ordered list of all negative example ids to consider (i.e. if the theory covers examples outside this set they are not considered)
%
% Returns:
%    TheoryResultTrain: the theory result for the training examples
%    TheoryResultTest:  the theory result for the test examples
%
% Notes:
%    With a perfect theory we would have TheoryPosCovered=AllPositives, TheoryNegCovered=[]
%    We are assuming each hypothesis in the theory has run through each element in AllPositives and AllNegatives (and possible more)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_theory_result(TheoryPosCovered, TheoryNegCovered, AllPositives, AllNegatives,
                      TestFold, TheoryResultTrain, TheoryResultTest):-
  foldSeparate(AllPositives, TestFold, TestPositives, TrainPositives),
  foldSeparate(AllNegatives, TestFold, TestNegatives, TrainNegatives),
  evaluate_theory(TheoryPosCovered, TheoryNegCovered, TrainPositives, TrainNegatives, TheoryResultTrain),
  evaluate_theory(TheoryPosCovered, TheoryNegCovered, TestPositives, TestNegatives, TheoryResultTest).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% evaluate_theory(+TheoryPosCovered, +TheoryNegCovered, +PositiveIDs, +NegativeIDs,
%                 -TheoryResult)
%
% Given:
%    TheoryPosCovered: ordered list of positive example ids that the theory covers
%    TheoryNegCovered: ordered list of negative example ids that the theory covers
%    PositiveIDs: ordered list of all positive example ids to consider (i.e. if the theory covers examples outside this set they are not considered)
%    NegativeIDs: ordered list of all negative example ids to consider (i.e. if the theory covers examples outside this set they are not considered)
%
% Returns:
%    TheoryResult: a term (TruePositivesWeight, FalsePositivesWeight, TrueNegativesWeight, FalseNegativesWeight)
%                  with the result of a theory evaluated in a given set of examples
%
% Notes:
%   This predicate doesn't take a TestFold as input and computes the theory results for the given Positive and Negative IDs
%   The result of a theory thus depends on the examples given and the examples can be either training or testing ones
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

evaluate_theory(TheoryPosCovered, TheoryNegCovered, AllPositives, AllNegatives,
                [TruePositivesWeight, FalsePositivesWeight, TrueNegativesWeight, FalseNegativesWeight]):-
  ord_intersection(AllPositives, TheoryPosCovered, TruePositivesIDs),
  ord_intersection(AllNegatives, TheoryNegCovered, FalsePositivesIDs),
  ord_union(TheoryPosCovered, TheoryNegCovered, TheoryCovered),
  ord_subtract(AllPositives, TheoryCovered, FalseNegativesIDs),
  ord_subtract(AllNegatives, TheoryCovered, TrueNegativesIDs),
  exampleIDsWeights(TruePositivesIDs, TruePositivesWeight),    % notice we are ignoring the fold id
  exampleIDsWeights(FalsePositivesIDs, FalsePositivesWeight),  % that's because we want to count all the examples
  exampleIDsWeights(TrueNegativesIDs, TrueNegativesWeight),
  exampleIDsWeights(FalseNegativesIDs, FalseNegativesWeight).

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
%   MessageType: type of message to output (cannot be show_theory_summary!!)
%   TestFold: the fold not used for training the theory
%
% Outputs the theory results on standard output
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

showTheorySummary(TheoryResult, TR_STDs, TheoryResultMetrics, TRM_STDs,
                  MessageType, TestFold):-
  message(show_theory_summary, [TheoryResult, TR_STDs, TheoryResultMetrics, TRM_STDs, MessageType, TestFold]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% theoryResult2Metrics(+TheoryResult, -TheoryResultMetrics)
%
% Given:
%   TheoryResult: a term of the form: (TruePositivesWeight, FalsePositivesWeight, TrueNegativesWeight, FalseNegativesWeight)
%
% Returns:
%   TheoryResultMetrics: a term of the form:
%    (DefaultAccuracy, ClassifierAccuracy, Recall, Specificity, Precision, CorPredNeg, F1Score, MatthewsCorrelation)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theoryResult2Metrics([TP, FP, TN, FN],
                     [DefaultAccuracy, ClassifierAccuracy, Recall, Specificity, Precision, CorPredNeg, F1Score, MatthewsCorrelation]):-

  % auxiliar variables
  TotalActualPositiveWeight is TP + FN,
  TotalActualNegativeWeight is abs(FP) + abs(TN),
  TotalExamplesWeight is TotalActualPositiveWeight + TotalActualNegativeWeight,% or TotalPredictedPositiveWeight + TotalPredictedNegativeWeight
  TotalPredictedPositiveWeight is TP + abs(FP),
  TotalPredictedNegativeWeight is abs(TN) + FN,

  do_div(max(TotalActualPositiveWeight, TotalActualNegativeWeight)*100, TotalExamplesWeight, DefaultAccuracy),
  do_div((TP+abs(TN))*100.0, TotalExamplesWeight, ClassifierAccuracy),
  do_div(TP*100, TotalActualPositiveWeight, Recall), % also know as sensitivity. I.e. % of correctly classified positive examples
  do_div(abs(TN)*100.0, TotalActualNegativeWeight, Specificity), % pct of correcly classified negative examples
  do_div(TP*100.0, TotalPredictedPositiveWeight, Precision), % pct of correctly predicted positive examples
  do_div(abs(TN)*100.0, TotalPredictedNegativeWeight, CorPredNeg), % pct of correctly predicted negative examples
  do_div(2*Precision*Recall, (Precision+Recall)*100.0, F1Score), % 2*Precision*Recall/(Precision+Recall), the /100 is because Precision and Recall were multiplied by 100 previously
  % multiply by 1.0 to convert to float. Using integer may cause overflow if GIMPS is not installed
  MC_Numerator is TP*1.0*abs(TN) - abs(FP)*1.0*FN,
  MC_SQR is max((TP*1.0+abs(FP))*(TP+FN)*(abs(TN)+abs(FP))*(abs(TN)+FN),0),
  do_div(MC_Numerator, sqrt(MC_SQR), MatthewsCorrelation).% a division by 0 yields 1.#INF, does not crash

  % the actual metrics
/*
  DefaultAccuracy is max(TotalActualPositiveWeight, TotalActualNegativeWeight)*100/TotalExamplesWeight,
  ClassifierAccuracy is (TP+abs(TN))*100.0/TotalExamplesWeight,
  Recall is TP*100/TotalActualPositiveWeight, % also know as sensitivity. I.e. % of correctly classified positive examples
  Specificity is abs(TN)*100.0/TotalActualNegativeWeight, % pct of correcly classified negative examples
  Precision is TP*100.0/TotalPredictedPositiveWeight, % pct of correctly predicted positive examples
  CorPredNeg is abs(TN)*100.0/TotalPredictedNegativeWeight, % pct of correctly predicted negative examples
  F1Score is 2*Precision*Recall/(Precision+Recall)/100.0, % 2*Precision*Recall/(Precision+Recall), the /100 is because Precision and Recall were multiplied by 100 previously
  % multiply by 1.0 to convert to float. Using integer may cause overflow if GIMPS is not installed
  MC_Numerator is TP*1.0*abs(TN) - abs(FP)*1.0*FN,
  MC_SQR is max((TP*1.0+abs(FP))*(TP+FN)*(abs(TN)+abs(FP))*(abs(TN)+FN),0),
  MatthewsCorrelation is MC_Numerator/sqrt(MC_SQR).% a division by 0 yields 1.#INF, does not crash
*/

%do_div(+Numerator, +Denominator, -Result)
do_div(Numerator, Denominator, Res):-
  (Denominator=:=0 ->
    Res=0
   ;
    Res is Numerator / Denominator
  ).
