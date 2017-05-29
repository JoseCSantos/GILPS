%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-04-23
%
%   This file defines and has predicates to deal with type Theories.
%   Theories is a list of Theory terms (see theory.pl)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(theories,
           [
             createTheories/2,
             showTheories/3
           ]
         ).

% GILPS modules
:- use_module('theory', [showTheory/4, numElementsInTheoryResult/1, numElementsInTheoryResultMetrics/1,
                         showTheorySummary/6, theoryResult2Metrics/2, compute_theory_result/7]).
:- use_module('theory_constructor', [construct_global_theory/3]).
:- use_module('../settings/settings', [setting/2]). % for verbose, cross_validation_folds
:- use_module('../utils/list', [numbersList/3]).
:- use_module('../utils/math', [initStats/1, updateStats/3, valueStats/3]). % to compute running statistics
:- use_module('../messages/messages', [message/2]).

% YAP modules
:- use_module(library(lists), [member/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% createTheories(+HypothesesCoverage, -Theories)
%
% Given:
%  HypothesesCoverage: a list of tuples of the form: (Hypothesis, HypSig, ListExGen, ListExPos, ListExNeg) where:
%
%                       Hypothesis: an hypothesis (clause form)
%                       HypSig: hypothesis signature
%                       NumLiterals: number of literals in Hypothesis
%                       ListExGen: list of examples that generated Hypothesis
%                       ListExPos: list of positive examples Hypothesis covers
%                       ListExNeg: list of negative examples Hypothesis covers
%
% Returns:
%   Theories: a list with number of cross validation folds theories + 1
%             Theory at position I is the result of learning with all folds except I
%             Type Theory is described in theory.pl
%
% Notes:
%   In position 0 of Theories is the Theory built with all examples as training. At position I>0, is the
%   theory built with all examples except the ones belonging to fold I.
%
%   Thus, the number of Theories is:
%             1 if cross_validation_folds is 1 (i.e. no cross validation)
%             cross_validation_folds + 1 if cross_validation_folds>1
%
%   The reason numbersList/3, works nicely here is a little tricky:
%
%      When cross_validation_folds is 1 all examples belong to fold 0, and thus ignoring fold 1 is no problem.
%      When cross_validation_folds is > 1, no example belongs to fold 0, and thus ignoring fold 0 yields the
%       theory using all data as training
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

createTheories(HypothesesCoverage, Theories):-
  setting(cross_validation_folds, NumFolds),
  (NumFolds=1->StartNum=1;StartNum=0),
  numbersList(StartNum, NumFolds, Folds),
  % this findall performs the cross-validation
  findall(Theory,
          (member(Fold, Folds),
           construct_global_theory(HypothesesCoverage, Fold, Theory),
           message(theory_constructed, [Fold, NumFolds])
          ),
          Theories).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showTheories(+Theories, +PositiveExampleIDs, +NegativeExampleIDs)
%
% Given:
%   Theories: a list of theory terms.
%             The first element (index 0) of this list is always a theory built with all the examples as training
%             The remaining theories (index>=1), have been constructed with all folds, except fold 'index'
%
%   PositiveExampleIDs: a list of all the positive example ids used (excluding only the out of the sample)
%   NegativeExampleIDs: a list of all the negative example ids used (excluding only the out of the sample)
%
% Outputs to stdout, for each hypotheses, depending on the verbose level
%   The hypotheses that constitute the theory
%   Its confusion matrix
%   Basic stats (accuracy, sensitivity, recall,...)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

showTheories([AllDataTheory|FoldsTheories], PosExampleIDs, NegExampleIDs):-
  showTheory(AllDataTheory, PosExampleIDs, NegExampleIDs, -1),% Fold -1 ensures that all examples are considered
  numElementsInTheoryResult(NTR),
  numElementsInTheoryResultMetrics(NTRM),
  initListStats(NTR, FTRTrainStats), initListStats(NTR, FTRTestStats),
  initListStats(NTRM, FTRTrainMStats), initListStats(NTRM, FTRTestMStats),
  showFoldsTheories(FoldsTheories, 1, (FTRTrainStats, FTRTrainMStats, FTRTestStats, FTRTestMStats), PosExampleIDs, NegExampleIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% showFoldsTheories(+FoldTheories, +CurrentFoldNumber, +(FoldsTheoryResultTrainStats, FoldsTheoryResultTrainMetrics,
%                   FoldsTheoryResultTestStats, FoldsTheoryResultTestMetrics), +PositiveExampleIDs, +NegativeExampleIDs)
%
% Given:
%   FoldTheories: A list of theories, one per fold
%   CurrentFoldNumber: 
%   FoldsTheoryResultStats:
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%showAverageFoldsTheorySummary(+MessageType, +FoldsTheoryResultStats, +FoldsTheoryResultMetrics)
showAverageFoldsTheorySummary(MessageType, FoldsTheoryResultStats, FoldsTheoryResultMetrics):-
  valueListStats(FoldsTheoryResultStats, Avg_TheoryResult, StdDev_TheoryResult),
  valueListStats(FoldsTheoryResultMetrics, Avg_TheoryResultMetrics, StdDev_TheoryResultMetrics),
  showTheorySummary(Avg_TheoryResult, StdDev_TheoryResult,
                    Avg_TheoryResultMetrics, StdDev_TheoryResultMetrics,
                    MessageType, -1).

showFoldsTheories([], 1, _, _, _):-!. % no cross validation, don't show any averages
showFoldsTheories([], _, (FTRTrainStats, FTRTrainMetricsStats, FTRTestStats, FTRTestMetricsStats), _, _):-
  showAverageFoldsTheorySummary(display_avg_train_theory_results, FTRTrainStats, FTRTrainMetricsStats),
  showAverageFoldsTheorySummary(display_avg_test_theory_results, FTRTestStats, FTRTestMetricsStats).

showFoldsTheories([FT|FTs], TestFold, (FTRTrainStats, FTRTrainMStats, FTRTestStats, FTRTestMStats), PExIDs, NExIDs):-
  FT=(_NumLits, TPosCov, TNegCov, _Hypotheses),
  showTheory(FT, PExIDs, NExIDs, TestFold),
  compute_theory_result(TPosCov, TNegCov, PExIDs, NExIDs, TestFold, TResultTrain, TResultTest),
  %process theory result train
  updateListStats(TResultTrain, FTRTrainStats, FTRTrainStats1),
  theoryResult2Metrics(TResultTrain, TResultTrainMetrics),
  updateListStats(TResultTrainMetrics, FTRTrainMStats, FTRTrainMStats1),
  % process theory result test
  updateListStats(TResultTest, FTRTestStats, FTRTestStats1),
  theoryResult2Metrics(TResultTest, TResultTestMetrics),
  updateListStats(TResultTestMetrics, FTRTestMStats, FTRTestMStats1),  
  %proceed...
  TestFold1 is TestFold+1,
  showFoldsTheories(FTs, TestFold1, (FTRTrainStats1, FTRTrainMStats1, FTRTestStats1, FTRTestMStats1), PExIDs, NExIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Below are 3 auxiliary predicates to deal with maintaining a list of running statistics.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% initListStats(+N, -StatsList)

initListStats(0, []):-!.
initListStats(N, [S|T]):-
  initStats(S),
  N1 is N-1,
  initListStats(N1, T).

% updateListStats(+ResultLists, +CurStatsList, -NextStatsList)

updateListStats([], [], []).
updateListStats([R|RL], [S|SL], [NS|NSL]):-
  updateStats(R, S, NS),
  updateListStats(RL, SL, NSL).

% valueListStats(+CurStatsList, -MeansList, -StdDevsList)

valueListStats([], [], []).
valueListStats([S|SL], [Mean|Ms], [StdDev|Ss]):-
  valueStats(S, Mean, StdDev),
  valueListStats(SL, Ms, Ss).
