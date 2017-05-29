%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-07-08
%
%
%   This file has predicates to compute score of an hypothesis.
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(score,
            [
              hypothesis_info/5,
              score/3,
              score/4,
              stop_score/1,
              verifies_partial_metrics/2,
              verifies_full_metrics/2
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [exampleIDsWeights/2, pos_prior/1]).

% YAP modules
:- use_module(library(ordsets), [ord_intersection/3, ord_subtract/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% hypothesis_info(+HypPosEIDs, +HypNegEIDs, +PosEIDs, +NegEIDs, -HypInfo)
%
% This predicate returns the confusion matrix metrics of an hypothesis which covers HypPosEIDs + HypNegEIDs examples
% when tested against examples PosEIDs, NegEIDs
%
% Given:
%   HypPosEIDs: a list of the positive example ids an hypothesis covers
%   HypNegEIDs: a list of the negative example ids an hypothesis covers (same hypothesis
%   PosEIDs: a list of the positive example ids we want to test for
%   NegEIDs: a list of the negative example ids we want to test for
%
% Returns:
%  HypInfo: a list with the result of evaluating hypothesis against PosEIDs and NegEIDs
%    TP: True Positive weight
%    FP: False Positive weight
%    FN: False Negative weight
%    TN: True Negative weight
%
% Notes:
%   HypPosEIDs/HypNegEIDs may have elements not in PosEIDs/NegEIDs.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

hypothesis_info(ACovPosEIDs, ACovNegEIDs, PosEIDs, NegEIDs, [TP, AFP, FN, ATN]):-
  ord_intersection(ACovPosEIDs, PosEIDs, Cov_PosIDs),
  ord_intersection(ACovNegEIDs, NegEIDs, Cov_NegIDs),
  ord_subtract(PosEIDs, Cov_PosIDs, NonCov_PosIDs),
  ord_subtract(NegEIDs, Cov_NegIDs, NonCov_NegIDs),
  exampleIDsWeights(Cov_PosIDs, TP),
  exampleIDsWeights(Cov_NegIDs, FP),
  exampleIDsWeights(NonCov_PosIDs, FN),
  exampleIDsWeights(NonCov_NegIDs, TN),
  AFP is abs(FP),
  ATN is abs(TN).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% score(+NumLiterals, +HypInfo, -Score)
%
% Given:
%  NumLiterals: number of literals in hypothesis (only matters for compression)
%  HypInfo: a list with the result of evaluating hypothesis against PosEIDs and NegEIDs
%    TP: true positives weights
%    FP: false positives weights (i.e. false predicated as true)
%    FN: false negatives weights (i.e. true predicated as false)
%    TN: true negatives weights
%
% Returns:
%   Score: the score for these metrics according to the ScoreFunction
%
% Notes:
%  All integers in HypInfo are given in absolute value, so are all non-negative numbers
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

score(NumLiterals, HypInfo, Score):-
  setting(evalfn, ScoreFunction),
  score(ScoreFunction, NumLiterals, HypInfo, Score).

%score(+Measure, +NumLiterals, +HypInfo, -Score)

score(compression_ratio, NumLiterals, [TP, FP, _FN, _TN], Score):-
  !, Score is (TP - FP)/NumLiterals.
score(compression, NumLiterals, [TP, FP, _FN, _TN], Score):-
  !, Score is TP - FP - NumLiterals.
score(coverage, _NumLiterals, HypInfo, Score):-
  !, score(compression, 0, HypInfo, Score).
score(accuracy, _NumLiterals, [TP, FP, FN, TN], Score):-
  !,
  N is TP + FP + FN + TN, % Total examples
  Score is (TP+TN)/N.
score(mestimate, _NumLiterals, [TP, FP, _TN, _FN], Score):-
  !,
  Cover is TP + FP,
  %Cover must be non negative!
  (Cover < 0 ->
      K = 0
    ;
      K is sqrt(Cover)
  ),
  pos_prior(PosPrior),
  Score is (TP + K*PosPrior)/(Cover+K).
score(sensitivity, _NumLiterals, [TP, _FP, FN, _TN], Score):- %also known as recall
  !,
  NPos is TP + FN, %Num Real Pos
  Score is TP/NPos.
score(recall, NumLiterals, HypInfo, Score):-
  !, score(sensitivity, NumLiterals, HypInfo, Score).
score(specificity, _NumLiterals, [_TP, FP, _FN, TN], Score):-
  !,
  NNeg is FP + TN, %Num Real Neg
  Score is TN/NNeg.
score(precision, _NumLiterals, [TP, FP, _FN, _TN], Score):- % percentage of correctly predicted positive examples
  !,
  PPos is TP + FP, %Num Predicted Pos
  Score is TP/PPos.
score(wprecision, NumLiterals, [TP, FP, FN, TN], Score):- % weighted precision
  !,
  score(precision, NumLiterals, [TP, FP, FN, TN], Precision),
  Score is TP*1.0*Precision/(TP+FN).
score(corpredneg, _NumLiterals, [_TP, _FP, FN, TN], Score):-
  !,
  PNeg is FN + TN, %Num Predicted Neg
  Score is TN/PNeg.
score(f1score, NumLiterals, HypInfo, Score):-
  !,
  score(precision, NumLiterals, HypInfo, Precision),
  score(recall, NumLiterals, HypInfo, Recall),
  Score is 2*Precision*Recall/(Precision+Recall).
score(correlation, _NumLiterals, [TP, FP, FN, TN], Score):- % Matthews Correlation
  !,
  MC_Numerator is TP*1.0*TN - FP*1.0*FN,
  MC_SQR is max((TP*1.0+FP)*(TP+FN)*(TN+FP)*(TN+FN),0),
  Score is MC_Numerator/sqrt(MC_SQR).% a division by 0 yields 1.#INF, does not crash
score(support, _NumLiterals, [TP, FP, FN, TN], Score):-
  !,
  Score is TP/(TP+FP+FN+TN).
score(novelty, _NumLiterals, [TP, FP, FN, TN], Score):-
  !,
  N is TP + FP + FN + TN, % Total examples
  NPos is TP + FN, %Num Real Pos
  PPos is TP + FP, %Num Predicted Pos
  Score is TP/N - (NPos*PPos)/(N*N).
score(wracc, NumLiterals, HypInfo, Score):-
  !, score(novelty, NumLiterals, HypInfo, Score).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% default(+Measure, +HypInfo, -Score)
%
% Given:
%   Measure: a score measure
%   HypInfo: a list with four integers
%     TP: true positives
%     FP: false positive (i.e. false predicated as true)   (negative value)
%     FN: false negative (i.e. true predicated as false)
%     TN: true negatives                                   (negative value)
%
% Returns:
%   Score: the default score for measure Measure
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

default(accuracy, [TP, FP, FN, TN], Default):-
  !,
  N is TP + FP + FN + TN, % Total examples
  Default is max(TP+FN, FP+TN)/N.
default(sensitivity, [TP, FP, FN, TN], Default):-
  !,
  NPos is TP + FN, %Num Real Pos
  NNeg is FP + TN, %Num Real Neg
  (NPos>=NNeg -> Default=1 ; Default=0).
default(specificity, [TP, FP, FN, TN], Default):-
  !,
  NPos is TP + FN, %Num Real Pos
  NNeg is FP + TN, %Num Real Neg
  (NPos>=NNeg -> Default=0 ; Default=1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% stop_score(-StopScore)
%
% Returns:
%   StopScore: the stop score for the current evaluation function
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

stop_score(StopScore):-
  setting(evalfn, ScoreFunction),
  stop_score(ScoreFunction, StopScore).

stop_score(wprecision, 0):-!.
stop_score(precision, 0):-!.
stop_score(f1score, 0):-!.
stop_score(compression, 0):-!.
stop_score(compression_ratio, 1.0):-!.
stop_score(coverage, 0):-!.
stop_score(accuracy, A):-
  !, pos_prior(P),
  A is max(P, 1-P).
stop_score(novelty, 0.01):-!.
stop_score(wracc, S):- 
  !, stop_score(novelty, S).
stop_score(_, 0):-!. % to catch other measures not specified

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% verifies_partial_metrics(+NumLiterals, +HypInfo)
% verifies_full_metrics(+NumLiterals, +HypInfo)
%
% Succeeds if HypInfo verifies the user defined metrics
%
% Notes:
%   The full does the partial evaluation plus the verification of coverage and minpos
%   The reason for the distinction is that in bottom up ILP systems the initial clauses
%   have very little coverage and only the final ones should be check for coverage
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

verifies_partial_metrics(NumLiterals, [TP, FP, FN, TN]):-
  setting(maxneg, MaxNeg),
  FP=<MaxNeg,
  setting(minprec, MinPrec1),
  pos_prior(PosPrior),
  MinPrec is max(max(1-PosPrior, PosPrior), MinPrec1),
  score(precision, NumLiterals, [TP, FP, FN, TN], Precision),
  Precision>=MinPrec,
  setting(noise, Noise),
  (1-Precision)=<Noise,
  setting(minacc, MinAcc),
  score(accuracy, NumLiterals, [TP, FP, FN, TN], Accuracy), 
  Accuracy>=MinAcc.

verifies_full_metrics(NumLiterals, [TP, FP, FN, TN]):-
  verifies_partial_metrics(NumLiterals, [TP, FP, FN, TN]),
  % do not check for maxneg and noise, as these are checked at hypothesis_coverage
  % besides, maxneg may be passed when doing smart negative based reduction
  %above min score
  score(NumLiterals, [TP, FP, FN, TN], CurScore),
  stop_score(StopScore),
  CurScore>StopScore,
  N is TP+FP+FN+TN,
  setting(mincov, MinCov),
  TP/N>=MinCov,
  setting(minpos, MinPos),
  TP>=MinPos. % check we cover at least the required positive weight
