%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-03-11
%
%
%   This file has predicates to compute coverage of a single hypothesis.
%
%   In case the hypothesis is recursive the following crucial assumption is made:
%
%     There is only one definition for the recursive case. The base case is already in the
%   background knowledge or is a positive example.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(coverage,
            [
              full_hypothesis_coverage/6,
              full_hypothesis_coverage/7,
              hypothesis_coverage/6
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [exampleIDsWeights/2]).
:- use_module('../clause evaluation/common_clause_evaluation', [clause_examples_coverage/6, can_use_heuristic_clause_evaluation/1, apply_clause_transformations/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% hypothesis_coverage(+Hypothesis, +HypothesisSignature, +PosExamplesID, +NegExamplesID, -PosExamplesIDCovered, -NegExamplesIDCovered)
%
% Given;
%   Hypothesis: an hypothesis as a list of literals (e.g. [class(X,mammal), has_milk(X)])
%   PosExamplesID: a list of ids of positive examples we want to test coverage
%   NegExamplesID: a list of ids of negative examples we want to test coverage
%
% Returns:
%   PosExamplesIDCovered: a list of ids of positive examples that are covered by the current clause
%   NegExamplesIDCovered: a list of ids of negative examples that are covered by the current clause
%
% Notes:
%   This predicate fails if the coverage exceeds the noise, minacc or maxneg settings. That is, if
%   AbsWeightNegExamplesIDCovered/(WeightPosExamplesIDCovered+AbsNegExamplesIDCovered)>= noise
%   or if the hypothesis doesn't cover the minimum weight of positives
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

hypothesis_coverage(_Hypothesis, _HypothesisSignature, _PosExamplesID, _NegExamplesID, PosExamplesIDCovered, NegExamplesIDCovered):-
  ground(PosExamplesIDCovered),
  ground(NegExamplesIDCovered),!. % after computing the negative reduction in Progolem we already know the coverage

hypothesis_coverage(Hypothesis, HypothesisSignature, PosExamplesID, NegExamplesID, PosExamplesIDCovered, NegExamplesIDCovered):-
  apply_clause_transformations(Hypothesis, HypothesisSignature, Hyp1),
  setting(maxneg, MaxNeg),
  setting(noise, Noise),
  (evaluate_negatives_first(MaxNeg, Noise, PosExamplesID, MaxNegWeight) ->
    %write(clause_examples_coverage(NegExamplesID, Hyp1, HypothesisSignature, MaxNegWeight, NegWeightsCovered, NegExamplesIDCovered)),nl,halt,
    clause_examples_coverage(NegExamplesID, Hyp1, HypothesisSignature, MaxNegWeight, NegWeightsCovered, NegExamplesIDCovered),
    clause_examples_coverage(PosExamplesID, Hyp1, HypothesisSignature, inf, PosWeightsCovered, PosExamplesIDCovered)
   ;
    clause_examples_coverage(PosExamplesID, Hyp1, HypothesisSignature, inf, PosWeightsCovered, PosExamplesIDCovered),
    MaxNegWeightNoise is Noise*PosWeightsCovered/(1-Noise), % max allowed absolute negative weight
    MaxNegWeight is min(MaxNeg, MaxNegWeightNoise),
    clause_examples_coverage(NegExamplesID, Hyp1, HypothesisSignature, MaxNegWeight, NegWeightsCovered, NegExamplesIDCovered)
  ),
  (PosWeightsCovered+NegWeightsCovered=:=0 ->
     format("Warning: clause covers no examples! This should never happen. There is a bug somewhere (PosCov:~w,NegCov:~w).~n", [PosWeightsCovered,NegWeightsCovered]),
     HypNoise = 1
   ;
     HypNoise is NegWeightsCovered/(PosWeightsCovered+NegWeightsCovered)
  ),
  HypNoise=<Noise.

/*
  clause_examples_coverage(PosExamplesID, Hyp1, HypothesisSignature, inf, NegWeightsCovered, NegExamplesIDCovered),
  MaxNegWeightNoise is Noise*PosWeightsCovered/(1-Noise), % max allowed absolute negative weight
  setting(maxneg, MaxNeg),
  MaxNegWeight is min(MaxNeg, MaxNegWeightNoise),
  clause_examples_coverage(NegExamplesID, Hyp1, HypothesisSignature, MaxNegWeight, _AbsNegWeightsCovered, NegExamplesIDCovered).
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% evaluate_negatives_first(+MaxNegs, +Noise, +PosExamplesID, -MaxNegWeight)
%
% Returns: (on success)
%  MaxNegWeight: maximum weight of the allowed negatives to cover
%
% This predicate decides if one should evaluate the negative examples before the positives.
% One should do so if we estimate that will lead to less tests
%
% Assume that evaluating a positive or a negative costs the same and that the probability
% for a clause to cover a positive or a negative is the same.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

evaluate_negatives_first(_, _, _, _):-
  setting(evaluate_negatives_first, false),!,
  fail.

evaluate_negatives_first(_, 0, _, 0):-!.
evaluate_negatives_first(MaxNegs, Noise, PosEIDs, MaxNegWeight):-
  exampleIDsWeights(PosEIDs, PosWeights),
  MaxNegWeight is min(MaxNegs, Noise*PosWeights).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% full_hypothesis_coverage(+Hypothesis, +HypSig, +PosExampleIDs, +NegExampleIDs, -PosExampleIDsCovered, -NegExampleIDsCovered)
% full_hypothesis_coverage(+Hypothesis, +HypSig, +PosExampleIDs, +NegExampleIDs, +MaxNegsToCover, -PosExampleIDsCovered, -NegExampleIDsCovered)
%
%  Identical to above but we compute full the negative coverage no matter what the prunning settings
%  (a variant is to compute the negative coverage just until a certain threshold)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

full_hypothesis_coverage(Hypothesis, HypSig, PosExamplesID, NegExamplesID, PosExamplesIDCovered, NegExamplesIDCovered):-
  full_hypothesis_coverage(Hypothesis, HypSig, PosExamplesID, NegExamplesID, inf, PosExamplesIDCovered, NegExamplesIDCovered).

full_hypothesis_coverage(Hypothesis, HypSig, PosExamplesID, NegExamplesID, MaxNegsToCover, PosExamplesIDCovered, NegExamplesIDCovered):-
  apply_clause_transformations(Hypothesis, HypSig, Hyp1),
  clause_examples_coverage(PosExamplesID, Hyp1, HypSig, inf, _PosWeightsCovered, PosExamplesIDCovered),
  clause_examples_coverage(NegExamplesID, Hyp1, HypSig, MaxNegsToCover, _AbsNegWeightsCovered, NegExamplesIDCovered).
