%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-02-04
%
%   This file processes the examples. The example processing consists in assigning them
% IDs, folds and has predicates to generate a set of hypotheses with their respective
% coverage, given a set of examples (positives and negatives)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(examples,
           [
             processExamples/2,
             exampleIDs/2,
             exampleIDs/5,
             exampleIDsInInterval/4,
             load_examples_term/1,
             save_examples_term/1,
             example/5,
             exampleIDsWeights/2,
             exampleIDsWeights/3,
             belongsToOtherFolds/2,
             foldSeparate/4,
             id2example/2,
             ids2Examples/2, %rename this later to ids2examples
             randomExampleIDs/2,
             positiveExamplesUnifying/4,
             erase_examples/1,
             pos_prior/1,
             read_examples_from_file/3
           ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]).
:- use_module('../messages/messages', [message/2]).
:- use_module('../utils/list', [randomPermutation/2]).
:- use_module('../utils/goal_solutions', [collect_solutions/4]).
:- use_module('../clause evaluation/theta_subsumption', [load_example/3]). % only needed if setting(clause_evaluation, theta_subsumption)

% YAP modules
:- use_module(library(lists), [member/2]).
:- use_module(library(random), [random/3]).

:- dynamic example/5.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% example(+ExampleId, +Example, +Weight, +Fold, +RandomNum)
%
% ExampleId:  a positive integer uniquely identifying the example (1 based)
% Example:    the example itself, a ground fact
% Weight:     the example weight, a finite real number number.
%             >0 positive example, <0 negative, =0 to be ignored
% Fold:       a positive integer, the fold number (for cross-fold validation)
% Float:      a random number in [0..1[. If sampling is on determine if an example is
%            used or not sampled or not
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic pos_prior/1.
% pos_prior(-PosPrior): returns the apriori probability that an example is positive
% (neg_prior is 1-pos_prior)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% fold(-Fold):
%
% Returns:
%  Fold: unified with a fold at random between 1 and number of cross validation folds
%
% Notes:
%  If 'cross_validation_folds' is 1 then Fold is always 0.
%  Either all examples belong to fold 0 (i.e. no CV), or belong uniformly to folds from
%  1 to cross_validation_folds
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fold(0):-
  setting(cross_validation_folds, 1),!.
fold(Fold):-
  setting(cross_validation_folds, NumFolds),
  NumFolds1 is NumFolds+1,
  random(1, NumFolds1, Fold). % Fold is an integer between 1..NumFolds

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% userExample(-Example, -Weight, -Fold)
%
%  Retrieves user defined examples
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

userExample(Example, Weight, Fold):-
  current_predicate(example, user:example(_,_)), !, % check if example/2 is defined in user module
  user:example(Example, Weight),
  fold(Fold). % the example has no fold, assign one randomly
userExample(Example, Weight, Fold):-
  current_predicate(example, user:example(_,_,_)), !, % check if example/3 is defined in user module
  user:example(Example, Weight, ExFold), % the example already has a user defined fold, check if valid
  (valid(ExFold)->Fold=ExFold; fold(Fold)). % if valid accept, otherwise assign one randomly

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% valid(+Fold): succeeds if Fold is a valid Fold number
%
% A Fold is valid if it's between 1 and cross_validation_folds (if cross_validation_folds>1)
% If cross_validation_folds=1, Fold must be 0
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

valid(0):-
  setting(cross_validation_folds, 1),!.
valid(Fold):-
  Fold>0,
  setting(cross_validation_folds, MaxFolds),
  MaxFolds>1,
  Fold=<MaxFolds.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% eraseUserExamples/0:
%
%  Retracts the user provided examples to save space as we have duplicated this information
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eraseUserExamples:-
  abolish(user:example/2), % abolish instead of retract because these are static predicates
  abolish(user:example/3).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% eraseProcessedExamples/0:
%
%  Retracts the processed examples
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eraseProcessedExamples:-
  retractall(pos_prior(_)),
  retractall(example(_, _, _, _, _)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processExamples(-PosEIDsProcessed, -NegEIDsProcessed)
%    identifies and inflates the examples read normally with consult
%
% Returns:
%   PosEIDsProcessed: list of positive examples ids processed
%   NegEIDsProcessed: list of negative examples ids processed
%
% Side effects:
%
%  After processExamples/0 succeeds the following is defined:
%
%    examples:example/5:  as explained above. It has all the example information
%    tPosExs: a global variable which holds the total number of positive
%      examples in use (accessed via nb_getval(tPosExs, NP)
%    tNegExs: a global variable which holds the total number of negative
%      examples in use (accessed via nb_getval(tNegExs, NN)
%    numAllExamples: a global variable which holds the total number of examples
%      (no matter if positive, negative, neutral, or if in use or not in use)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processExamples(_, _):-
  initializeVariable(numAllExamples),
  initializeVariable(tPosExs),
  initializeVariable(tNegExs),
  nb_getval(numAllExamples, NumExamples),
  NumExamples1 is NumExamples+1,
  nb_setval(start_example_id, NumExamples1),
  userExample(Example, Weight, Fold), % choice point to backtrack all examples
  inflate_example(Weight, NWeight),
  assertExample(Example, NWeight, Fold),
  fail.
processExamples(PosEIDs, NegEIDs):-
  nb_getval(numAllExamples, NumExamples), % examples numbered from 1..NumExamples
  nb_getval(tPosExs, NumPosExamples),
  nb_getval(tNegExs, NumNegExamples),
  retractall(pos_prior(_)),
  nb_getval(start_example_id, StartIntervalEID),
  nb_delete(start_example_id),
  exampleIDsInInterval(StartIntervalEID, inf, PosEIDs, NegEIDs),
  (NumExamples=0 -> PosPrior=0 ; PosPrior is NumPosExamples/NumExamples),
  asserta(pos_prior(PosPrior)),
  message(examples_loaded, [NumExamples, NumPosExamples, NumNegExamples]),
  eraseUserExamples.

%inflate_example(+Weight, -NWeight)
inflate_example(Weight, NWeight):-
  setting(example_inflation, EI),
  setting(positive_example_inflation, PEI),
  setting(negative_example_inflation, NEI),
  NWeight1 is Weight*EI,
  (NWeight1 < 0 ->
      NWeight is NWeight1*NEI
    ;
      NWeight is NWeight1*PEI
  ).

%initializeVariable(+VarName)
initializeVariable(VarName):-
  nb_current(VarName, _),!. % variable already exists, use it's current value
initializeVariable(VarName):-
  nb_setval(VarName, 0),!. % initialize to zero

%incrementVariable(+VarName, -UpdatedValue)
incrementVariable(VarName, VarValue1):-
  nb_getval(VarName, VarValue),
  VarValue1 is VarValue+1,
  nb_setval(VarName, VarValue1).

%decrementVariable(+VarName, -UpdatedValue)
decrementVariable(VarName, VarValue1):-
  nb_getval(VarName, VarValue),
  VarValue1 is VarValue-1,
  nb_setval(VarName, VarValue1).

assertExample(Example, Weight, Fold):-
  RandomFloat is random,
  incrementVariable(numAllExamples, ExampleID),
  (Weight>0 -> incrementVariable(tPosExs, _) ; incrementVariable(tNegExs, _)),
  assertExampleAux(ExampleID, Example, Weight, Fold, RandomFloat).

assertExampleAux(ExampleID, Example, Weight, Fold, RandomFloat):-
  assertz(example(ExampleID, Example, Weight, Fold, RandomFloat)), % assertz to keep the examples order
  load_example(Example, Weight, ExampleID). 
% Note: JCAS: 9th September 2010. I've decided to always store the bottom clause even if the clause evaluation
% engine is not theta_subsumption. This is not strictly needed but otherwise we would have to ensure the clause_evaluation
% was set before read_problem/2. The proper way to do this is in the settings module. Whenever the clause_evaluation setting
% is set to theta_subsumption we would load the ground bottom clauses of the examples, when it is set otherwise we would unload them.

%   (setting(clause_evaluation, theta_subsumption) ->
%      load_example(Example, Weight, ExampleID)
%     ;
%      true
%   ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% exampleIDs(-PosExampleIDsInUse, -NegExampleIDsInUse)
%
% Returns:
%
%   PosExampleIDsInUse: a list of positive example ids that are in use (that is, passed sampling)
%   NegExampleIDsInUse: a list of negative example ids that are in use (that is, passed sampling)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

exampleIDs(PosExampleIDsInUse, NegExampleIDsInUse):-
  setting(sample, Sample),
  findall(PosID, (example(PosID, _Ex, Weight, _Fold, Rand), Rand=<Sample, Weight>0), PosExampleIDsInUse),
  findall(NegID, (example(NegID, _Ex, Weight, _Fold, Rand), Rand=<Sample, Weight<0), NegExampleIDsInUse).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% exampleIDs(+Fold, -PosExampleIDsFold, -NegExampleIDsFold, -PosExampleIDsNonFold, -NegExampleIDsNonFold)
%
% Returns:
%   PosExampleIDsFold: a list of positive example ids that have passed sampling and belong to fold Fold
%   NegExampleIDsFold: a list of negative example ids that have passed sampling and belong to fold Fold
%   PosExampleIDsNonFold: a list of positive example ids that have passed sampling and do not belong to fold Fold
%   NegExampleIDsNonFold: a list of negative example ids that have passed sampling and do not belong to fold Fold
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

exampleIDs(Fold, PosExampleIDsFold, NegExampleIDsFold, PosExampleIDsNonFold, NegExampleIDsNonFold):-
  setting(sample, Sample),
  findall(PosID, (example(PosID, _Ex, Weight, Fold, Rand), Rand=<Sample, Weight>0), PosExampleIDsFold),
  findall(NegID, (example(NegID, _Ex, Weight, Fold, Rand), Rand=<Sample, Weight<0), NegExampleIDsFold),
  findall(PosID,
          (example(PosID, _Ex, Weight, Fold1, Rand),
           Fold1\=Fold,
           Rand=<Sample,
           Weight>0
          ),
          PosExampleIDsNonFold),
  findall(NegID,
          (example(NegID, _Ex, Weight, Fold1, Rand),
           Fold1\=Fold,
           Rand=<Sample,
           Weight<0
          ),
          NegExampleIDsNonFold).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% exampleIDsInInterval(+MinEID, +MaxEID, -PosExampleIDs, -NegExampleIDs)
%
% Returns:
%   MinEID: minimum example id to consider
%   MaxEID: maximum example id to consider
%   PosExampleIDs: a list of positive example ids that have passed sampling
%   NegExampleIDs: a list of negative example ids that have passed sampling
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
          
exampleIDsInInterval(MinEID, MaxEID, PosExampleIDs, NegExampleIDs):-
  MinEID=<MaxEID,
  setting(sample, Sample),
  findall(PosID, (example(PosID, _Ex, Weight, _Fold, Rand), 
                  PosID>=MinEID,PosID=<MaxEID,
                  Rand=<Sample, Weight>0),
                 PosExampleIDs),
  findall(NegID, (example(NegID, _Ex, Weight, _Fold, Rand),
                  NegID>=MinEID,NegID=<MaxEID,
                  Rand=<Sample, 
                  Weight<0),
                 NegExampleIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% save_examples_term(-Examples)
%
% Given:
%
%  Examples: ordered list of all examples (each example is the full example term)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

save_examples_term(Examples):-
  findall(example(ID, Ex, Weight, Fold, Rand), example(ID, Ex, Weight, Fold, Rand), Examples).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% load_examples_term(+Examples)
%
% Given:
%
%  Examples: ordered list of all examples (each example is the full example term)
%
% Succeeds by retracting existing examples and asserting the new ones
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_examples_term(Examples):-
  eraseProcessedExamples,
  forall(member(Example, Examples), assertz(Example)). % assertz to keep the lower ids before the higher ids

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% exampleIDsWeights(+ExampleIDs, -SumWeights)
%
% Given:
%   ExampleIDs: a list of example ids
%
% Returns:
%   The sum of weights of the example ids
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

exampleIDsWeights(ExampleIDs, SumWeights):-
  exampleIDsWeights(ExampleIDs, -1, SumWeights). %-1 is the fold to ignore, no example ever belongs
                                                 % to a negative fold, so this will count all examples

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% exampleIDsWeights(+ExampleIDs, +TestFold, -SumWeights)
%
% Given:
%   ExampleIDs: a list of example ids
%   TestFold: the weight of the examples belonging to this fold is ignored
%
% Returns:
%  The sum of weights of the example ids that do not belong to test fold
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

exampleIDsWeights([], _IgnoreFold, Sum, Sum):-!.
exampleIDsWeights([ExampleID|ExampleIDs], IgnoreFold, CurSum, FinalSum):-
  example(ExampleID, _Ex, Weight, Fold, _Rand),
  (Fold=IgnoreFold-> CurSum1=CurSum ; CurSum1 is CurSum+Weight),
  exampleIDsWeights(ExampleIDs, IgnoreFold, CurSum1, FinalSum).

exampleIDsWeights(ExampleIDs, TestFold, SumWeights):-
  exampleIDsWeights(ExampleIDs, TestFold, 0, SumWeights).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% belongsToOtherFolds(+ExampleIDs, +Fold)
%
% Given:
%  ExampleIDs: a list of example ids
%  Fold: a fold number
%
% Succeeds if at least one of the examples in ExampleIDs belongs to a fold different than Fold
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

belongsToOtherFolds([], _):-!,fail. % all elements have been looked upon, and all belong to Fold
belongsToOtherFolds([ExampleID|ExampleIDs], Fold):-
  example(ExampleID, _Ex, _Weight, Fold, _Rand), % ExampleID belongs to fold Fold
  belongsToOtherFolds(ExampleIDs, Fold).
belongsToOtherFolds([_|_], _):-!. % the head example does not belong to fold

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% foldSeparate(+ExampleIDs, +Fold, -ExampleIDsBelongingToFold, -ExampleIDsNotBelongingToFold)
%
% Given:
%  ExampleIDs: a list of example ids
%  Fold: a fold number
%
% Returns:
%  ExampleIDsBelongingToFold: subset of the example ids in ExampleIDs that belong to fold Fold
%  ExampleIDsNotBelongingToFold: subset of the example ids in ExampleIDs that do not belong to fold Fold
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

foldSeparate([], _, [], []).
foldSeparate([ExampleID|ExampleIDs], Fold, [ExampleID|BelongExampleIDs], NotBelongExampleIDs):-
  example(ExampleID, _Ex, _Weight, Fold, _Rand),!,
  foldSeparate(ExampleIDs, Fold, BelongExampleIDs, NotBelongExampleIDs).
foldSeparate([ExampleID|ExampleIDs], Fold, BelongExampleIDs, [ExampleID|NotBelongExampleIDs]):-
  foldSeparate(ExampleIDs, Fold, BelongExampleIDs, NotBelongExampleIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% ids2Examples(+ExampleIDs, -Examples)
%
% Given:
%  ExampleIDs: list of example ids
%
% Returns:
%  Examples: list of the actual examples corresponding to the ExampleIDs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ids2Examples([], []).
ids2Examples([EID|EIDs], [Example|Examples]):-
  example(EID, Example, _Weight, _Fold, _Rand),
  ids2Examples(EIDs, Examples).

% id2example(+ExampleID, -Example)
id2example(ExampleID, Example):-
  example(ExampleID, Example, _Weight, _Fold, _Rand).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% randomExampleIDs(+RandPosExampleIDs, -RandNegExampleIDs)
%
% Returns:
%   RandPosExampleIDs: positive example ids in use in a random order
%   RandNegExampleIDs: negative example ids in use in a random order
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

randomExampleIDs(RandPosExampleIDs, RandNegExampleIDs):-
  exampleIDs(PosExampleIDsInUse, NegExampleIDsInUse),
  randomPermutation(PosExampleIDsInUse, RandPosExampleIDs),
  randomPermutation(NegExampleIDsInUse, RandNegExampleIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% positiveExamplesUnifying(+Unifier, +NonUnifier, +MaxExamples, -Examples)
%
% Given:
%   Unifier: an example with some variables instantiated (e.g. qsort(A,A))
%   NonUnifier: an example (possibly all ground) that we cannot unify (e.g. qsort([1], [1]))
%   MaxExamples: max number of examples to return
%
% Returns:
%   Examples: up to MaxExamples positive examples that match Unifier
%             (e.g. [qsort([0], [0]), qsort([1], [1]), ...]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

positiveExamplesUnifying(Unifier, NonUnifier, MaxExamples, Examples):-
  setting(sample, Sample),
  collect_solutions(Unifier,
          (example(_, Unifier, Weight, _Fold, Rand),
           Unifier\=NonUnifier, Rand=<Sample, Weight>0),
          MaxExamples,
          Examples).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% erase_examples(+ExampleIDs)
%
% Given:
%   ExampleIDs: list of example IDs (e.g. [1,4,6])
%
% Always succeeds and as side effect removes all examples in ExampleIDs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

erase_examples([]).
erase_examples([EID|EIDs]):-
  retract(example(EID, _, Weight, _, _)),!,
  decrementVariable(numAllExamples, _),
  (Weight>0 -> decrementVariable(tPosExs, _) ; decrementVariable(tNegExs, _)),
  erase_examples(EIDs).

erase_examples([_EID|EIDs]):-
  % EID does not exist
  erase_examples(EIDs).
