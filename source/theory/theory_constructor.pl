%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-05-09
%
%   This file defines predicates to build the two types of theories: global or incremental
%
%   Global theories are constructed having the information of all hypotheses from all examples
%   and greedily choosing the best hypotheses.
%
%   Incremental theories are constructed incrementally. For each example, its hypotheses are
%   generated and the best one is added to the theory. All (positive) examples covered by that
%   hypothesis are removed and the process continues with the remaining uncovered positives.
%
%   Important note: when an hypothesis is being evaluated, it is currently evaluated against
%   ALL the examples, even in cross fold validation. Naturally, when building the theory
%   we ignore its coverage on the test fold.
%
%   So far all theories are constructed in a greedy way
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(theory_constructor,
           [
             clauses_to_theory/4,
             construct_global_theory/3,
             construct_incremental_theory/7,
             highestScoringHypothesis/4
           ]
         ).

% GILPS modules
:- use_module('../hypotheses/coverage', [full_hypothesis_coverage/6]).
:- use_module('../hypotheses/score', [score/3, stop_score/1, hypothesis_info/5]).
:- use_module('../examples/examples', [belongsToOtherFolds/2, exampleIDsWeights/3, exampleIDs/2, exampleIDs/5, exampleIDsWeights/2]).
:- use_module('../messages/messages', [message/2]).
:- use_module('../settings/settings', [setting/2, set/2]).

% YAP modules
:- use_module(library(apply_macros), [convlist/3, maplist/3]).
:- use_module(library(lists), [append/3, reverse/2]).
:- use_module(library(ordsets), [ord_subtract/3, ord_union/3]).

%clauses_to_theory(+Clauses, +ClauseNum, +PosExampleIDs, +NegExampleIDs, +CurTheory, -FinalTheory)
clauses_to_theory([], _, _, _, T, T).
clauses_to_theory([(Clause, ClauseSig)|Clauses], N, PosEIDs, NegEIDs, CurTheory, FTheory):-
  full_hypothesis_coverage(Clause, ClauseSig, PosEIDs, NegEIDs, PosCov, NegCov),
  length(Clause, NumLiterals),
  addHypothesisToTheory(CurTheory, -1, (_, (Clause, ClauseSig, NumLiterals, PosCov, NegCov)), NCurTheory),
  N1 is N+1,
  clauses_to_theory(Clauses, N1, PosEIDs, NegEIDs, NCurTheory, FTheory).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% clauses_to_theory(+Clauses, +PosExampleIDs, +NegExampleIDs, -Theory)
%
% Given:
%  Clauses: list of terms: (Clause, ClauseSignature)
%  PosExampleIDs: list of positive example ids to evaluate theory on
%  NegExampleIDs: list of negative example ids to evaluate clauses on
%
% Returns:
%  Theory: a theory term (see theory.pl) from theory_clauses that are loaded 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clauses_to_theory(Clauses, PosExampleIDs, NegExampleIDs, Theory):-
  emptyTheory(InitialTheory),
  clauses_to_theory(Clauses, 1, PosExampleIDs, NegExampleIDs, InitialTheory, Theory).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% construct_global_theory(+HypothesesCoverage, +TestFold, -Theory)
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
%  TestFold: fold to ignore when constructing the theory (<0 means don't ignore any)
%
%  Returns:
%    Theory: type Theory is described in theory.pl
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_global_theory(HypothesesCoverage, TestFold, Theory):-
  setting(max_clauses_per_theory, MaxClauses),
  convlist(processHypothesis(TestFold), HypothesesCoverage, AllHypotheses),
  greedy_search(AllHypotheses, MaxClauses, TestFold, Theory).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processHypothesis(+FoldToIgnore,
%                   +(Hypothesis, HypSig, NumLiterals, ListExGen, CoveredPosIDs, CoveredNegIDs)),
%                   -(Hypothesis, HypSig, NumLiterals, CoveredPosIDs, CoveredNegIDs))
%
%  Given:
%    FoldToIgnore: the fold to ignore. If an hypothesis was generated exclusively with examples from this fold
%                  it will be ignored
%    HypInfo: tuple of the form: (Hypothesis, NumLiterals, PosIDsGenerating, CoveredPosIDs, CoveredNegIDs)
%
%  Returns:
%    HypInfo tuple slightly processed (without the List Generated examples and with number of literals)
%    The pair is only output when at least one of the examples in ListExGen does _not_ belong to FoldToIgnore
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processHypothesis(FoldToIgnore,
                  (Hypothesis, HypSig, NumLiterals, ListExGen, CoveredPosIDs, CoveredNegIDs),
                  (Hypothesis, HypSig, NumLiterals, CoveredPosIDs, CoveredNegIDs)):-
  belongsToOtherFolds(ListExGen, FoldToIgnore).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% construct_incremental_theory(+TrainPosEIDs, +TrainNegEIDs, +APosEIDs, +ANegEIDs, +HypGenPred, +TestFold, -Theory)
%
% Given:
%  TrainPosEIDs: ordered list of positive example ids to use for training
%  TrainNegEIDs: ordered list of negative example ids to use for training
%  APosEIDs: ordered list of all positive example ids (to ignore!!!)
%  ANegEIDs: ordered list of all negative example ids (to ignore!!!)
%  HypGenPred: predicate to generate hypotheses from an example. It has 3 arguments:
%               +Example, +MaxHypsPerExample, -Hypotheses  (in clause form)
%
%  TestFold: fold to ignore when constructing the theory (<0 means don't ignore any)
%
%  Returns:
%    Theory: type Theory is described in theory.pl
%
%  Notes:
%   With an incremental theory construction there is no efficient way to perform cross validation
%   There is no fundamental need to provide APosEIDs and ANegEIDs. The reason they are provided is because
%   the test theory displayer assumes a theory has the list of all the examples it entails. This was done
%   when we had only global algorithms where it was efficient to add all coverage immediately.
%   Consider changing this later and use only TrainPosEIDs, TrainNegEIDs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate construct_incremental_theory(?, ?, ?, ?, :, ?, ?). %the fourth argument, HypGenPred, is to be executed in its own module

construct_incremental_theory(TPosEIDs, TNegEIDs, _APosEIDs, _ANegEIDs, HypGenPred, TestFold, Theory):-
  setting(max_clauses_per_theory, MaxClauses),
  emptyTheory(InitialTheory),
  %we should randomize the order of the PosExampleIDs ...
  construct_incremental_theory(TPosEIDs, TNegEIDs, TPosEIDs, 0, HypGenPred, 0, MaxClauses,
                               TestFold, InitialTheory, Theory).

:- meta_predicate construct_incremental_theory(?, ?, ?, ?, :, ?, ?, ?, ?, ?).

%construct_incremental_theory(+TrainPosEIDs, +TrainNegEIDs, +AllRemainTrainPosEIDs, +NumUncompressiveExamples
%                             +HypGenPred, +NumClauses, +MaxClauses, +TestFold, +CurrentTheory, -Theory)
construct_incremental_theory(_, _, _, _, _, MaxClauses, MaxClauses, _, Theory, Theory):-!.
construct_incremental_theory([], _, _, _, _, _, _, _, Theory, Theory):-!.
construct_incremental_theory(TPosEIDs, TNegEIDs, APosEIDs, NUE, HypGenPred, NumClauses, MaxClauses,
                             TestFold, CurrentTheory, Theory):-
  call_with_args(HypGenPred, TPosEIDs, TNegEIDs, APosEIDs, TestFold, BestHypothesis1),!,
  updateBestHypothesis(BestHypothesis1, BestHypothesis),%Signature must get here!!
  addHypothesisToTheory(CurrentTheory, TestFold, BestHypothesis, NCurrentTheory),
  BestHypothesis=(_Score, Hypothesis, _HypSig, _NumLiterals, PosEIDsCovered, NegEIDsCovered),
  ord_subtract(TPosEIDs, PosEIDsCovered, NTPosEIDs), % this will have to be changed to minus/3 if/when PosEIDs is not ordered
  ord_subtract(APosEIDs, PosEIDsCovered, NAPosEIDs), % we have to remove the positive examples covered
  setting(remove_negatives, RemoveNegatives),
  (RemoveNegatives=true ->  ord_subtract(TNegEIDs, NegEIDsCovered, NTNegEIDs)  ; NTNegEIDs=TNegEIDs),
  message(most_compressive_hypothesis, [Hypothesis, TestFold, PosEIDsCovered, NegEIDsCovered, NTPosEIDs, NTNegEIDs]),
  NumClauses1 is NumClauses+1,
  construct_incremental_theory(NTPosEIDs, NTNegEIDs, NAPosEIDs, NUE, HypGenPred, NumClauses1,
                               MaxClauses, TestFold, NCurrentTheory, Theory).

construct_incremental_theory([TPosEID|TPosEIDs], TNegEIDs, APosEIDs, NUE, HypGenPred, NumClauses, MaxClauses,
                             TestFold, CurrentTheory, Theory):-
  NUE1 is NUE+1,
  (setting(engine, progolem), setting(progolem_mode, pairs) ->
     NTPosEIDs = [TPosEID|TPosEIDs]
   ;
     message(non_compressive_example, [TPosEID, TPosEIDs, TNegEIDs]), % non compressive (or whatever metric) clause found for PosEID, continuing...
     NTPosEIDs=TPosEIDs
  ),
  (early_stop(NUE1, TPosEIDs, APosEIDs) ->
     Theory=CurrentTheory
   ;
     construct_incremental_theory(NTPosEIDs, TNegEIDs, APosEIDs, NUE1,
                                  HypGenPred, NumClauses, MaxClauses, TestFold, CurrentTheory, Theory)
  ).

%early_stop(+NumUncompressiveExamples Examples, +RemainPosEIDs, +AllPosEIDs)
early_stop(NumUncompExamples, _RemainPosEIDs, AllPosEIDs):-
  length(AllPosEIDs, N), % it's a bit stupid to keep computing this, it's a constant!
  NumUncompExamples>=N.% if the number of uncompressive examples is at least N, stop!

early_stop(NumUncompExamples, _RemainPosEIDs, _AllPosEIDs):-
  setting(max_uncompressive_examples, MaxUncompExamples),
  NumUncompExamples>=MaxUncompExamples,!.


%JCAS: 24/Aug/2010- This code should be disabled. It may make incremental theory construction stop much earlier than it should!
%early_stop(+NumUncompressiveExamples Examples, +RemainPosEIDs, +AllPosEIDs)
% early_stop(_NumUncompExamples, RemainPosEIDs, AllPosEIDs):-
%   exampleIDsWeights(RemainPosEIDs, RemainPosWeight),
%   exampleIDsWeights(AllPosEIDs, TotalPosWeight), % it's a bit stupid to keep computing this, it's a constant!
%   setting(minpos, MinPos),
%   setting(mincov, MinCov),
%   (MinPos>RemainPosWeight ; MinCov>RemainPosWeight/TotalPosWeight).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% updateBestHypothesis(+BestHypothesis, -NBestHypothesis)
%
% Given:
%   BestHypothesis: a tuple of the form (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                   (Hypothesis as a list of literals)
%                    with PosIDsCov and NegIDsCov being the coverage of the hypothesis in just the training data
%
% Returns:
%   NBestHypothesis: a tuple of the form (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                    with PosIDsCov and NegIDsCov being the full coverage of the hypothesis in all the data
%
% Notes:
%   This predicate is only needed because the show theory assumes the theory has the full coverage computed.
%   This is a bad idea however as it complicates things and decreases module independence.
%   Get rid of this predicate when possible
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

updateBestHypothesis((FScore, FClause, FClauseSig, FNumLiterals, _FPosIDsCov, _FNegIDsCov),
                     (FScore, FClause, FClauseSig, FNumLiterals, FFPosIDsCov, FFNegIDsCov)):-
  exampleIDs(APosEIDs, ANegEIDs),
  full_hypothesis_coverage(FClause, FClauseSig, APosEIDs, ANegEIDs, FFPosIDsCov, FFNegIDsCov).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% highestScoringHypothesis(+Hypotheses, +PosEIDs, +NegEIDs, -HighestScoringHypothesis)
%
%  Given:
%    Hypotheses: list of hypotheses tuples, each is of the form (Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                Hypothesis is in clause form
%    PosEIDs: positive example ids to check for the best hypothesis
%    NegEIDs: negative example ids to check for the best hypothesis
%
%  Returns:
%    HighestScoringHypothesis: the hypothesis tuple with highest score. I.e. (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                              when evaluated on PosEIDs, NegEIDs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

highestScoringHypothesis(Hypotheses, PosEIDs, NegEIDs, HighestScoringHypothesis):-
  emptyTheory(InitialTheory),
  bestHypothesis(Hypotheses, PosEIDs, NegEIDs, InitialTheory, HighestScoringHypothesis).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% emptyTheory(-Theory):
%
% Returns:
%   Theory: an empty theory
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

emptyTheory((0, [], [], [])).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% addHypothesisToTheory(+CurrentTheory, +TestFold, +Hypothesis, -NewTheory)
%
% Given:
%    CurrentTheory: a Theory tuple as described above
%    Hypothesis: a term of the form: (Score, Hypothesis, HypothesisSig, NumLiterals, PosCov, NegCov))
%    TestFold: an integer, the test fold (examples belonging to this fold do not appear as covered
%              in the hypothesis weight, but _do appear_ as covered by the theory. This is important
%              to allow efficient cross validation
%
% Returns:
%    NewTheory : an updated theory, resulted from adding Hypothesis to CurrentTheory (also a Theory tuple)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

addHypothesisToTheory((TotLiterals, PosCovered, NegCovered, Hypotheses),  %Current Theory
                      TestFold, % the test fold
                      (_Score, Hypothesis, HypSig, NumLiterals, HPosCov, HNegCov),   %Hypothesis
                      (NTotLiterals, NPosCovered, NNegCovered, NHypotheses)):- % New theory
  NTotLiterals is TotLiterals+NumLiterals,
  ord_union(HPosCov, PosCovered, NPosCovered),
  ord_union(HNegCov, NegCovered, NNegCovered),
  ord_subtract(HPosCov, PosCovered, NewPosCovered),
  ord_subtract(HNegCov, NegCovered, NewNegCovered),
  exampleIDsWeights(HPosCov, TestFold, WPosHyp),
  exampleIDsWeights(HNegCov, TestFold, WNegHyp),
  exampleIDsWeights(NewPosCovered, TestFold, WNewPosHyp),
  exampleIDsWeights(NewNegCovered, TestFold, WNewNegHyp),
  append(Hypotheses, [(Hypothesis, HypSig, NumLiterals, WPosHyp, WNegHyp, WNewPosHyp, WNewNegHyp)], NHypotheses).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  GREEDY ALGORITHM IMPLEMENTED BELOW %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% greedy_search(+Hypotheses, +MaxClauses, +TestFold, -Theory)
%
% Given:
%   Hypotheses: a list where each element is a tuple: (Hypothesis, HypSig, NumLiterals, ListExPos, ListExNeg)
%    where:
%      Hypothesis: is a unique hypothesis as a list of literals
%      HypSig: Hypothesis signature
%      NumLiterals: number of literals in hypothesis
%      ListExPos: list of example ids of the positive examples covered
%      ListExNeg: list of example ids of the negative examples covered
%
%    (Note: Hypotheses generated exclusively by examples from the test fold are not present)
%
%   MaxClauses: limits the theory to the first best MaxClauses (inf for no limit, that is, keep adding until metric positive)
%   TestFold: examples belonging to this fold are not considered when greedly picking the best hypothesis to add
%
% Returns:
%   Theory: a tuple of the form:  (TotLiterals, PosCovered, NegCovered, Hypotheses)
%
%    where:
%      TotLiterals: total number of literals in all hypothesis in Hypotheses
%      PosCovered: ordered list of all the positive examples covered by the theory (i.e. the union of the coverage of its hypotheses)
%      NegCovered: ordered list of all the negative examples covered by the theory (i.e. the union of the coverage of its hypotheses)
%      Hypotheses: list of tuples of the form: (Hypothesis, NumLiterals, NPos, NNeg, NNewPos, NNewNeg)
%
%      where:
%         Hypothesis: is a unique hypothesis (with variables in clause form)
%         HypSig: hypothesis signature
%         NumLiterals: number of literals in hypothesis
%         NPos: weight of positive examples hypothesis covered in the training data
%         NNeg: weight of negative examples hypothesis covered in the training data
%         NNewPos: weight of new positive examples covered (i.e. subtracting the ones covered by the previous hypothesis)
%         NNewNeg: weight of new negative examples covered (i.e. subtracting the ones covered by the previous hypothesis)
%
%   The order of the hypotheses in the Theory is important. The first hypotheses are the most discriminating ones
%
% Algorithm:
%    The idea is to pick the best hypothesis so far at each step. The best hypothesis is the one that increases
%  more the score of the current theory
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

greedy_search(Hypotheses, MaxClauses, TestFold, Theory):-
  emptyTheory(InitialTheory),
  exampleIDs(TestFold, _PosEIDsFold, _NegEIDsFold, PosEIDsNonFold, NegEIDsNonFold),
  greedyAux(InitialTheory, 0, MaxClauses, PosEIDsNonFold, NegEIDsNonFold, TestFold, Hypotheses, Theory).

%greedyAux(+CurrentTheory, +CurClause, +MaxClauses, +PosEIDsNonFold, +NegEIDsNonFold, +TestFold, +AllHypotheses, -FinalTheory)
greedyAux(Theory, MaxClauses, MaxClauses, _, _, _, _, Theory):-!. % Theory already has the maximum clauses
greedyAux(CurrentTheory, CurClause, MaxClause, PosEIDs, NegEIDs, TestFold, AllHypotheses, FinalTheory):-
  bestHypothesis(AllHypotheses, PosEIDs, NegEIDs, CurrentTheory, BestHypothesis),!,
  addHypothesisToTheory(CurrentTheory, TestFold, BestHypothesis, NCurrentTheory),
  CurClause1 is CurClause+1,
  greedyAux(NCurrentTheory, CurClause1, MaxClause, PosEIDs, NegEIDs, TestFold, AllHypotheses, FinalTheory).
greedyAux(Theory, _, _, _, _, _, _, Theory):-!. % no best hypothesis exist, terminate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% bestHypothesis(+Hypotheses, +PosEIDs, +NegEIDs, +CurrentTheory, -BestHypothesis)
%
%  Given:
%    Hypotheses: list of hypothesis tuples, each is of the form (Hypothesis, HypSig, NumLiterals, ListExPos, ListExNeg)
%    CurrentTheory: a tuple of the form:  (TotLiterals, PosCovered, NegCovered, Hypotheses)
%    PosEIDs: positive example ids to check for the best hypothesis
%    NegEIDs: negative example ids to check for the best hypothesis
%
%  Returns:
%    BestHypothesis: a term of the form of CurrentBestHypothesis (see below)
%
%  Notes:
%    It fails if there is no best hypothesis in Hypotheses (i.e. none has positive score)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bestHypothesis(Hypotheses, PosEIDs, NegEIDs, CurrentTheory, BestHypothesis):-
  initialHypothesisTerm(InitialHypothesis),
  bestHypothesis(Hypotheses, PosEIDs, NegEIDs, CurrentTheory, InitialHypothesis, BestHypothesis).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% bestHypothesis(+AllHypothesesData, +PosEIDs, +NegEIDs, +CurrentTheory, +CurrentBestHypothesis, -FinalBestHypothesis)
%
%  See above. The extra parameter
%    CurrentBestHypothesis: a tuple of the form:  (HypothesisScore, HypothesisData)
%        where:
%               HypothesisScore: a positive number
%               HypothesisData: a term of the form: (Hypothesis, HypSig, NumLiterals, ListExPos, ListExNeg)
%
%  holds the best hypothesis so far
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bestHypothesis([], _, _, _, (Score, BestHyp), (Score, BestHyp)):-
  stop_score(StopScore),
  Score>StopScore,!. % best hypothesis search should only fail when best hypothesis score is <= stop score
bestHypothesis([HypothesisTerm|Hypotheses], PEIDs, NEIDs, CurrentTheory, (CurBestScore, _CurrentBestHyp), BestHyp):-
  scoreGain(CurrentTheory, PEIDs, NEIDs, HypothesisTerm, Score),
  Score>CurBestScore,!,%Hypothesis Term score higher than best score so far
  bestHypothesis(Hypotheses, PEIDs, NEIDs, CurrentTheory, (Score, HypothesisTerm), BestHyp).
bestHypothesis([_|Hypotheses], PEIDs, NEIDs, CurrentTheory, CurrentBestHyp, BestHyp):-
  bestHypothesis(Hypotheses, PEIDs, NEIDs, CurrentTheory, CurrentBestHyp, BestHyp).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% scoreGain(+CurrentTheory, +PosEIDs, +NegEIDs, +Hypothesis, -Score)
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

scoreGain((_TotLiterals, TheoryPosCov, TheoryNegCov, _), PosEIDs, NegEIDs,
          (_Hypothesis, _HypSig, NumLiterals, HypPosCov, HypNegCov), Score):-
% Notice that to compute the score we just consider the newly covered examples. All the coverage
% of an hypothesis for examples previously covered is irrelevant to compute its score.
  ord_subtract(HypPosCov, TheoryPosCov, NewHypPosCov),
  ord_subtract(HypNegCov, TheoryNegCov, NewHypNegCov),
%
%
  ord_subtract(PosEIDs, TheoryPosCov, NewPosEIDs),
  ord_subtract(NegEIDs, TheoryNegCov, NewNegEIDs),

  hypothesis_info(NewHypPosCov, NewHypNegCov, NewPosEIDs, NewNegEIDs, HypInfo),
  score(NumLiterals, HypInfo, Score).

% initialHypothesisTerm(-(Score, Hypothesis)).
initialHypothesisTerm((0, nil)).
