%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-05-11
%
%   This file has predicates to generate a theory in Progolem way
%
%   Progolem: the idea is to positively reduce a clause, followed by negative reduce
%
%   algorithm progolem_hyp_generator(+Example, +PosExamples, +NegExamples, -Theory)
%     How to generate a single hypothesis from a set of examples
%
%     0. Let Theory = empty set
%     1. repeat
%     2.   Let Clauses = {Bottom clause of the first example in Examples}
%     3.   Let ScoreThreshold = Bottom clause score
%     4.   while(length(Clauses)>0)
%     5.     Let BestClauseSoFar = highest scoring clause from Clauses
%            Let SPos = an independent (from PosPairs) sample of K positive examples
%            Let NClauses = empty circular list % with at most N positions
%            for each clause, c, in NClauses do
%              for each positive example, p, in SPos do
%                Let c1 = ARMG(p, c)
%                Let score = c1's score
%                if(score>ScoreThreshold)
%                   NClauses = NClauses U c1
%                end if
%              end for
%            end for
%            ScoreThreshold = highest scoring clause in NClauses
%            Clauses=NClauses
%          end while
%          if(ScoreThreshold>0)
%            remove all positive (and negatives optionally) examples covered by BestClauseSoFar
%            Theory = Theory U NegativelyReduce(BestClauseSoFar)
%          end if
%        until ScoreThreshold<0
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Types:
%    ARMG: armg(core(SeedID, Ordered list of example ids used in its construction, % includes SeedID
%                    ListOfIndexs from  bottom clause of SeedID that constitute clause),
%               clause(Clause, ClauseSig))
%  ClauseInfo: tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(engine_progolem,
           [
             runProgolem/1
           ]
         ).

% GILPS modules
:- use_module('common', [generate_global_HypothesesAndTheory/2, generate_incremental_HypothesesAndTheory/1]).
:- use_module('../settings/settings', [setting/2]). % because of 'n' and 'k'
:- use_module('../bottom clause/bottom_clause', [sat/3]).
:- use_module('../bottom clause/clause_reduce', [positive_clause_reduce/3, positiveClauseReduce/6, negative_clause_reduce/8, negative_clause_reduce/10]).
:- use_module('../bottom clause/common_clause', [commonClause/4]).
:- use_module('../bottom clause/srmg', [create_srmg_heuristic_term/2, srmg/5, srmg/6, srmg/7]).
:- use_module('../examples/examples', [id2example/2, exampleIDsWeights/2]).
:- use_module('../hypotheses/score', [hypothesis_info/5, stop_score/1, score/3, verifies_partial_metrics/2, verifies_full_metrics/2]).
:- use_module('../hypotheses/coverage', [full_hypothesis_coverage/6, hypothesis_coverage/6]).
:- use_module('../utils/list', [elemsAtPos/3, firstNElemsOf/3, n_randomElems/3, randomPairs/3, custom_qsort/3, numbersList/3]).
:- use_module('../messages/messages', [message/2]).
:- use_module('../utils/clause', [prettyPrintLiterals/1]).

% YAP modules
:- use_module(library(lists), [nth/3, nth/4, reverse/2, flatten/2]).
:- use_module(library(apply_macros), [convlist/3, maplist/3]).
:- use_module(library(ordsets), [ord_subtract/3, ord_insert/3, ord_union/3]).
:- use_module(library(random), [randseq/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_armg(+ExampleID, -ARMG)
%
% Given:
%  ExampleID: the example id to compute the starting ARMG)
% 
% Returns:
%  ARMG: the resulting armg, see armg type above
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_armg(ExampleID, armg(core(ExampleID, [ExampleID], Indexs), clause(Bottom, BottomSig))):-
  id2example(ExampleID, Example),
  sat(Example, Bottom, BottomSig),
  length(Bottom, NumLiterals),
  numbersList(1, NumLiterals, Indexs).

%armg_core_to_clause(+core(SeedID, Remaining examples used in its construction, ListOfIndexs from SeedID), -Clause, -ClauseSig)
armg_core_to_clause(core(SeedID, _OtherConsIDs, IndexsFromSeed), Clause, ClauseSig):-
  id2example(SeedID, Example),
  sat(Example, Bottom, BottomSig), % this can be expensive if done often...
  elemsAtPos(Bottom, IndexsFromSeed, Clause),
  elemsAtPos(BottomSig, IndexsFromSeed, ClauseSig).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% runProgolem(+FileName)
%
% Given:
%   FileName: the filename to store the generated hypotheses and their coverages. If it's a variable it's ignored
%
% Displays the outcome of running Progolem in standard output, possibly saving the hypotheses (but not the theory)
% in FileName
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

runProgolem(FileName):-
  (setting(theory_construction, global) ->
    generate_global_HypothesesAndTheory(genHypFromExample_global, FileName)
%    format("Progolem can only be executed in incremental theory construction mode.~n", [])
   ;
  %setting(theory_construction, incremental)
    generate_incremental_HypothesesAndTheory(genHypFromExample_incremental)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% genHypFromExample_global(+ExampleID, +TPosEIDs, +APosEIDs, +ANegEIDs, +MaxHypothesesPerExample, -Hypotheses)
%
% Given:
%   ExampleID: example id to process now
%   TPosEIDs: ordered list of positive example ids remaining (i.e. the subset from APosEIDs not yet considered)
%   APosEIDs: ordered list of all positive example ids (to possibly test for coverage)
%   ANegEIDs: ordered list of all negative example ids (to possibly test for coverage)
%   MaxHypothesesPerExample: maximum number of hypotheses an example may generate
%
% Returns:
%   Hypotheses: a list of tuples (hypothesis, hypothesis signature)
%
% Notes:
%   This is the main distinguisher between ILP systems: the way hypotheses are generated
%   Notice that Progolem only outputs one hypothesis per example!
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_global(ExampleID, _TPosEIDs, APosEIDs, ANegEIDs, _MaxHypothesesPerExample, Result):-
  create_armg(ExampleID, armg(Core, clause(Bottom, BottomSig))),
  %id2example(ExampleID, Example),
  %sat(Example, Bottom, BottomSig),
  (hypothesis_score(Bottom, BottomSig, APosEIDs, ANegEIDs, NumLits, PosEIDsCov, NegEIDsCov, _HypInfo, Score) ->
     BottomClauseInfo=(Score, NumLits, PosEIDsCov, NegEIDsCov, armg(Core, clause(Bottom, BottomSig))),
     (setting(progolem_mode, reduce) ->
       ClauseInfo=BottomClauseInfo
      ;
       iterate_until_best_clause(1, [BottomClauseInfo], APosEIDs, APosEIDs, ANegEIDs, ClauseInfo)
     ),
     (negative_reduce(ClauseInfo, APosEIDs, ANegEIDs, BestHypothesis) ->
       BestHypothesis=(_Score, Hyp, HypSig, _NumLiterals, _PosIDsCov, _NegIDsCov),
       Result=[(Hyp,HypSig)]
     ;
       format("No compressive hypothesis~n",[]),
       Result=[] % no compressive hypothesis was found, don't waste time adding it
     )
   ;
    format("Bottom clause covers negatives~n",[]),%halt,
    Result=[] % bottom clause already covers negatives or no positives (may happen with noise, low recall or if min_resolutions is low)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% genHypFromExample_incremental(+TPosEIDs, +TNegEIDs, +APosEIDs, +TestFold, -BestHypothesis)
%
% Given:
%  TPosEIDs: ordered list of train positive examples id to generate best hypothesis from
%  TNegEIDs: ordered list of train negative examples id to generate best hypothesis from
%  APosEIDs: ordered list of all positive example ids of the current fold not yet entailed
%            (i.e. TPosEIDs plus the positive examples where one couldn't find compressive clauses)
%  TestFold: test fold
%
% Returns:
%   BestHypothesis: a tuple of the form (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                   (Hypothesis as a list of literals)
%
% Notes:
%   APosEIDs and ANegEIDs not strictly needed. Consider not using them later (they are here just because
%   the way theories are shown. they require the coverage to be known for train and test)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_incremental(TPosEIDs, TNegEIDs, APosEIDs, _TestFold, % review later the need for TestFold
                              BestHypothesis):-
  generate_seed_clauses(TPosEIDs, APosEIDs, TNegEIDs, SeedClauses),
  (setting(progolem_mode, reduce)->
      SeedClauses=[ClauseInfo]
    ;
      iterate_until_best_clause(1, SeedClauses, TPosEIDs, APosEIDs, TNegEIDs, ClauseInfo)
  ),
  negative_reduce(ClauseInfo, APosEIDs, TNegEIDs, BestHypothesis).

%generate_seed_clauses(+TPosEIDs, +APosEIDs, +TNegEIDs, -SeedClauses)
generate_seed_clauses(_, APosEIDs, TNegEIDs, SeedClauses):-
  setting(theory_construction, incremental),% pairs mode only applicable in incremental theory construction
  setting(progolem_mode, pairs),!,
  setting(progolem_initial_pairs_sample, NumPairs),
  message(compute_rmg_pairs, []),
  randomPairs(NumPairs, APosEIDs, Pairs),
  convlist(rmg_pair_info(APosEIDs, TNegEIDs), Pairs, AllClausesInfo),
  best_clauses(AllClausesInfo, SeedClauses).

generate_seed_clauses([TPosEID|_], APosEIDs, TNegEIDs, [BottomClauseInfo]):-
  %(setting(progolem_mode, single);setting(progolem_mode, reduce)),!,
  create_armg(TPosEID, armg(Core, clause(Bottom, BottomSig))),
  %id2example(TPosEID, Example),
  %sat(Example, Bottom, BottomSig),
  hypothesis_score(Bottom, BottomSig, APosEIDs, TNegEIDs, NumLits, PosEIDsCov, NegEIDsCov, _HypInfo, Score),
  BottomClauseInfo=(Score, NumLits, PosEIDsCov, NegEIDsCov, armg(Core, clause(Bottom, BottomSig))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% rmg_pair_info(+PosExampleIDs, +NegExampleIDs, +(ExID1, ExID2), -ClauseInfo)
%
% Given:
%  PosExampleIDs: ordered list of positive example ids to consider for coverage
%  NegExampleIDs: ordered list of negative example ids to consider for coverage
%  ExID1: first example ID
%  Ex2: second example ID
%
% Returns:
%  ClauseInfo: tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rmg_pair_info(PosEIDs, NegEIDs, (ExID1, ExID2), (Score, NumLits, PosEIDsCov, NegEIDsCov, armg(Core, clause(Clause, ClauseSig)))):-
  id2example(ExID1, Example1),
  id2example(ExID2, Example2),
  (setting(progolem_refinement_operator, armg) ->
     create_armg(ExID1, ARMG1),
     positive_clause_reduce(ARMG1, ExID2, armg(Core, clause(Clause, ClauseSig)))
   ;
     format("SRMGs not yet supported when we represent a clause as a list of indexs from the bottom~n", []),halt,
     create_srmg_heuristic_term(NegEIDs, SRMG_Heuristic),
     srmg(Example1, Example2, SRMG_Heuristic, Clause, ClauseSig)
  ),
  sort([ExID1, ExID2], GenCPosEIDs),
  coverage_computation(0, Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov, _HypInfo, NumLits, Score),
  message(rmg_pair, [Clause, Example1, Example2, ExID1, ExID2, (Score, NumLits, PosEIDsCov, NegEIDsCov)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% coverage_computation(+IterationNum, +Clause, +ClauseSig, +GenCPosEIDs, +PosEIDs, +NegEIDs,
%                      -PosEIDsCov, -NegEIDsCov, -HypInfo, -NumLits, -Score)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

coverage_computation(IterNum, Clause, ClauseSig, GenCPosEIDs, PosEIDs, NegEIDs,
                     PosEIDsCov, NegEIDsCov, HypInfo, NumLits, Score):-
  setting(progolem_bypass_coverage_iters, ByPassN),
  length(Clause, NumLits),
  (ByPassN>IterNum ->
     PosEIDsCov=GenCPosEIDs, NegEIDsCov=[],
     hypothesis_score_aux(PosEIDs, NegEIDs, NumLits, PosEIDsCov, NegEIDsCov, HypInfo, Score)
    ;
     hypothesis_score(Clause, ClauseSig, PosEIDs, NegEIDs, NumLits, PosEIDsCov, NegEIDsCov, HypInfo, Score)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% negative_reduce(+ClauseInfo, +TPosEIDs, +TNegEIDs, -BestHypothesis)
%
% Given:
%  ClauseInfo: a term of the form (CScore, CNumLiterals, CPosIDsCov, CNegIDsCov, ARMG)
%  TPosEIDs: ordered list of train positive example ids to consider for reduction
%  TNegEIDs: ordered list of train negative example ids to consider for reduction
%
% Returns:
%   BestHypothesis: a tuple of the form (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                   (Hypothesis as a list of literals)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

negative_reduce((CScore, _CNumLiterals, CPosIDsCov, CNegIDsCov, armg(_Core, clause(CClause, CClauseSig))),
                TPosEIDs, TNegEIDs,
                (FScore, FClause, FClauseSig, FNumLiterals, FPosEIDsCov, FNegEIDsCov)):-
  message(before_neg_reduction, [CClause, CClauseSig, CScore, CPosIDsCov, CNegIDsCov]),
  negative_clause_reduce(CClause, CClauseSig, TPosEIDs, TNegEIDs, CPosIDsCov, CNegIDsCov, FClause, FClauseSig, FPosEIDsCov, FNegEIDsCov),
  hypothesis_info(FPosEIDsCov, FNegEIDsCov, TPosEIDs, TNegEIDs, HypInfo),
  length(FClause, FNumLiterals),
  stop_criteria(FClause, FClauseSig, FNumLiterals, HypInfo, FScore).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% stop_criteria(+Clause, +ClauseSig, +NumLiterals, +HypInfo, -Score)
%
% Given:
%   Clause: as a list of literals
%   ClauseSig: Clause's signature
%   NumLiterals: an integer
%   HypInfo: a list with 4 integers: [TP, FP, FN, TN]
%
% Succeeds if clause has positive compression, otherwise fails
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

stop_criteria(Clause, ClauseSig, NumLiterals, [TP, FP, FN, TN], Score):-
  score(NumLiterals, [TP, FP, FN, TN], Score),
  message(after_neg_reduction, [Clause, ClauseSig, Score, NumLiterals, TP, FP]),
  (verifies_full_metrics(NumLiterals, [TP, FP, FN, TN]) ->
    true
   ;
    message(no_good_clause, [TP, FP, FN, TN, Score]),
    fail
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% iterate_until_best_clause(+Iteration, +CurrentClausesInfo, +TPosEIDs, +APosEIDs, +TNegEIDs, -BestClauseInfo)
%
% Given:
%   Iteration: an integer specifying the current iteration
%   CurrentClausesInfo: list of tuples (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%   TPosEIDs: ordered list of train positive example ids available for ARMG
%   APosEIDs: ordered list of train positive example ids available for coverage (same as above, plus non
%              compressive ones from previous iterations)
%   TNegEIDs: ordered list of train negative example ids
%
% Returns:
%   BestClauseInfo: the highest scoring clause info (no further refinement yields a better one)
%                   It's a tuple of the form (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

iterate_until_best_clause(Iter, CurrentClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, BestClauseInfo):-
  CurrentClausesInfo=[CurBestInfo|_],
  CurBestInfo=(Score, _NumLiterals, PosIDsCov, NegIDsCov, ARMG),
  message(best_rmg, [Iter, Score, ARMG, PosIDsCov, NegIDsCov]), %% UPDATE THIS, clause, GenPosEIDs by ARMG
  nextClauses(Iter, CurrentClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, NextClausesInfo),
  (NextClausesInfo=[] -> % no further best clauses
     BestClauseInfo=CurBestInfo
   ;
     Iter1 is Iter+1,
     iterate_until_best_clause(Iter1, NextClausesInfo, TPosEIDs, APosEIDs, TNegEIDs, BestClauseInfo)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% nextClauses(+Iter, +ClausesInfo, +TPosEIDs, +APosEIDs, +TNegEIDs, -NextClausesInfo)
%
% Given:
%   Iter: iteration number
%   ClausesInfo: a list of up to 'n' (user parameter) clauses info. Each is a tuple of the form
%            (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%   TPosEIDs: ordered list of positive examples used for training (i.e. considered for extending ARMG and coverage)
%   APosEIDs: ordered list of train positive example ids available for coverage (same as above, plus non
%              compressive ones from previous iterations)
%   TNegEIDs: ordered list of negative examples used for training (i.e. considered for coverage)
%
% Returns:
%   NextClauses: a list of up to 'n' clauses (ClausesInfo format). Each clause must have higher score than
%                the highest score in ClausesInfo
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

nextClauses(Iter, Clauses, TPosEIDs, APosEIDs, TNegEIDs, NClauses):-
  Clauses=[(HighestScore, NumLiterals, _, _, _ARMG)|_],%
  maplist(extend_clause_rmg(Iter, TPosEIDs, APosEIDs, TNegEIDs, HighestScore, NumLiterals), Clauses, SuccessorClauses),
  flatten(SuccessorClauses, AllSuccessorClauses),
  best_clauses(AllSuccessorClauses, NClauses).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% extend_clause_rmg(+Iter, +PosEIDs, +APosEIDs, +NegEIDs, +ScoreThreshold, +NumLiterals, +ClauseInfo, -NClauseTuples)
%
% Given:
%  Iter: iteration number
%  PosEIDs: list of positive example ids to consider for coverage
%  APosEIDs: ordered list of train positive example ids available for coverage (same as above, plus non
%            compressive ones from previous iterations)
%  NegEIDs: list of negative example ids to consider for coverage
%  ScoreThreshold: all NClauseTuples must be above this score
%  NumLiterals: number of literals of the score with score ScoreThreshold
%  ClauseInfo: tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
% Returns:
%  NClauseTuple: successors of ClauseInfo, each of the same form as ClauseInfo
%                they are ClauseTuple with ARMG extended by one extra positive example from PosExampleIDs but
%                not in GenClausePosEIDs
%
% Notes:
%  Only clauses with scores higher than the highest in ClauseTuples appear in NClauseTuple
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

extend_clause_rmg(Iter, PosExampleIDs, APosEIDs, NegExampleIDs, ScoreThreshold, NumLits, ClauseInfo, NClauseTuples):-
  setting(progolem_iteration_sample_size, NumExamples),
  ClauseInfo=(_,_,PosIDsCov,_,armg(core(_,GenClausePosEIDs,_),clause(_,_))), % we only want to consider positive examples that are not already covered by the ARMG
  ord_union(PosIDsCov, GenClausePosEIDs, DisregardPosEIDs), % GenClausePosEIDs should be a subset of PosIDsCov but may not be if min_resolutions is low
  %DisregardPosEIDs=GenClausePosEIDs,
  ord_subtract(PosExampleIDs, DisregardPosEIDs, ExtendARMGPosIDs), % determine pos examples that may be used to extend the ARMG  
  n_randomElems(ExtendARMGPosIDs, NumExamples, SelectedARMGPosIDs),
  convlist(pos_clause_reduce(Iter, ScoreThreshold, NumLits, APosEIDs, NegExampleIDs, ClauseInfo), SelectedARMGPosIDs, NClauseTuples).

%pos_clause_reduce(+IterNum, +ScoreThreshold, +NumLitsThreshold, +PosExampleIDs, +NegExampleIDs, +ClauseInfo, +PosEID2Reduce,
%                  -NextClauseInfo)
pos_clause_reduce(Iter, ScoreThreshold, NumLitsThreshold, PosEIDs, NegEIDs, (_, _, _, _, ARMG),
                  PosEID2Reduce, (Score, NumLiterals, PosEIDsCov, NegEIDsCov, NARMG)):-
  ARMG=armg(core(_, GenEIDs, _), clause(Clause, ClauseSignature)),
  id2example(PosEID2Reduce, PosExample),
  (setting(progolem_refinement_operator, armg) ->
     positive_clause_reduce(ARMG, PosEID2Reduce, armg(core(SeedID, NGenEIDs, Indexs), clause(Clause1, Clause1Sig))),
     %positiveClauseReduce(Clause, ClauseSignature, PosEID2Reduce, _FailProfile, NClause1, NClauseSignature1),
     setting(progolem_negative_sample_per_iteration, NegSample),
     (NegSample=0 ->
       NClause=Clause1,
       NClauseSignature=Clause1Sig,
       NARMG=armg(core(SeedID, NGenEIDs, Indexs), clause(NClause, NClauseSignature))
      ;
       n_randomElems(NegEIDs, NegSample, SampleNegEIDs),
% negative_reduce(+ClauseInfo, TPosEIDs, +TNegEIDs, -BestHypothesis)
%
% Given:
%  ClauseInfo: a term of the form (CScore, CNumLiterals, CPosIDsCov, CNegIDsCov, ARMG)
       format("Negative reduction at each iteration is not yet supported when we represent a clause as a list of indexs from the bottom~n", []),halt,
       negative_clause_reduce(NClause1, NClauseSignature1, PosEIDs, SampleNegEIDs, NClause, NClauseSignature, _PosEIDsCov, _NegEIDsCov),
       NARMG=armg(core(SeedID, NGenEIDs, Indexs), clause(NClause1, NClauseSignature1))
       %Note: when we do negative reduction of a small sample it is possible that we prune away more literals than we should
       % and thus getting an inconsistent clause with respect to the noise setting
     )     
   ;
     format("SRMGs are not yet supported when we represent a clause as a list of indexs from the bottom~n", []),halt,
     create_srmg_heuristic_term(NegEIDs, SRMG_Heuristic),
     srmg(Clause, ClauseSignature, PosExample, SRMG_Heuristic, NClause, NClauseSignature),
     ord_insert(GenEIDs, PosEID2Reduce, NGenEIDs),
     NARMG=armg(core(SeedID, NGenEIDs, Indexs), clause(NClause, NClauseSignature))
  ),
%  format("PosEIDs:~w, NegEIDs:~w~n", [PosEIDs, NegEIDs]),
  coverage_computation(Iter, NClause, NClauseSignature, NGenEIDs, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov,
                       HypInfo, NumLiterals, Score),
  message(extended_rmg, [PosExample, PosEID2Reduce, GenEIDs, NumLiterals, Score, HypInfo]),
  compareClause(>, (Score, NumLiterals, _, _, _), (ScoreThreshold, NumLitsThreshold, _, _, _)).
%  format("Score: ~w NumLiterals: ~w Threshold: ~w~n", [Score, NumLiterals, ScoreThreshold]),

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compareClause(-Compare, +ClauseScoreInfo1, -ClauseScoreInfo2)
%
% Given:
%  ClauseScoreInfo1: a tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%  ClauseScoreInfo2: a tuple of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
% Returns:
%  Compare: either '=' if the ClauseScores are identical
%                  '>' if first score is better than second
%                  '<' if second score is better than first
%
% Notes:
%   A ClauseScore is better than other if the score is higher, or if is equal but has less literals
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compareClause(>, (S1, _, _, _, _), (S2, _, _, _, _)):- S1>S2,!.
compareClause(>, (S, L1, _, _, _), (S, L2, _, _, _)):-
  ( (setting(evalfn, compression);setting(evalfn, compression_ratio)) ->
       L1>L2 % if compression or compression ratio are the metrics then, for the same score, we prefer longer clauses
     ;
       L1<L2 % otherwise, for the same score, we prefer shorter clauses
  ),
  !.
% we want to remove clauses if they have the same score and same length (are likely to be equivalent or even the same!,
% we are unlikely gain much in keeping both), so we say that two such clauses are equal
compareClause(=, (S, L, _, _, _), (S, L, _, _, _)):- !.
%compareClause(=, (S, L, A, B, C, D, E), (S, L, A, B, C, D, E)):- !. % with this we would keep both if they are distinct (that's what sort/2) does
compareClause(<, _, _):- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% best_clauses(+ClauseScores, -BestClauses)
%
% Given:
%  Clauses: a list of tuples of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%
% Returns:
%  BestClauses: the top 'n' highest scoring clauses
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

best_clauses(ClauseScores, BestClauses):-
  setting(progolem_beam_width, NumBestClauses),
  (setting(progolem_stochastic_beam, true) ->
    do_tournament(ClauseScores, NumBestClauses, BestClauses)
   ;
    custom_qsort(ClauseScores, compareClause, SClauses), %clauses sorted according to score (ascending)
    % note that if we used sort(ClauseScores, SClauses) we would be prefering longer literals
    %sort(ClauseScores, SClauses), %clauses sorted according to score (ascending)
    reverse(SClauses, SClauses1), % reverse the clause to have clauses descendingly sorted by score
    firstNElemsOf(SClauses1, NumBestClauses, BestClauses)
  ).
  %maplist(removeU, BestClauses, SClauses2), write(SClauses2),nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% do_tournament(+Clauses, +N, -SelectedClauses)
%
% Given:
%  Clauses: a list of tuples of the form: (Score, NumLiterals, PosIDsCov, NegIDsCov, ARMG)
%  N: Number of clauses to select for next iteration
%
% Returns:
%  SelectedClauses: the N clauses selected for the next iteration in no particular order
%                              This is sub list of Clauses
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

do_tournament([], _N, []):-!.
do_tournament(ClauseScores, N, BestClauses):-
  length(ClauseScores, NumClauses),
  setting(progolem_tournament_size, K), %  K=TournamentSize: see description in settings file
  (K>NumClauses ->
     do_tournament_aux(N, ClauseScores, NumClauses, NumClauses, BestClauses)    
    ;
     do_tournament_aux(N, ClauseScores, K, NumClauses, BestClauses)
  ).
  
do_tournament_aux(0, _, _, _, []):-!.
do_tournament_aux(N, ClauseScores, K, NumClauses, [WinnerC|RemainClauses]):-
  randseq(K, NumClauses, TournamentClausesIDs),
  sort(TournamentClausesIDs, STournamentClausesIDs),
  elemsAtPos(ClauseScores, STournamentClausesIDs, TournamentClauses),
  find_max_score(TournamentClauses, WinnerC),
  N1 is N-1,
  do_tournament_aux(N1, ClauseScores, K, NumClauses, RemainClauses).

%find_max_score(+TournamentClauses, -WinnerClause)
find_max_score([Clause|RClauses], WinnerClause):-
  find_max_score_aux(RClauses, Clause, WinnerClause).

%find_max_score_aux(+RemainClauses, +BestClauseSoFar, -WinnerClause)
find_max_score_aux([], WinnerClause, WinnerClause).
find_max_score_aux([CurClause|Cs], BestClauseSoFar, WinnerClause):-
  CurClause=(Score1, _, _, _, _),
  BestClauseSoFar=(Score2, _, _, _, _),
  (Score1>Score2 ->
      find_max_score_aux(Cs, CurClause, WinnerClause)    
    ;
      find_max_score_aux(Cs, BestClauseSoFar, WinnerClause)
  ).

removeU((S, L, _, _, _), (S,L)).

%hypothesis_score(+Clause, +ClauseSig, +PosEIDs, +NegEIDs, -NumLiterals, -PosEIDsCov, -NegEIDsCov, -HypInfo, -Score)
hypothesis_score(Clause, ClauseSig, PosEIDs, NegEIDs, NumLiterals, PosEIDsCov, NegEIDsCov, HypInfo, Score):-
  hypothesis_coverage(Clause, ClauseSig, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov),
  length(Clause, NumLiterals),
  hypothesis_score_aux(PosEIDs, NegEIDs, NumLiterals, PosEIDsCov, NegEIDsCov, HypInfo, Score).

%hypothesis_score_aux(+PosEIDs, +NegEIDs, +NumLiterals, +PosEIDsCov, +NegEIDsCov, -HypInfo,  -Score)
hypothesis_score_aux(PosEIDs, NegEIDs, NumLiterals, PosEIDsCov, NegEIDsCov, HypInfo, Score):-
  hypothesis_info(PosEIDsCov, NegEIDsCov, PosEIDs, NegEIDs, HypInfo),
  verifies_partial_metrics(NumLiterals, HypInfo),
  score(NumLiterals, HypInfo, Score).
