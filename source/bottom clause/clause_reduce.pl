%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-03-13
%
%
%    This file contains predicates to reduce a clause. This is used in ProGolem, a bottom clause is
% generated and then it's reduced by providing further positive examples
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(clause_reduce,
            [
              reduceToHeadOutputVars/4,
              positive_clause_reduce/3,
              positiveClauseReduce/6,
              negative_clause_reduce/8,
              negative_clause_reduce/10,
              examplesFullFailingProfile/4,
              fullFailingProfile/4
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]). % because of clause_length, 'negative_reduction_measure' and 'negative_reduction_effort'
:- use_module('../clause evaluation/common_clause_evaluation', [identifyFirstFailingLiteral/4, identifyFirstFailingLiteral/5]).
:- use_module('../utils/list', [afterFirstNElemsOf/3, splitAtPos/4, member_identical_chk/2, merge_keys/2, remove_positions/3, replaceAt/4]).
:- use_module('../utils/clause', [atomArgs/4]).
:- use_module('../examples/examples', [id2example/2, exampleIDsWeights/2]).
:- use_module('../hypotheses/coverage', [full_hypothesis_coverage/6]). % to make negative reduction more independent
:- use_module('../hypotheses/score', [score/4, verifies_partial_metrics/2]). % to score alternative negative reductions
%:- use_module('../mode declarations/mode_declarations', [determinate_transformation/2]).

% YAP modules
:- use_module(library(lists), [nth/3, nth/4, append/3, member/2, memberchk/2, reverse/2, flatten/2, select/3]).
:- use_module(library(ordsets), [list_to_ord_set/2, ord_insert/3, ord_union/3, ord_subset/2, ord_subtract/3]).
:- use_module(library(apply_macros), [maplist/3, selectlist/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% reduceToHeadOutputVars(+Clause, +ClauseSignature, +MaximumReducedClauses, -ReducedClauses)
%
% Given:
%   Clause: a list of literals representing a clause
%   ClauseSignature: list of signatures for Clause
%   MaximumReducedClauses: maximum number of reduced clauses to output (<0 for all)
%
% Returns:
%   ReducedClauses: a list where each tuple is a pair: (Clause, ClauseSignature)
%
% Notes:
%   Shall we limit ReducedClauses to the user provided clause_length? probably we should..
%
% algorithm ReduceToHeadOuputVars(+Clause, -ReducedClauses)
%
%  1.  Let HeadOutVar = unique output variables from Clause's Head
%  2.  Let HeadInVar = unique input variables from Clause's Head
%  3.  do breadth first search from HeadInVar
%  4.     at each iteration add the SubClauses which have HeadOutVar as a subset of their instantiated variables
%         until maximum reduced clauses reached 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

reduceToHeadOutputVars(Clause, ClauseSig, MaximumReducedClauses, ReducedClauses):-
  computeReducedClauses(Clause, ClauseSig, MaximumReducedClauses, ReducedClausesPositions),
  maplist(convertLiteralsPos(Clause, ClauseSig), ReducedClausesPositions, ReducedClauses).
  %format("They are:~w~n", [ReducedClauses]).

%convertLiteralsPos(+Clause, +ClauseSig, +ClauseAsListOfLiteralPos, -(Clause,ClauseSig))
convertLiteralsPos(Clause, ClauseSig, LiteralsPos, (RedClause, RedClauseSig)):-
  literalPos2Clause(LiteralsPos, Clause, ClauseSig, 1, RedClause, RedClauseSig, _, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% computeReducedClauses(+Clause, +ClauseSig, +MaximumReducedClauses, -ReducedClausesPositions)
%
% Returns:
%  ReducedClausesPositions: a list of list of literal positions.
%                           Each list of literal positions is a reduced clause
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeReducedClauses([Head|Body], [HeadSig|BodySig], MaximumReducedClauses, ReducedClausesPositions):-
  atomArgs(Head, HeadSig, HIV, HOV),
  (ord_subset(HOV, HIV)-> % head is itself a reduced clause, stop
     ReducedClausesPositions=[[1]] % [1] stands for the head literal position
   ;
     computeReducedClauses([([1], HIV)], 1, [Head|Body], [HeadSig|BodySig], HOV,
                           0, MaximumReducedClauses, ReducedClausesPositions)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% computeReducedClauses(+SubClausesToVisit, +CurLength, +Clause, +ClauseSig, +HeadOutVars,
%                       +NumReducedClauses, +MaximumReducedClauses, -ReducedClauses)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeReducedClauses([], _, _, _, _, _, _, []):-!.
computeReducedClauses(_, _, _, _, _, N, N, []):-!.
computeReducedClauses(SubClausesToVisit, CurLen, Clause, ClauseSig, HeadOutVars, NumReduced, MaxReduced, ReducedClauses):-
  setting(clause_length, MaxLen),
  CurLen<MaxLen,!,
  %format("Computing successors of length ~w...~n", [CurLen]),
  subClausesSuccessors(SubClausesToVisit, Clause, ClauseSig, TempNextClausesToVisit),
  findReducedClauses(TempNextClausesToVisit, HeadOutVars, NumReduced, MaxReduced,
                     NextClausesToVisit, NextNumReduced, ReducedClausesThisTurn),
  %length(NextClausesToVisit, NumNextToVisit), format("~w clauses to visit next~n", [NumNextToVisit]),
  %format("~w possible clauses found~n", [NextNumReduced, MaxReduced]),
  append(ReducedClausesThisTurn, RemainReducedClauses, ReducedClauses),
  CurLen1 is CurLen+1,
  computeReducedClauses(NextClausesToVisit, CurLen1, Clause, ClauseSig, HeadOutVars,
                        NextNumReduced, MaxReduced, RemainReducedClauses).
computeReducedClauses(_, _, _, _, _, _, _, []):-!. %Sub clauses to visit have maximum length already

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% subClausesSuccessors(+CurSubClauses, +Clause, +ClauseSig, -NextSubClauses)
%
% Given:
%   CurSubClauses: list of subclauses, where each one is tuple: 
%           (reversed list of literal positions (from Clause), variables from Clause that are instantiated)
%   Clause: Clause from which the subclauses are taken from
%   ClauseSig: Clause's signature
%
% Returns:
%   NextSubClauses: list of the subclauses that are neighbour of CurSubClauses
%
% Notes:
%   A clause C1 is a successor of a clause C2 if C1=C2,L1, where L1 is a literal that has all its input variables
%   instantiated in C2
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subClausesSuccessors(CurClauses, Clause, ClauseSig, Result):-
  getAtomVars(Clause, ClauseSig, LitInVars, LitOutVars), %precompute atom variables
  maplist(successors(LitInVars, LitOutVars), CurClauses, NextClauses),
%  format("successors of ~w are ~w~n",[CurClauses, NextClauses]),
  flatten(NextClauses, Result).

%getAtomVars(+Clause, +ClauseSig, -LitInVars, -LitOutVars)
getAtomVars([], [], [], []).
getAtomVars([Lit|Lits], [LitSig|LitsSig], [LitInVars|InVars], [LitOutVars|OutVars]):-
  atomArgs(Lit, LitSig, LitInVars, LitOutVars),
  getAtomVars(Lits, LitsSig, InVars, OutVars).

/*
%successors(+LitsInVars, +LitsOutVars, +CurSubClause, -SuccessorsOfCurSubClause)
successors(LitsInVars, LitsOutVars, CurSubClause, SuccessorsCurSubClause):-
  successorsOf(LitsInVars, LitsOutVars, 1, CurSubClause, SuccessorsCurSubClause).
*/

%this is slower because splitting LitsInVars and LitsOutVars causes a lot of garbage collection
successors(LitsInVars, LitsOutVars, ([LastLitPos|RLitsPos], InstVars), SuccessorsCurSubClause):-
  N is LastLitPos+1,
  afterFirstNElemsOf(LitsInVars, N, RelevantLitsInVars),
  afterFirstNElemsOf(LitsOutVars, N, RelevantLitsOutVars),!,
  successorsOf(RelevantLitsInVars, RelevantLitsOutVars, N, ([LastLitPos|RLitsPos], InstVars), SuccessorsCurSubClause).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% successorsOf(+LitsInVars, +LitsOutVars, +CurPos, +(CurSubClause, InstVars), -ListOf(NextClause, NextInstVars))
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

successorsOf([], [], _, _, []):-!.
successorsOf([AtomInVars|LitInVars], [AtomOutVars|LitOutVars], CurPos, ([LastLitPos|RemLits], InstVars), [Neighbour|Result]):-
  CurPos>LastLitPos,
  ord_subset(AtomInVars, InstVars), !,
  ord_union(AtomOutVars, InstVars, NextInstVars),
  Neighbour= ([CurPos, LastLitPos|RemLits], NextInstVars),
  CurPos1 is CurPos+1,
  successorsOf(LitInVars, LitOutVars, CurPos1, ([LastLitPos|RemLits], InstVars), Result).
successorsOf([_|LitInVars], [_|LitOutVars], CurPos, CurSubClause, Result):-
  CurPos1 is CurPos+1,
  successorsOf(LitInVars, LitOutVars, CurPos1, CurSubClause, Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%findReducedClauses(+TempNextClausesToVisit, +HeadOutVars, +NumReduced, +MaxReduced,
%                   -NextClausesToVisit, -NextNumReduced, -ReducedClausesThisTurn)
%
% Given:
%   TempNextClausesToVisit: All clauses to visit next turn. Each clause is a tuple:
%                     (reversed list of literal positions, list of instantiated variables)
%
% Returns:
%   NextClausesToVisit: Clauses from TempNextClausesToVisit which do not have HeadOutVars instantiated
%   ReducedClausesThisTurn: Clauses from TempNextClausesToVisit which have HeadOutVars instantiated
%                           (only the literal positions are kept and reversed to get the original order)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

findReducedClauses([], _, NumReduced, _, [], NumReduced, []):-!.
findReducedClauses(_, _, MaxReduced, MaxReduced, [], MaxReduced, []):-!.
findReducedClauses([(RLitsPos, InstVars)|VClauses], HeadOutVars, NumReduced, MaxReduced,
                   NextClausesToVisit, NextNumReduced, [LitsPos|RClauses]):-
  ord_subset(HeadOutVars, InstVars),!,
  reverse(RLitsPos, LitsPos),
  NumReduced1 is NumReduced+1,
  findReducedClauses(VClauses, HeadOutVars, NumReduced1, MaxReduced,
                     NextClausesToVisit, NextNumReduced, RClauses).
findReducedClauses([Clause|VClauses], HeadOutVars, NumReduced, MaxReduced,
                   [Clause|NextClausesToVisit], NextNumReduced, RClauses):-
  findReducedClauses(VClauses, HeadOutVars, NumReduced, MaxReduced,
                     NextClausesToVisit, NextNumReduced, RClauses).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% negative_clause_reduce(+Clause, +ClauseSignature, +PosEIDs, +NegEIDs,
%                        -ReducedClause, -ReducedClauseSignature, -PosEIDsCov, -NegEIDsCov)
%
% Given:
%   Clause: a list of literals representing a clause
%   ClauseSignature: list of signatures for Clause
%   PosEIDs: ordered list of positive examples to be considered (Clause may entail some already and we would
%             like the reduced clause to entail more)
%   NegEIDs: ordered list of negative examples to be considered (Clause may entail some already and we would
%             like the reduced clause to do not entail any more)
%
% Returns:
%   ReducedClause: Clause negatively reduced with all Atoms
%   ReducedClauseSignature: list of signatures for ReducedClause
%   PosEIDsCov: ordered list of positive example ids covered by ReducedClause (a subset of PosEIDs)
%   NegEIDsCov: ordered list of negative example ids covered by ReducedClause (a subset of NegEIDs)
%
% Notes:
%   This predicate returns a Clause, ReducedClause, that is a subset of Clause and still does not
%   cover any atom in Atoms. (if an atom in Atoms is covered by Clause, it is ignored)
%
%   This predicate calls the background knowledge. We assume there are no disconnected literals
%   in Clause as there won't be if it's a bottom clause, or a previous reduced clause
%   We also assume Clause does not contain repeated literals
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

negative_clause_reduce(Clause, ClauseSignature, PosEIDs, NegEIDs,
                       ReducedClause, ReducedClauseSignature, FPosEIDsCov, FNegEIDsCov):-
  full_hypothesis_coverage(Clause, ClauseSignature, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov),
  negative_clause_reduce(Clause, ClauseSignature, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov,
                         ReducedClause, ReducedClauseSignature, FPosEIDsCov, FNegEIDsCov).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% negative_clause_reduce(+Clause, +ClauseSignature, +PosEIDs, +NegEIDs,
%                        +PosEIDsCov, +NegEIDsCov,
%                        -ReducedClause, -ReducedClauseSignature, -FPosEIDsCov, -FNegEIDsCov)
%
% Given: (the same as above)
%   with: PosEIDsCov: the positive example ids Clause is known to cover
%         NegEIDsCov: the negative example ids Clause is known to cover
%
% Notes:
%   The only motivation for this predicate is efficiency. It avoids the initial coverage computation when
%   (as often is the case), we already know the coverage of Clause
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

negative_clause_reduce([], [], _, _, [], [], [], [], [], []):-!. %in case the start clause is already empty
negative_clause_reduce(Clause, ClauseSignature, PosEIDs, NegEIDs, PosEIDsCov, NegEIDsCov,
                     ReducedClause, ReducedClauseSignature, FPosEIDsCov, FNegEIDsCov):-
  ord_subtract(PosEIDs, PosEIDsCov, PosEIDsNonCov),
  ord_subtract(NegEIDs, NegEIDsCov, NegEIDsNonCov),
  exampleIDsWeights(PosEIDsCov, PosCovWeights),
  exampleIDsWeights(NegEIDsCov, NegCovWeights),
  (setting(negative_reduction_effort, normal) ->
    negativeClauseReduceAux(PosEIDsNonCov, NegEIDsNonCov, PosCovWeights, NegCovWeights, Clause, ClauseSignature, [],
                            ReducedClause, ReducedClauseSignature, NPosEIDsNonCov, NNegEIDsNonCov)
   ;%setting(negative_reduction_effort, exhaustive)
    repeatUntilNoChange(Clause, ClauseSignature, PosEIDsNonCov, NegEIDsNonCov, PosCovWeights, NegCovWeights,
                        ReducedClause, ReducedClauseSignature, NPosEIDsNonCov, NNegEIDsNonCov)
  ),
  ord_subtract(NegEIDs, NNegEIDsNonCov, FNegEIDsCov),
  determine_positive_coverage(ReducedClause, ReducedClauseSignature, PosEIDs, NPosEIDsNonCov, FPosEIDsCov).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% determine_positive_coverage(+RedClause, +RedClauseSig, +AllPosEIDs, +PosEIDsNonCov, -PosEIDsCov)
%  positive coverage needs to be updated if reduce for consistency was used
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_positive_coverage(RedClause, RedClauseSig, AllPosEIDs, PosEIDsNonCov, PosEIDsCov):-
  ord_subtract(AllPosEIDs, PosEIDsNonCov, PosEIDsCovForSure),
  full_hypothesis_coverage(RedClause, RedClauseSig, PosEIDsNonCov, [],
                           PosEIDsCovExtra, []),
  ord_union(PosEIDsCovForSure, PosEIDsCovExtra, PosEIDsCov).

%repeatUntilNoChange(+CurClause, +CurClauseSignature, +PosEIDsNonCov, +NegEIDsNonCov, +PosCovWeights, +NegCovWeights,
%                    -ReducedClause, -ReducedClauseSignature, -NPosEIDsNonCov, -NNegEIDsNonCov)
repeatUntilNoChange(CurClause, CurClauseSig, PosEIDsNonCov, NegEIDsNonCov, PosCovWeights, NegCovWeights,
                    ReducedClause, ReducedClauseSig, NPosEIDsNonCov, NNegEIDsNonCov):-
  negativeClauseReduceAux(PosEIDsNonCov, NegEIDsNonCov, PosCovWeights, NegCovWeights, CurClause, CurClauseSig, [], 
                          CurReducedClause, CurReducedClauseSig, NPosEIDsNonCov, NNegEIDsNonCov),
  length(CurClause, N1),
  length(CurReducedClause, N2),
  (N1=N2 ->
    ReducedClause=CurReducedClause,
    ReducedClauseSig=CurReducedClauseSig,
    NPosEIDsNonCov=PosEIDsNonCov,
    NNegEIDsNonCov=NegEIDsNonCov
   ;
    format("Reducing further (temporary clause size:~w)~n", [N2]),
    repeatUntilNoChange(CurReducedClause, CurReducedClauseSig, NPosEIDsNonCov, NNegEIDsNonCov, PosCovWeights, NegCovWeights,
                        ReducedClause, ReducedClauseSig, NPosEIDsNonCov, NNegEIDsNonCov)
  ).

%negaticeClauseReduceAux(+PosEIDsNonCov, +NegEIDsNonCov, +PosCovWeights, +NegCovWeights, +Clause, +ClauseSig, +FailLiterals,
%                        -RedClause, -RedClauseSignature, -NPosEIDsNonCov, -NNegEIDsNonCov)
negativeClauseReduceAux(PosEIDsNonCov, NegEIDsNonCov, PosCovWeights, NegCovWeights, Clause, ClauseSig, FailLiterals,
                        ReducedClause, ReducedClauseSignature, NPosEIDsNonCov, NNegEIDsNonCov):-
  choose_cutoff_literal(Clause, ClauseSig, PosEIDsNonCov, NegEIDsNonCov, PosCovWeights, NegCovWeights, LiteralPos,
                        NewPosEIDsNonCov, NewNegEIDsNonCov, NewPosCovWeights, NewNegCovWeights),
  %portray_clause(Clause),nl,
  %format("LiteralPos: ~w~n", [LiteralPos]),
  (LiteralPos=0 -> % just in case there is no failing literal
    ReducedClause=Clause, ReducedClauseSignature=ClauseSig,
    NPosEIDsNonCov=NewPosEIDsNonCov, NNegEIDsNonCov=NewNegEIDsNonCov
   ;
    computeSupportClause(Clause, ClauseSig, LiteralPos,
                         SupportClause, SupportClauseSig, NonSupportLiterals, NonSupportLiteralsSig,
                         _AfterFailLit, _AfterFailLitSig),
    append(SupportClause, NonSupportLiterals, NewClause),
    append(SupportClauseSig, NonSupportLiteralsSig, NewClauseSig),
    %portray_clause(NewClause),nl,
    nth(LiteralPos, Clause, FailLiteral),
    (member_identical_chk(FailLiteral, FailLiterals)->
      %we had already encountered FailLiteral before
        %format("Fail literal was found before~n",[]),
        ReducedClause=NewClause, ReducedClauseSignature=NewClauseSig,
        NPosEIDsNonCov=NewPosEIDsNonCov, NNegEIDsNonCov=NewNegEIDsNonCov
      ;
        negativeClauseReduceAux(NewPosEIDsNonCov, NewNegEIDsNonCov, NewPosCovWeights, NewNegCovWeights, NewClause, NewClauseSig,
                                [FailLiteral|FailLiterals], ReducedClause, ReducedClauseSignature, NPosEIDsNonCov, NNegEIDsNonCov)
    )
   ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% reduce_for_consistency(+NegCovWeights)
%
% Given:
%  NegCovWeights: weight of negative examples covered
%
% Succeeds iff we should reduce clause for consistency
%
% Notes:
%  This predicate is just for efficiency purposes. Reducing for anything other than consistency is much more
%  expensive as we have to compute the positive fail profile.
%  There are a few cases where the user didn't ask to optimize for consistency but are equivalent as optimizing
%  for it.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

reduce_for_consistency(_):-
  setting(negative_reduction_measure, consistency),!.
reduce_for_consistency(_):-
  setting(noise, 0),!. % no noise is allowed
reduce_for_consistency(NegCovWeights):-
  setting(maxneg, NegCovWeights),!. % the clause already covers the maximum negatives allowed

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% choose_cutoff_literal(+Clause, +ClauseSig, +PosEIDsNonCov, +NegEIDsNonCov, +PosCovWeights, +NegCovWeights, 
%                       -LiteralPos, -PosEIDsNotCovered, -NegEIDsNotCovered, -NewPosCovWeights, -NewNegCovWeights)
%
% Given:
%  Clause: the clause to test the example ids against
%  ClauseSig: Clause's signature
%  PosEIDsNonCov: an ordered list of (positive) example ids that we do not cover but would like to cover
%  NegEIDsNonCov: an ordered list of (negative) example ids that we do not cover and want to avoid covering
%  PosCovWeights: number representing the absolute value of the positive weights covered by Clause (i.e True Positives)
%  NegCovWeights: number representing the absolute value of the negative weights covered by Clause (i.e False Positives)
%
% Returns:
%  LiteralPos: the literal position where all literals to its right are to be pruned away
%  NewPosEIDsNonCov: ordered list of PosEIDs that we have not yet covered (try to cover in next iteration)
%  NewNegEIDsNonCov: ordered list of NegEIDs that we have not yet covered (continue to avoid covering in next iter)
%  NewPosCovWeights: number representing the new True Positives after removing all literals to the right of LiteralPos
%  NewNegCovWeights: number representing the new False Positives after removing all literals to the right of LiteralPos
%
% Notes:
%  The best LiteralPos to remove depends on the user selected evaluation function. But in general is the one
%  which greedily maximizes the difference between positives covered and negatives covered. If the score
%  for a small LiteralPos is the same as an higher order we prefer the smaller one (bias towards shorter clauses)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

choose_cutoff_literal(Clause, ClauseSig, PosEIDsNonCov, NegEIDsNonCov, PosCovWeights, NegCovWeights,
                      LiteralPos, NewPosEIDsNonCov, NewNegEIDsNonCov, NewPosCovWeights, NewNegCovWeights):-
  (reduce_for_consistency(NegCovWeights) ->
     fail_profile(NegEIDsNonCov, Clause, ClauseSig, NegFailProfile, NegEIDsAlreadyCovered), % in principle, NegEIDsAlreadyCovered=[],
     (NegFailProfile=[LiteralPos-_|_] ->
         % unless it had been miscalculated before due to resource bound call
         NewPosEIDsNonCov=PosEIDsNonCov, % this is not exactly true that there will not be any new positives covered after removing
                                        % all literals after LiteralPos. However, we cannot afford to test exactly what will those ids be
         ord_subtract(NegEIDsNonCov, NegEIDsAlreadyCovered, NewNegEIDsNonCov), % we bother updating the coverage because it may save time later
         exampleIDsWeights(NegEIDsAlreadyCovered, NegAlreadyCovWeights)
       ;
         LiteralPos=0, % no failing literal
         NegAlreadyCovWeights=0
     ),
     NewPosCovWeights = PosCovWeights,
     NewNegCovWeights is NegCovWeights + NegAlreadyCovWeights % we don't really need to update this...
   ;
   %some other metric
   %due to clause reordering and to the bound in the number of resolutions it's possible that some positives or negatives
   %previously thought not to be covered are now covered
    fail_profile(PosEIDsNonCov, Clause, ClauseSig, PositiveFailProfile, PosEIDsAlreadyCovered),
    fail_profile(NegEIDsNonCov, Clause, ClauseSig, NegativeFailProfile, NegEIDsAlreadyCovered),

    %format("PosFailProfile: ~w~n", [PositiveFailProfile]),
    %format("NegFailProfile: ~w~n", [NegativeFailProfile]),

    exampleIDsWeights(PosEIDsAlreadyCovered, PosAlreadyCovWeights),
    exampleIDsWeights(NegEIDsAlreadyCovered, NegAlreadyCovWeights),

    ord_subtract(PosEIDsNonCov, PosEIDsAlreadyCovered, TPosEIDsNonCov),
    ord_subtract(NegEIDsNonCov, NegEIDsAlreadyCovered, TNegEIDsNonCov),
    exampleIDsWeights(TPosEIDsNonCov, PosNonCovWeights),
    exampleIDsWeights(TNegEIDsNonCov, NegNonCovWeights),
    UpdatedPosCovWeights is PosCovWeights + PosAlreadyCovWeights,
    UpdatedNegCovWeights is NegCovWeights + NegAlreadyCovWeights,

    length(Clause, NumLiterals),
    best_cutoff_literal(NumLiterals, PositiveFailProfile, NegativeFailProfile, UpdatedPosCovWeights, UpdatedNegCovWeights,
                        PosNonCovWeights, NegNonCovWeights, LiteralPos, NewPosEIDsCovered, NewNegEIDsCovered),
    % update NewPosEIDsCovered and NewNegEIDsCovered considering the (few or none) examples covered in fail profile
    ord_subtract(TPosEIDsNonCov, NewPosEIDsCovered, NewPosEIDsNonCov),
    ord_subtract(TNegEIDsNonCov, NewNegEIDsCovered, NewNegEIDsNonCov),

    exampleIDsWeights(NewPosEIDsCovered, NewPosCovWeightsAux),
    exampleIDsWeights(NewNegEIDsCovered, NewNegCovWeightsAux),
    NewPosCovWeights is UpdatedPosCovWeights + NewPosCovWeightsAux,
    NewNegCovWeights is UpdatedNegCovWeights + NewNegCovWeightsAux
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% best_cutoff_literal(+NumLiterals, +PosFailProfile, +NegFailProfile, +PosCovWeights, +NegCovWeights,
%                     +PosNonCovWeights, +NegNonCovWeights, -LiteralPos, -PosEIDsCovered, -NegEIDsCovered)
%
% Given:
%  NumLiterals: number of literals in the clause
%  PosFailProfile: a descending (on Pos) ordered list of tuples: Pos-IDss, where Pos is a literal position
%                  and IDs is the ordered list of positive examples that first fail at that literal position
%  NegFailProfile: a descending (on Pos) ordered list of tuples: Pos-IDss, where Pos is a literal position
%                  and IDs is the ordered list of negative examples that first fail at that literal position
%  PosCovWeights: value of the positive weights covered by current clause (i.e True Positives), positive number
%  NegCovWeights: value of the negative weights covered by current clause (i.e False Positives)  negative number
%  PosNonCovWeights: value of the positive weights not covered by current clause (i.e False Negatives), positive number
%  NegNonCovWeights: value of the negative weights not covered by current clause (i.e True Negatives), negative number
%
% Returns:
%  LiteralPos: the best failing literal pos (i.e. the one that maximizes compression).
%  PosEIDsCovered: ordered list of positive example IDs that are covered after every literal to the right
%                  of LiteralPos is removed (LiteralPos exclusive)
%  NegEIDsCovered: ordered list of negative example IDs that are covered after every literal to the right
%                  of LiteralPos is removed (LiteralPos exclusive)
%
% Notes:
%  In case of ties (i.e. same number of literals for the same weights) we prefer shorter clauses and thus prune more
%  literals. A LiteralPos=0 means don't choose anything, there's nothing to gain from a cut.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

best_cutoff_literal(NumLiterals, PosFailProfile, NegFailProfile, PosCovWeights, NegCovWeights,
                    PosNonCovWeights, NegNonCovWeights, LiteralPos, PosEIDsCovered, NegEIDsCovered):-
  fail_profile_to_weight_balance(PosFailProfile, PosNonCovWeights, NumLiterals, PosWeightBalance),
  fail_profile_to_weight_balance(NegFailProfile, NegNonCovWeights, NumLiterals, NegWeightBalance),
  TP=PosCovWeights, FP=abs(NegCovWeights), FN=PosNonCovWeights, TN=abs(NegNonCovWeights),
  negative_reduction_measure(Measure),
  score(Measure, NumLiterals, [TP, FP, FN, TN], CurScore),
  %format("Cur score: ~w~n", [CurScore]),
  best_cutoff_literal_aux(PosWeightBalance, NegWeightBalance, PosCovWeights, NegCovWeights, CurScore, LiteralPos),
  examples_after_position(LiteralPos, PosFailProfile, PosEIDsCovered),
  examples_after_position(LiteralPos, NegFailProfile, NegEIDsCovered).

%negative_reduction_measure(-Measure)
negative_reduction_measure(Measure):-
  setting(negative_reduction_measure, auto),!,
  setting(evalfn, Measure).
negative_reduction_measure(Measure):-
  setting(negative_reduction_measure, Measure).

%best_cutoff_literal_aux(+PosWeightBalance, +NegWeightBalance, +PosCovWeights, +NegCovWeights, +CurScore, -LiteralPos)
best_cutoff_literal_aux(PosWeightBalance, NegWeightBalance, PosCovWeights, NegCovWeights, CurScore, LiteralPos):-
  best_cutoff_literal_aux(PosWeightBalance, NegWeightBalance, PosCovWeights, NegCovWeights, CurScore, 0, LiteralPos).

%best_cutoff_literal_aux(+PosWeightBalance, +NegWeightBalance, +PosCovWeights, +NegCovWeights, +CurBestScore, +CurBestLiteralPos, -LiteralPos)

best_cutoff_literal_aux([(LP,WLP,WRP)|PosWBalance], [(LP,WLN,WRN)|NegWBalance], PosCovWeights, NegCovWeights, CurBestScore,
                        _CurBestLiteralPos, LiteralPos):-
  TP is PosCovWeights + WRP,
  FP is abs(NegCovWeights) + abs(WRN),
  FN is WLP,
  TN is abs(WLN),
  verifies_partial_metrics(LP, [TP, FP, FN, TN]),
  negative_reduction_measure(Measure),
  score(Measure, LP, [TP, FP, FN, TN], CurScore),
  CurScore>=CurBestScore,!,
  best_cutoff_literal_aux(PosWBalance, NegWBalance, PosCovWeights, NegCovWeights, CurScore, LP, LiteralPos).
best_cutoff_literal_aux(_, _, _, _, _, LiteralPos, LiteralPos):-!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% examples_after_position(+LiteralPos, +FailProfile, -ExampleIDsCovered)
%
% Given:
%  LiteralPos: Literal position
%  FailProfile: as described in fail_profile/4
%
% Returns:
%  ExampleIDsCovered: ordered list of example ids covered after LiteralPos (not including literal pos!)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

examples_after_position(LiteralPos, FailProfile, ExampleIDsCovered):-
  examples_after_position_aux(FailProfile, LiteralPos, TExampleIDsCovered),
  sort(TExampleIDsCovered, ExampleIDsCovered).

examples_after_position_aux([], _, []):-!.
examples_after_position_aux([Pos-_|_], LP, []):-
  Pos=<LP, !.
examples_after_position_aux([_Pos-EIDs|FailProfile], LP, NExampleIDsCovered):-
  append(EIDs, ExampleIDsCovered, NExampleIDsCovered),!, %cut is crucial, we just want the first solution
  examples_after_position_aux(FailProfile, LP, ExampleIDsCovered).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% fail_profile_to_weight_balance(+FailProfile, +TotalWeightsInFailProfile, +NumLiterals, -WeightBalance)
%
% Given:
%  FailProfile: as described in fail_profile/4
%  TotalWeightsInFailProfile: sum of all the weights of all example ids present in the FailProfile
%  NumLiterals: number of literals present in the clause from which the fail profile was derived
%
% Returns:
%  WeightBalance: descending ordered list with NumLiterals positions, each a tuple with 3 elements: (LP, WL, WR)
%                 LP: Literal Position, 
%                 WL: Weights covered to the left of Literal Position (inclusive with Literal Position)
%                 WR: Weights covered to the right of Literal Position, 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fail_profile_to_weight_balance(FailProfile, TotalWeightsInFailProfile, NumLiterals, WeightBalance):-
  fail_profile_to_weight_balance(NumLiterals, FailProfile, TotalWeightsInFailProfile, 0, WeightBalance).
  %reverse(RWeightBalance, WeightBalance).

%fail_profile_to_weight_balance(+NumLiterals, +FailProfile, +RemainingWeightsToLeftInclusive, +TotalWeightsToRight, -WeightBalance)
fail_profile_to_weight_balance(0, [], 0, _, []):-!.
fail_profile_to_weight_balance(Pos, [Pos-EIDs|FailProfile], LW, RW, [(Pos,LW,RW)|WeightBalance]):-
  !,
  exampleIDsWeights(EIDs, WeightsAtPos),
  Pos1 is Pos-1,
  LW1 is LW - WeightsAtPos,
  RW1 is RW + WeightsAtPos,
  fail_profile_to_weight_balance(Pos1, FailProfile, LW1, RW1, WeightBalance).
fail_profile_to_weight_balance(Pos, FailProfile, LW, RW, [(Pos,LW,RW)|WeightBalance]):-
  %Pos>First position of failing profile
  Pos1 is Pos-1,
  fail_profile_to_weight_balance(Pos1, FailProfile, LW, RW, WeightBalance).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% fail_profile(+ExampleIDs, +Clause, +ClauseSig, -FailProfile, -ExampleIDsCovered)
%
% Given:
%  ExampleIDs: ordered list of example ids to use for constructing the failing profile
%  Clause: a list of literals representing a clause 
%  ClauseSig: Clause's signature
%
% Returns:
%  FailProfile: a descending sorted list of tuples: LiteralPos-ExampleIDs where
%               LiteralPos is the first failing literal position, ExampleIDs is an ordered list of all examples
%               IDs that first fail at that position. (E.g. [7-[103,204],5-[54]])
%  ExampleIDsCovered: ordered list of the example ids, from ExampleIDs, that the clause already covers
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fail_profile(ExampleIDs, Clause, ClauseSig, FailProfile, ExampleIDsCovered):-
  fail_profile_aux(ExampleIDs, Clause, ClauseSig, FailProfileAux, ExampleIDsCovered),
  merge_keys(FailProfileAux, FailProfile1),
  reverse(FailProfile1, FailProfile).

fail_profile_aux([], _, _, [], []).
fail_profile_aux([ExampleID|ExampleIDs], Clause, ClauseSig, NFailProfile, NEIDsCovered):-
  identifyFirstFailingLiteral(Clause, ClauseSig, ExampleID, FailLiteralPos),
  (FailLiteralPos=0 ->
      NEIDsCovered=[ExampleID|EIDsCovered],
      NFailProfile=FailProfile
    ;
      NEIDsCovered=EIDsCovered,
      NFailProfile=[FailLiteralPos-ExampleID|FailProfile]
  ),
  fail_profile_aux(ExampleIDs, Clause, ClauseSig, FailProfile, EIDsCovered).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% computeSupportClause(+Clause, +ClauseSignature, +AtomPos,
%                      -SupportClause, -SupportClauseSignature,
%                      -NonSupportLiterals, -NonSupportLiteralsSignature,
%                      -LiteralsAfterAtomPos, -LiteralsSigAfterAtomPos)
%
% Given:
%  Clause: clause as a list of literals (first is head)
%  ClauseSignature: Clause' signature
%  AtomPos: position of the atom (1 based, relative to clause) that we want to compute the support literal set
%
% Returns:
%  SupportClause: list of literals needed to connected Head's input variables with Atom's input variables (clause head and Atom included)
%  SupportClauseSignature: SupportLiterals' signatures
%  NonSupportLiterals: literals from Lits that do not belong to support literals  (clause head not included)
%  NonSupportLiteralsSignature: NonSupportLiterals signatures
%  LiteralsAfterAtomPos: list of literals after AtomPos
%  LiteralsSigAfterAtomPos: LiteralsAfterAtomPos signatures
%
% Notes:
%  SupportLiterals is a support set computed with breadth first search
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeSupportClause([Head|Body], [HeadSig|BodySig], 1, [Head], [HeadSig], [], [], Body, BodySig):-!. % Head case
computeSupportClause([Head|Body], [HeadSig|BodySig], AtomPos, SupClause, SupClauseSig, %Body case
                     NonSupLits, NonSupLitsSigs, LiteralsAfterAtomPos, LiteralsSigAfterAtomPos):-
  splitAtPos([Head|Body], AtomPos, [Head|BodyUntilLitPos], LiteralsAfterAtomPos),
  splitAtPos([HeadSig|BodySig], AtomPos, [HeadSig|BodySigUntilLitPos], LiteralsSigAfterAtomPos),
  getLitsInfo([Head|Body], [HeadSig|BodySig], [info(1, HeadInVars, _, _, _)|BodyInfo]),
  iterative_deep(1, AtomPos, BodyInfo, AtomPos, HeadInVars, [1], SupLiteralsPos),% max depth is AtomPos
  literalPos2Clause(SupLiteralsPos, [Head|BodyUntilLitPos], [HeadSig|BodySigUntilLitPos], 1,
                    SupClause, SupClauseSig, NonSupLits, NonSupLitsSigs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% iterative_deep(+CurDepth, +MaxDepth, +LitsInfo, +AtomIndex, +InitInstVars, +InitPath, -FinalPath)
%
% Performs iterative_deepening (up to depth MaxDepth)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

iterative_deep(CurDepth, _, LitsInfo, AtomIndex, InitInstVars, InitPath, Path):-
  dfs(CurDepth, LitsInfo, AtomIndex, InitInstVars, InitPath, Path),!.
iterative_deep(CurDepth, MaxDepth, LitsInfo, AtomIndex, InitInstVars, InitPath, Path):-
  %format("Depth:~w (Max:~w)~n", [CurDepth, MaxDepth]),
  CurDepth=<MaxDepth,!,
  CurDepth1 is CurDepth+1,
  iterative_deep(CurDepth1, MaxDepth, LitsInfo, AtomIndex, InitInstVars, InitPath, Path).
iterative_deep(_, _, _, _, _, _, _):-
  format("Could not compute support set of literal. Badly formed clause(?)~n", []),
  fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% dfs(+Depth, +AvailableLitsInfo, +AtomIndex, +CurInstVars, +CurPath, -FinalPath)
%
% Given:
%   Depth: Num literals still allowed to be added
%   AvailableLitsInfo: a list of the form: info(LitIndex, IV, OV, Lit, LitSig) with literal's
%               LitIndex input and output variables
%   AtomIndex: the atom Index we want to reach
%   CurInstVars: ordered list (no reps) of all the variables instantiated so far
%   CurPath: list of indexs (reversed) with the literals indexs seen so far
%
% Returns:
%   FinalPath: list of indexs with the minimal number of literals to get from the head to
%              AtomIndex
%
% Notes: this predicate fails if there is no solution at a given depth
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dfs(0, _, _, _, _, _):-!, fail.
dfs(Depth, ACI, AtomIndex, InstVars, CurPath, FinalPath):-
  %Depth>0,
  splitAtPos(ACI, _, _, [info(LitIndex, IV, OV, _, _)|NACI]),
  ord_subset(IV, InstVars),
  NCurPath=[LitIndex|CurPath],
  (LitIndex=AtomIndex ->
     reverse(NCurPath, FinalPath)
   ;
     ord_subtract(OV, InstVars, [NV|NewVars]),% there must be at least one new variable
     % testing for the existence of a new output variable is not needed but speeds up search
     ord_union([NV|NewVars], InstVars, NInstVars),
     Depth1 is Depth-1,
     dfs(Depth1, NACI, AtomIndex, NInstVars, NCurPath, FinalPath)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% litsInfo2Clause(+LitsInfo, -Clause, -ClauseSig)
%
% Given:
%  LitsInfo: a list of terms: info(Index, InVars, OutVars, Lit, LitSig) for each Lits, LitsSig
%
% Returns:
%  Clause: a clause as a list of literals
%  ClauseSig: Clause signature
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

litsInfo2Clause([], [], []).
litsInfo2Clause([info(_,_,_,Lit,LitSig)|Info], [Lit|Lits], [LitSig|LitsSig]):-
  litsInfo2Clause(Info, Lits, LitsSig).

%literalPos2Clause(+SuppLiteralsPos, +Clause, +ClauseSig, +CurPos,
%                  -SuppClause, -SuppClauseSig, -NonSuppClause, -NonSuppClauseSig)
literalPos2Clause([], _, _, _, [], [], [], []):-!.
literalPos2Clause([LitPos|LitsPos], [Lit|Lits], [LitSig|LitsSig], LitPos,
                  [Lit|SuppClause], [LitSig|SuppClauseSig], NonSuppClause, NonSuppClauseSig):-
  !, CurPos1 is LitPos+1,
  literalPos2Clause(LitsPos, Lits, LitsSig, CurPos1, SuppClause, SuppClauseSig, NonSuppClause, NonSuppClauseSig).
literalPos2Clause(LitsPos, [Lit|Lits], [LitSig|LitsSig], CurPos, SuppClause, SuppClauseSig, [Lit|NonSuppClause], [LitSig|NonSuppClauseSig]):-
  CurPos1 is CurPos+1,
  literalPos2Clause(LitsPos, Lits, LitsSig, CurPos1, SuppClause, SuppClauseSig, NonSuppClause, NonSuppClauseSig).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% positive_clause_reduce(+ARMG, +ExampleID, -NewARMG)
%
% Given:
%   ARMG: armg(core(SeedID, Remaining ordered list of example ids used in its construction,
%                    ListOfIndexs from  bottom clause of SeedID that constitute clause),
%               clause(Clause, ClauseSig))
%   ExampleID: example id to do the armg 
%
% Returns:
%  NewARMG: Updated ARMG with literals that cause ARMG not to entail ExampleID removed
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

positive_clause_reduce(armg(core(SeedID, OtherConsIDs, Indexs), clause(ARMG, ARMGSig)), ExampleID,
                       armg(core(SeedID, NewConsIDs, NIndexs), clause(ReducedARMG, ReducedARMGSig))):-
  id2example(ExampleID, Atom),
  ord_insert(OtherConsIDs, ExampleID, NewConsIDs),
  (ARMG\=[Atom|_] ->
    NIndexs=[], 
    ReducedARMG=[],
    ReducedARMGSig=[]
   ;
    getLitsInfo(ARMG, ARMGSig, ClauseInfo),
    positiveClauseReduceAux(ARMG, ARMGSig, ClauseInfo, ExampleID, 2, ReducedARMG, ReducedARMGSig, FailLitsPos),
    remove_positions(Indexs, FailLitsPos, NIndexs)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% positiveClauseReduce(+Clause, +ClauseSignature, +ExampleID, -RemovedLiteralsIndexs, -ReducedClause, -ReducedClauseSignature)
%
% Given:
%   Clause: a list of literals representing a clause
%   ClauseSignature: list of signatures for Clause
%   ExampleID: the id of the example that should match the clause head (representing a positive example)
%
% Returns:
%   RemovedLiterals: sorted list of literal indexs (from Clause), that needed to be removed in order for Clause to subsume Example
%   ReducedClause: Clause with the body literals, that were responsible for it not to subsume Atom, removed
%   ReducedClauseSignature: list of signatures for ReducedClause
%
% Notes:
%   This predicate calls the background knowledge. We assume there are no essential disconnected literals
%   in Clause as there won't be if it's a bottom clause, or a previous reduced clause  
%
% E.g.
%  positiveClauseReduce([class(X, mammal),flies(X),milk(X)], class(dog, mammal),
%               [class(+animal, #class),flies(+animal),milk(+animal)], RC, RCS)
%               RC=[class(X, mammal), milk(X)]
%               RCS=[class(+animal, #class), milk(+animal)]
%       assuming the background knowledge has milk(dog) but not flies(dog).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

positiveClauseReduce([Head|_], Sig, ExampleID, RemovedLitsIndexs, [], []):-
  id2example(ExampleID, Example),
  Head\=Example,!, %in case Head does not match Example (but doesn't bind Head)
  length(Sig, LenHyp),
  numbersList(1, LenHyp, RemovedLitsIndexs).
positiveClauseReduce(Clause, ClauseSignature, ExampleID, RemovedLiteralsIndexs, ReducedClause, ReducedClauseSignature):-
  getLitsInfo(Clause, ClauseSignature, ClauseInfo),
  positiveClauseReduceAux(Clause, ClauseSignature, ClauseInfo, ExampleID, 2, ReducedClause, ReducedClauseSignature, RemovedLiteralsIndexs).

%positiveClauseReduceAux(+Clause, +ClauseSig, +ClauseInfo, +ExampleID, +FailAfterPos (inclusive), -RedClause, -RedClauseSignature, -FailLitsPos),
positiveClauseReduceAux(Clause, ClauseSig, ClauseInfo, ExampleID, AfterPos, RedClause, RedClauseSig, FailingProfile):-
  %format("Trying to identify first failing literal:~q~n with ~w~n", [Clause, ExampleID]),
  identifyFirstFailingLiteral(Clause, ClauseSig, ExampleID, AfterPos, LiteralPos),
  %format("Fail literal:~w~n", [LiteralPos]),
  (LiteralPos=0 -> % no failing literal pos, accept Clause as the reduced Clause
    FailingProfile=[],
    RedClause=Clause,
    RedClauseSig=ClauseSig
    %litsInfo2Clause(ClauseInfo, RedClause, RedClauseSig) %ReducedClause=Clause
   ;%Clause has a failing literal in it at LiteralPos position

    nth(LiteralPos, Clause, Lit, TClause),
    nth(LiteralPos, ClauseSig, _LitSig, TClauseSig),
    %utils_clauses:skolemize(Lit, LitS), format("LiteralPos failed: ~w (~w)~n", [LiteralPos, LitS]),
    findAdjustedLiteralPos(ClauseInfo, Lit, TClauseInfo, AdjustedLiteralPos),% this is to update ClauseInfo
%    format("Pos clause reduce AdjustedFailLitPos:~w~n", [AdjustedLiteralPos]),
    removeDisconnectedLiterals(TClause, TClauseSig, TClauseInfo, NClause, NClauseSig, NClauseInfo, DisconnectPositions),
    append([AdjustedLiteralPos|DisconnectPositions], RFailingProfile, FailingProfile),!, % cut crucial here, we just want the first append solution
    positiveClauseReduceAux(NClause, NClauseSig, NClauseInfo, ExampleID, LiteralPos, RedClause, RedClauseSig, RFailingProfile)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% getLitsInfo(+Lits, +LitsSig, -LitsInfo)
%
% Given:
%  Lits: a list of literals
%  LitsSig: a list of literals signatures
%
% Returns:
%  LitsInfo: a list of terms: info(Index, InVars, OutVars, Lit, LitSig) for each Lits, LitsSig
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

getLitsInfo(Lits, LitsSig, LitsInfo):-
  getLitsInfo(Lits, LitsSig, 1, LitsInfo).

%getLitsInfo(+Lits, +LitsSig, +CurIndex, -LitsInfo)
getLitsInfo([], [], _, []).
getLitsInfo([Lit|Lits], [LitSig|LitsSig], CurIndex, [info(CurIndex, InVars, OutVars, Lit, LitSig)|CInfo]):-
  atomArgs(Lit, LitSig, InVars, OutVars),
  CurIndex1 is CurIndex+1,
  getLitsInfo(Lits, LitsSig, CurIndex1, CInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% findAdjustedLiteralPos(+ClauseInfo, +Lit, -NClauseInfo, -AdjustedLiteralPos)
%
% Returns:
%   NClauseInfo: updated ClauseInfo with Lit removed
%   AdjustedLiteralPos: Lit position in the original clause (extracted from ClauseInfo)
% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

findAdjustedLiteralPos([info(Pos, _, _, L, _)|Info], Lit, Info, Pos):-
  L==Lit,!.
findAdjustedLiteralPos([Info|Infos], Lit, [Info|NInfos], APos):-
  findAdjustedLiteralPos(Infos, Lit, NInfos, APos).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% removeDisconnectedLiterals(+Clause, +ClauseSig, +ClauseInfo, -NClause, -NClauseSig, -NClauseInfo, -RemovedPositions)
%
% Given:
%  Clause: clause as a list of literals (the first literal is assumed to be the head)
%  ClauseSig: Clause's signatures
%  ClauseInfo: a list of terms: info(Index, InVars, OutVars, Lit, LitSig) for each Lits, LitsSig
%
% Returns:
%  NClause: Clause where the literals with the input variables not instantiated removed
%  NClauseSig: NClauseSig
%  NClauseInfo: updated clause info (i.e. infos for removed literals pruned)
%  RemovedPositions: ordered list of removed positions. Note that this positions are relative
%                    to the original clause (that's what the Index in Info is important)
%
%  E.g.
%   (Example with clause signatures rather than clause info)
%    removeDisconnectedLiterals([a(X),b(X,Y)], [a(+int),b(+int,+int)], Clause, ClauseSig, RemovedPositions)
%                Clause = [a(X), true],
%                ClauseSig = [a(+int), true]
%                ReplacedPositions = [2]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

removeDisconnectedLiterals([Head|Body], [HeadSig|BodySig], [info(1, HIV, HOV, Head, HeadSig)|Info],
                           [Head|NBody], [HeadSig|NBodySig], [info(1, HIV, HOV, Head, HeadSig)|RInfo], RP):-
  removeDisconnectedLiteralsAux(Body, BodySig, Info, HIV, NBody, NBodySig, RInfo, RP).

%removeDisconnectedLiteralsAux(+Literals, +LitsSig, +Info, +CurInstVars, -FLiterals, -FLitsSig, -RInfo, -ReplacedPositions)
removeDisconnectedLiteralsAux([], [], [], _, [], [], [], []).
removeDisconnectedLiteralsAux([Lit|Lits], [LitSig|LitSigs], [info(CurPos, LIV, LOV, Lit, LitSig)|Info], InstVars,
                              [Lit|RLits], [LitSig|RLitSigs], [info(CurPos, LIV, LOV, Lit, LitSig)|RInfo], RP):-
  ord_subset(LIV, InstVars),!,% all LIV occur in InstVars, so Lit can be called
  ord_union(LOV, InstVars, NInstVars),
  removeDisconnectedLiteralsAux(Lits, LitSigs, Info, NInstVars, RLits, RLitSigs, RInfo, RP).
removeDisconnectedLiteralsAux([_|Lits], [_|LitSigs], [info(CurPos, _, _, _, _)|Info], InstVars,
                               RLits, RLitsSigs, RInfo, [CurPos|RP]):-
  removeDisconnectedLiteralsAux(Lits, LitSigs, Info, InstVars, RLits, RLitsSigs, RInfo, RP).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% examplesFullFailingProfile(+Clause, +ClauseSignature, +ExampleIDs, -FailingProfiles)
%
% Given:
%   Clause: a list of literals representing a clause
%   ClauseSignature: list of signatures for Clause
%   ExampleIDs: ordered list of examples to compute the failing profile for
%
% Returns:
%  FailingProfiles: a list where each element is a tuple:
%                    (ExampleID-FailingProfileForExampleID)
%                   FailingProfileForExampleID is a list of integers
%                   Each integer is an index (1-based) respective to Clause that, is a failing
%                   literal
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

examplesFullFailingProfile(Clause, ClauseSig, ExampleIDs, FailingProfiles):-
  getLitsInfo(Clause, ClauseSig, ClauseInfo), %info(Index, InVars, OutVars, Lit, LitSig) for each Lits, LitsSig
  maplist(computeFullFailingProfile(Clause, ClauseSig, ClauseInfo), ExampleIDs, FailingProfiles).

%computeFullFailingProfile(+Clause, +ClauseSig, +ClauseInfo, +ExampleID, -FailingProfile).
computeFullFailingProfile(Clause, ClauseSig, ClauseInfo, ExampleID, (ExampleID-FailingProfile)):-
  %format("Computing fail profile for example:~w~n", [ExampleID]),
  id2example(ExampleID, Example),
  fullFailingProfileAux(Clause, ClauseSig, ClauseInfo, Example, 2, FailingProfile).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% fullFailingProfile(+Clause, +ClauseSignature, +Atom, -FailingProfile)
%
% Given:
%   Clause: a list of literals representing a clause
%   ClauseSignature: list of signatures for Clause
%   Atom: an atom that matches the clause head for which we want to compute its full failing profile
%
% Returns:
%   FailingProfile: ordered list of literal positions (from Clause) that, if removed, make Clause entail Atom
%
% Notes:
%   This predicate is identical to positiveClauseReduce except that we identify the failing literals rather
%   than removing them
%
% E.g.
%  fullFailingProfile([class(X, mammal),flies(X),milk(X)],                    % Clause
%                     [class(+animal, #class),flies(+animal),milk(+animal)],  % ClauseSignature
%                      class(dog, mammal), FP).
%
%       FP=[2] %i.e, if flies(X) is removed Clause entails example class(dog, mammal)
%       assuming the background knowledge has milk(dog) but not flies(dog).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fullFailingProfile([Head|_], _, Atom, [1]):-
  Head\=Atom,!. % Head does not match Atom, full failing profile is just the head
fullFailingProfile(Clause, ClauseSignature, Atom, FailingProfile):-
  getLitsInfo(Clause, ClauseSignature, ClauseInfo),
  fullFailingProfileAux(Clause, ClauseSignature, ClauseInfo, Atom, 2, FailingProfile).

%fullFailingProfileAux(+Clause, +ClauseSig, +ClauseInfo, +Atom, +PrevFailLitPos, -FullFailingProfile),
fullFailingProfileAux([], [], _, _, _, []):-!. %in case the start clause is already empty
fullFailingProfileAux([Head|_], _, _, Atom, _, [1]):- Head\=Atom,!. %in case Head does not match atom
fullFailingProfileAux(Clause, ClauseSig, ClauseInfo, Atom, PrevPos, FailingProfile):-
  identifyFirstFailingLiteral(Clause, ClauseSig, Atom, PrevPos, LiteralPos),
  (LiteralPos=0 -> % no failing literal pos, accept Body as the reduced body
    FailingProfile=[]
   ;%Clause has a failing literal in it at LiteralPos position
    nth(LiteralPos, Clause, Lit, TClause),
    nth(LiteralPos, ClauseSig, _LitSig, TClauseSig),
    findAdjustedLiteralPos(ClauseInfo, Lit, TClauseInfo, AdjustedLiteralPos),
    %format("AdjustedFailLitPos:~w~n", [AdjustedLiteralPos]),
    removeDisconnectedLiterals(TClause, TClauseSig, TClauseInfo, NClause, NClauseSig, NClauseInfo, DisconnectPositions),
    %format("Disconnected positions: ~w~n", [DisconnectPositions]),
    append([AdjustedLiteralPos|DisconnectPositions], RFailingProfile, FailingProfile),!, % cut crucial here, we just want the first append solution
    fullFailingProfileAux(NClause, NClauseSig, NClauseInfo, Atom, LiteralPos, RFailingProfile)
  ).
