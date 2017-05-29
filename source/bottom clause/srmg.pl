%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-08-13
%
%    This file contains predicates to compute the symmetric relative minimal generalization
%  of two clauses.
%
%
%  There's a linear algorithm to determine if an srmg bottom subsumes another.
%  An srmg can be viewed as a two list of integers (indexs) over each bottom clause used
%  to construct it. An srmg, srmg1, subsumes another srmg, srmg2, with respect to one example E,
%  if its list of integers (for bottom E) is a subset of the list of integers for srmg2 AND
%  at those positions, it unifies!
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(srmg,
            [
              create_srmg_heuristic_term/2,
              srmg/7, % srmg between 2 clauses (requires their signatures)
              srmg/6, % srmg between one clause and one example
              srmg/5  % srmg between two examples (constructs their bottom clauses)
            ]
         ).

% GILPS modules
:- use_module('../clause evaluation/common_clause_evaluation', [clause_examples_coverage/6]).
:- use_module('../utils/clause', [buildPredCall/4, skolemize/2]).
:- use_module('../settings/settings', [setting/2]).%because of 'srmg_heuristic'
:- use_module('bottom_clause', [sat/3]).

% YAP modules
:- use_module(library(lists), [nth/4, reverse/2]).
:- use_module(library(rbtrees), [rb_new/1, rb_lookup/3, rb_insert/4]).
:- use_module(library(apply_macros), [maplist/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_srmg_heuristic_term(+NegativeExampleIDs, -SRMG_Heuristic),
%
% Given:
%  NegativeExampleIDs: ordered list of negative example ids
%
% Returns:
%  SRMG_Heuristic: the heuristic term to use when computing srmgs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_srmg_heuristic_term(_, heuristic(first_match)):-
  setting(srmg_heuristic, first_match),!.

create_srmg_heuristic_term(NEIDs, heuristic(minimize_negative, NEIDs)):-
  setting(srmg_heuristic, minimize_negative),!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Type of important datastructures for constructing the lgg
%
%    Mapping: an rb_tree where the key is a triple (Type, Term1, Term2) and value is the variable
%             associated with this pair (Type is Term1 and Term2 type)
%             Term1 and Term2 are skolemized variables
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initial_mapping(-Mapping)
%
% Returns:
%   Mapping: initial Mapping
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initial_mapping(Mapping):-
  rb_new(Mapping).

%get_existing_mapping(+Mapping, +(Type, Term1, Term2), -Value)
get_existing_mapping(Mapping, (Type, Term1, Term2), Value):-
  rb_lookup(k(Type, Term1, Term2), Value, Mapping).

%create_new_mapping(+Mapping, +(Type, Term1, Term2), -Value, -NewMapping)
create_new_mapping(Mapping, (Type, Term1, Term2), Value, NewMapping):-
  rb_insert(Mapping, k(Type, Term1, Term2), Value, NewMapping).

/*
%Alternative mapping implementation with lists, the above is more efficient
initial_mapping([]).

get_existing_mapping([(Type, Term1A, Term2A, Value)|_], (Type, Term1B, Term2B), Value):-
  Term1A==Term1B,
  Term2A==Term2B,!.
get_existing_mapping([_|Map], (Type, Term1, Term2), Value):-
  get_existing_mapping(Map, (Type, Term1, Term2), Value).

create_new_mapping(Map, (Type, Term1, Term2), Value, [(Type, Term1, Term2, Value)|Map]).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% srmg(+Clause1, +ClauseSig1, +Clause2, +ClauseSig2, +Heuristic, -lgg, -lggSig)
%
% Given:
%   Clause1: a clause as a list of literals
%   Clause1Sig: Clause1 signature
%   Clause2: a clause as a list of literals
%   Clause2Sig: Clause2 signature
%   Heuristic: a term that can either be: heuristic(first_match) or
%                heuristic(minimize_negative, OrderedListOfNegativeExamples)
%
% Returns:
%   lgg: least general generalization of Clause1 and Clause2
%   lggSig: lgg signature
%
% Examples:
%
% srmg([a(5)],[a(#i)],[a(5)],[a(#i)], C, S).
%   C= [a(5)], S = [a(#i)] ? ;
%
% srmg([a(A),b(A,5)],[a(+i),b(+i,#i)],[a(B),b(B,5)],[a(+i),b(+i,#i)], C, S).
%   C = [a(_A),b(_A,5)],
%   S = [a(+i),b(+i,#i)] ?
%
% sat(p(d0),_C1,_S1),sat(p(d1),_C2,_S2),srmg(_C1,_C1,_C2,_S2,LGU,LGUS).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

srmg(Clause1, [HeadSig|Body1Sig], Clause2, [HeadSig|Body2Sig], Heuristic,
     [LGU_Head|LGU_Body], [HeadSig|LGU_BodySig]):-
  skolemize(Clause1, [Head1|Body1]),
  skolemize(Clause2, [Head2|Body2]),
  initial_mapping(Map0),
  lgu(Head1, Head2, HeadSig, head, Map0, LGU_Head, Map1),
  srmg_body(Body1, Body1Sig, Body2, Body2Sig, Map1, Heuristic, [LGU_Head], [HeadSig], LGU_Body, LGU_BodySig).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  srmg_body(+Body1, +Body1Sig, +Body2, +Body2Sig, +Map1, +Heuristic, +CurLGU, +CurLGUSig, 
%            -LGU_Body, -LGU_BodySig)
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

srmg_body([], [], _, _, _, _, _, _, [], []).
srmg_body([Atom|Atoms], [ASig|ASigs], Body, BodySig, CurMap, Heuristic, CL, CLS, [LGUB|Ls], [ASig|LBs]):-
  lgusForBodyAtom(Body, BodySig, Atom, ASig, CurMap, AllAtomLGUs),
  select_best_matching_lgu(Heuristic, AllAtomLGUs, ASig, CL, CLS, BestLGU, UHeuristic),!,
%  length(Atoms, StillToGo), format("Still ~w atoms to compute this srmg~n", [StillToGo]),
  BestLGU=(LGUB,Pos,NCurMap),
  nth(Pos, Body, _BodyAtom, NBody),
  nth(Pos, BodySig, _, NBodySig),
  %format("Atom ~w (pos: ~w) selected to match ~w~n", [_BodyAtom, Pos, Atom]),
  srmg_body(Atoms, ASigs, NBody, NBodySig, NCurMap, UHeuristic, [LGUB|CL], [ASig|CLS], Ls, LBs).
srmg_body([_|Atoms], [_|ASigs], Body, BodySig, CurMap, Heuristic, CL, CLS, LGU_Body, LGU_BodySig):-
  %Atom has no lgu in the other body
  srmg_body(Atoms, ASigs, Body, BodySig, CurMap, Heuristic, CL, CLS, LGU_Body, LGU_BodySig).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% select_best_matching_lgu(+Heuristic, +AllPossibleLGUs, +AllLGUSig, +CurLGU, +CurLGUSig,
%                         -BestMatchingLGU, -UpdatedHeuristic)
%
% Given:
%  Heuristic: see above srmg/6
%  AllPossibleLGUs: a list of all possible lgus where each element is a tuple: 
%    (LeastGeneralUnifier, Position in BodyAtoms, UpdatedMapping)
%  AllLGUSig: signature common to all LeastGeneralUnifiers in AllPossibleLGUs
%  CurLGU: a list of literals representing the current lgu (in reversed form!)
%  CurLGUSig: CurLGU signature  (in reversed form!)
%  NegativeExampleIDs: ordered list of negative example ids
%
% Returns:
%  BestMatchingLGU: the best matching lgu is a tuple: (LeastGeneralUnifier, Position in BodyAtoms, UpdatedMapping)
%    LeastGeneralUnifier is an atom
%  UpdatedHeuristic: the heuristic to use next turn (it's the same heuristic, this parameter is only
%                    needed because we want to pass an ordered list of the CoveredNegativeExamples,
%                    so that in the next turns, if heuristic is minimize_negative, we can do it more efficiently)
%
% Notes:
%  The best matching lgu is obtained by, from all the matching lgu, choosing the one that, when added
%  to the current lgu, covers the fewest negative examples weights.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%select_best_matching_lgu(+Heuristic, +AllPossibleLGUs, +CommonSig, +CurLGU, +CurLGUSig, -BMLGU, -UHeuristic):-
select_best_matching_lgu(heuristic(first_match), [BMLGU|_], _CSig, _C, _S, BMLGU, heuristic(first_match)).
select_best_matching_lgu(heuristic(minimize_negative, NEIDs), AllPLgus, ASig, CL, SL,%note that CL and SL are reversed
                         BMLGU, heuristic(minimize_negative, NNEIDs)):-
  length(AllPLgus, NumAllPLgus),
  NumAllPLgus>0,
  (NumAllPLgus=1 -> % there's only one choice, select it without computing negative coverage
     AllPLgus=[BMLGU],
     NNEIDs=NEIDs
   ;%NumAllPLgus>1
     reverse([ASig|SL], CSig), %C sig is now in proper format
    %CL still needs to have the head appended and reversed
     select_best_matching_lgu_mn(AllPLgus, NEIDs, CL, CSig, inf, _, _, NNEIDs, BMLGU)
  ).

%select_best_matching_lgu_mn(+AllPLgus, +NegativeEIDs, +CL, +ClauseSig, +CurBestNegWeightsCovered,
%                            +CurNegEIDsCovered, +CurBestMLGU, -FinalNegEIDsCovered, -FinalBestMLGU)

select_best_matching_lgu_mn([], _, _, _, _, NEIDs, BMLGU, NEIDs, BMLGU).
select_best_matching_lgu_mn([(LGUB,Pos,Map)|RL], NEIDs, CL, ClauseSig, CurBNWC,
                            _CurNegEIDsCovered, _CurBMLGU, FinalNegEIDsCov, BMLGU):-
  reverse([LGUB|CL], Clause), %ClauseSig has the signature for Clause
  clause_examples_coverage(NEIDs, Clause, ClauseSig, CurBNWC, NCurBNWC, NCurNegEIDsCovered),
  NCurBNWC<CurBNWC,!,% NCurBNWC may be equal to CurBNWC, in which case we prefer the former
  %format("Weight covered by atom pos ~w:~w~n", [Pos, NCurBNWC]),
  select_best_matching_lgu_mn(RL, NEIDs, CL, ClauseSig, NCurBNWC,
                              NCurNegEIDsCovered, (LGUB,Pos,Map), FinalNegEIDsCov, BMLGU).

select_best_matching_lgu_mn([_|RL], NEIDs, CL, ClauseSig, CurBNWC,
                            CurNegEIDsCovered, CurBMLGU, FinalNegEIDsCov, BMLGU):-
  % current LGU tuple is no better than the best so far
  select_best_matching_lgu_mn(RL, NEIDs, CL, ClauseSig, CurBNWC,
                              CurNegEIDsCovered, CurBMLGU, FinalNegEIDsCov, BMLGU).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% lgusForBodyAtom(+BodyAtoms, +BodyAtomsSig, +Atom, +AtomSig, +CurMapping, -LGUs)
%
% Given:
%  BodyAtoms: a list of atoms
%  BodyAtomsSig: signatures for each of BodyAtoms
%  Atom: an atom we want to compute its lgu
%  AtomSig: Atom signature
%  CurMapping: the current mapping of terms to variables
%
% Returns:
%  LGUs: a list where each element is a tuple: (LeastGeneralUnifier, Position in BodyAtoms, UpdatedMapping)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lgusForBodyAtom(BodyAtoms, BodyAtomsSig, Atom, AtomSig, CurMapping, LGUs):-
  lgusForBodyAtom(BodyAtoms, BodyAtomsSig, 1, Atom, AtomSig, CurMapping, LGUs).

lgusForBodyAtom([], [], _, _, _, _, []).
lgusForBodyAtom([A|As], [AtomSig|ASs], N, Atom, AtomSig, CM, [(LGU,N,FM)|LGUs]):-
  lgu(A, Atom, AtomSig, body, CM, LGU, FM),!,
  N1 is N+1,
  lgusForBodyAtom(As, ASs, N1, Atom, AtomSig, CM, LGUs).
lgusForBodyAtom([_|As], [_|ASs], N, Atom, AtomSig, CM, LGUs):-
  N1 is N+1,
  lgusForBodyAtom(As, ASs, N1, Atom, AtomSig, CM, LGUs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% lgu(+Atom1, +Atom2, +AtomSig, +LiteralFrom, +CurMapping, -LGU, -FinalMapping)
%
% Given:
%  Atom1: an atom
%  Atom2: another atom
%  AtomSig: signature that is shared by Atom1 and Atom2
%  LiteralFrom: where Atom1 and Atom2 comes from either 'head' or 'body'
%
% Returns:
%  lgu: least general unifier of Atom1 with Atom2
%       (it's signature is AtomSig)
%
% Notes:
%  The least general unifier must be mode compatible (that is, it's input variable must
%  already exist, except in the case of the head)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lgu(Atom1, Atom2, AtomSig, LiteralFrom, CurMap, LGU, FinalMap):-
  buildPredCall(AtomSig, Atom1Args, AtomIOTypes, Atom1),
  buildPredCall(AtomSig, Atom2Args, AtomIOTypes, Atom2),
  maplist(updateIO(LiteralFrom), AtomIOTypes, NAtomIOTypes),
  matchArgs(Atom1Args, Atom2Args, NAtomIOTypes, CurMap, ArgsUnifier, FinalMap),
  buildPredCall(AtomSig, ArgsUnifier, AtomIOTypes, LGU).

%updateIO(+LiteralFrom, +AtomIOType, -NewAtomIOType)
% head input atoms (+) are replaced by output (-) because otherwise matchArgs would fail to 
% find an existing unifier as the mapping is empty before processing head
updateIO(head, +T, -T):-!.
updateIO(_, IOT, IOT).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% matchArgs(+AA1, +AA2, +AIOT, +MappingDS, -ArgsGeneralizer, -NewMappingDS)
%
% Given:
%   AtomArgs1: atom1's terms (some/all may be variables). E.g. [A,5,B]
%   AtomArgs2: atom2's terms (some/all may be variables). 
%   AtomIOTypes: atom1's and atom2's io types. E.g. [+t,#i,-p]
%   MappingDS: mapping datastructure
%
% Returns:
%   ArgGeneralizer: a list of terms (variables or values) that generalize ATT1 with ATT2
%   NewMappingDS: new mapping datastructure
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%matchArgs(+AA1, +AA2, +AIOT, +MappingDS, -ArgsGeneralizer, -NewMappingDS):-
matchArgs([], [], [], Map, [], Map).
matchArgs([A1|A1s], [A2|A2s], [IOType|IOTs], CurMap, [AG|AGs], FMap):-
  matchTerm(IOType, A1, A2, CurMap, AG, NCurMap),
  matchArgs(A1s, A2s, IOTs, NCurMap, AGs, FMap).

%matchTerm(+IOType, +A1, +A2, +CurMapping, -Generalizer, -NewMapping)
matchTerm(+Type, A1, A2, CurMapping, Generalizer, CurMapping):-
  !, % if the IO Mode is + then the variable to add must already exist
  get_existing_mapping(CurMapping, (Type, A1, A2), Generalizer). % unifier already exists

matchTerm(#_, A1, A2, Mapping, A1, Mapping):-
  !, % if the IO Mode is # the constants must be the same, otherwise the unifier signature
     % wouldn't be equal
  A1=A2. % we don't need to update the mapping

matchTerm(-Type, A1, A2, CurMapping, Generalizer, CurMapping):-
  get_existing_mapping(CurMapping, (Type, A1, A2), Generalizer),!. % unifier already exists

% unifier does not exist, create it
matchTerm(-Type, A1, A2, Mapping, Generalizer, NewMapping):-
  %case where the terms are two distinct constants or variables (no matter if equal)
  create_new_mapping(Mapping, (Type, A1, A2), Generalizer, NewMapping).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% srmg(+Example1, +Example2, +Heuristic, -lgg, -lggSig)
% srmg(+Clause, +ClauseSig, +Example, +Heuristic, -SRMG, -SRMGSig)
%
% Given:
%
%  Heuristic: either heuristic(first_match) or heuristic(minimize_negative, NegEIDs)
%
% These are variations from the above srmg/6
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

srmg(Example1, Example2, Heuristic, SRMG, SRMGSig):-
  sat(Example1, Bottom_Example1, Bottom_Example1Sig),
  srmg(Bottom_Example1, Bottom_Example1Sig, Example2, Heuristic, SRMG, SRMGSig).

srmg(Clause, ClauseSig, Example, Heuristic, SRMG, SRMGSig):-
  sat(Example, Bottom_Example, Bottom_ExampleSig),
  srmg(Clause, ClauseSig, Bottom_Example, Bottom_ExampleSig, Heuristic, SRMG, SRMGSig).
