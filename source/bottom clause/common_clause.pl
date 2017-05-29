%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-03-13
%
%  This file contains predicates to find a common clause between examples.
%  This is currently only being used for tests
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(common_clause,
            [
              shortestCommonClause/4,
              shortestCommonClause/6,
              commonClause/4,
              commonClauseForExamples/3,
              computeLGGUpperBoundSize/3
            ]
         ).

% GILPS modules
:- use_module('bottom_clause', [sat/3]).
:- use_module('clause_reduce', [positiveClauseReduce/6]).
:- use_module('../utils/clause', [signature2PredArity/2]).
:- use_module('../examples/examples', [id2example/2]).

% YAP modules
:- use_module(library(rbtrees), [rb_new/1, rb_lookup/3, rb_insert/4, rb_update/4, rb_visit/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% shortestCommonClause(+Example1, +Example2, -CommonClause, -CommonClauseSignature)
%
% Given:
%   Example1: an example
%   Example2: another example
%
% Returns:
%   CommonClause: the shortest common clause between Example1 and Example2
%   CommonClauseSignature: list of signatures for CommonClause
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

shortestCommonClause(Example1, Example2, CommonClause, CommonClauseSignature):-
  sat(Example1, BottomClause1, BottomClauseSignature1),
  shortestCommonClause(Example1, BottomClause1, BottomClauseSignature1, Example2, CommonClause, CommonClauseSignature).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% shortestCommonClause(+Example1, +BottomClause, +BottomClauseSignature, +Example, -CommonClause, -CommonClauseSignature)
%
% Given:
%   Example1: an example
%   BottomClause1: the bottom clause for Example1
%   BottomClauseSignature: signature for BottomClause1
%   Example2: another example
%
% Returns:
%   CommonClause: the shortest common clause between Example1 and Example2
%   CommonClauseSignature: signature for CommonClause
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

shortestCommonClause(Example1, BottomClause1, BottomClauseSignature1, Example2, CommonClause, CommonClauseSignature):-
  sat(Example2, BottomClause2, BottomClauseSignature2),
  length(BottomClause1, Len1),
  length(BottomClause2, Len2),
  (Len1=<Len2->
    positiveClauseReduce(BottomClause1, BottomClauseSignature1, Example2, _FailProfile, CommonClause, CommonClauseSignature)
   ;
    positiveClauseReduce(BottomClause2, BottomClauseSignature2, Example1, _FailProfile, CommonClause, CommonClauseSignature)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% commonClause(+Example1, +Example2, -CommonClause, -CommonClauseSignature)
%
% Notes:
%   commonClause(E1, E2) is in general different than commonClause(E2,E1)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

commonClause(Example1, Example2, CommonClause, CommonClauseSignature):-
  commonClauseForExamples([Example1, Example2], CommonClause, CommonClauseSignature).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% commonClauseForExamples(+ExampleIDs, -CommonClause, -CommonClauseSignature)
%
% Given:
%   ExampleIDs: a list of example ids
%
% Returns:
%   CommonClause: the clause common to all Examples
%   CommonClauseSignature: CommonClause's signature
%
% Notes:
%   The order of the examples changes the common clause
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%commonClauseForExamples(+ExampleIDs, +CommonClause, +CommonClauseSignature, -FinalCommonClause, -FinalCommonClauseSignature).
commonClauseForExamples([], CC, CCS, CC, CCS).
commonClauseForExamples([Ex|Exs], CC, CCS, FCC, FCCS):-
  positiveClauseReduce(CC, CCS, Ex, _FailProfile, NCC, NCCS),
  commonClauseForExamples(Exs, NCC, NCCS, FCC, FCCS).

commonClauseForExamples([SeedExID|Exs], CC, FCS):-
  id2example(SeedExID, SeedEx),
  sat(SeedEx, BC, BCS),
%  format("Bottom clause for ~w:~n", [SeedEx]),
%  utils_clauses:prettyPrintLiterals(BC, 4),
  commonClauseForExamples(Exs, BC, BCS, CC, FCS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% computeLGGUpperBoundSize(+Example1, +Example2, -UpperBoundSize)
%
% Given:
%   Example1: an example
%   Example2: another example
%
% Returns:
%   UpperBoundSize: an integer, an upperbound on the size of the lgg between the two examples
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeLGGUpperBoundSize(Example1, Example2, UpperBoundSize):-
  sat(Example1, _Bottom1, BottomSig1),
  sat(Example2, _Bottom2, BottomSig2),
  computeLGGUpperBoundSizeSigs(BottomSig1, BottomSig2, UpperBoundSize).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% computeLGGUpperBoundSizeSigs(+ClauseSignature1, +ClauseSignature2, -UpperBoundSize)
%
% Given:
%   ClauseSignature1: a signature of a clause
%   ClauseSignature2: a signature of another clause
%
% Returns:
%   UpperBoundSize: an integer, an upperbound on the size of the lgg between clauses which have the
%                   given signatures
%
% Notes:
%   To compute this size we compute the predicate/Arity for each of the signatures and multiply together
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeLGGUpperBoundSizeSigs([HeadSig1|_], [HeadSig2|_], 0):-
  signature2PredArity(HeadSig1, PredArity1),
  signature2PredArity(HeadSig2, PredArity2),
  PredArity1\=PredArity2,!. % if different heads than lgg size is 0

computeLGGUpperBoundSizeSigs([_|BodySig1], [_|BodySig2], UpperBoundSize):-
  computePredNameArities(BodySig1, PredArities1),
  computePredNameArities(BodySig2, PredArities2),
  rb_visit(PredArities1, PredArities1List),
  write(PredArities1List),nl,
  rb_visit(PredArities2, PredArities2List),
  write(PredArities2List),nl,
  multiplyPredNameArities(PredArities1List, PredArities2, 1, UpperBoundSize). %1 to count the head

% multiplyPredNameArities(+PredArities1List, +PredArities2RBTree, +CurProduct, -UpperBoundSize)

multiplyPredNameArities([], _, Result, Result).
multiplyPredNameArities([PredArity-Count1|List], PredAritiesRBT, CurProduct, UpperBoundSize):-
  (rb_lookup(PredArity, Count2, PredAritiesRBT) ->
     NCurProduct is CurProduct + Count1*Count2
   ;
     NCurProduct=CurProduct
  ),
  multiplyPredNameArities(List, PredAritiesRBT, NCurProduct, UpperBoundSize).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% computePredNameArities(+Signatures, -PredAritiesRBTree):
%
% Given:
%   Signatures: a list of signatures
%
% Returns:
%   PredAritiesList: a rb_tree with PredName/Arity as key, NumOccurences as value
%
% E.g.
%  computePredNameArities([a(+b,-c),a(+d,-e),b(+g)], R), rb_visit(R, L), L=[a/2-2, b/1-1]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% computePredNameArities(+Signatures, -PredAritiesRBTree)

computePredNameArities(Signatures, PredAritiesRBTree):-
  rb_new(RBTree),
  computePredNameArities(Signatures, RBTree, PredAritiesRBTree).

% computePredNameArities(+Signatures, +CurRBTree, -FinalRBTree)

computePredNameArities([], RBTree, RBTree).
computePredNameArities([Sig|Sigs], CurRBTree, FRBTree):-
  signature2PredArity(Sig, PredArity),
  (rb_lookup(PredArity, Count, CurRBTree) ->
    Count1 is Count+1, % already exists
    rb_update(CurRBTree, PredArity, Count1, NextRBTree)
   ;
    %does not exist, create
    rb_insert(CurRBTree, PredArity, 1, NextRBTree)
  ),
  computePredNameArities(Sigs, NextRBTree, FRBTree).
