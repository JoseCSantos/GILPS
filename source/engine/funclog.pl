%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-04-24
%
%   This file has predicates to generate a theory in FuncLog way
%
%   FuncLog (for Functions in Logic) can only be used if there is at least one output
%   variable in the head of the clause.
%
%   algorithm funcLog(+Examples, -ReducedClause)
%     1. Let Clauses = empty list
%     2. for each positive example, Pe, in Examples do
%     3.   Let Peb = bottom clause for Pe
%     4.   Let HVar = Unique head output variables from Peb
%     5.   Let LastAtoms = atoms from Peb where one of their output variables is
%                          a subset of HVars
%     6.   for each atom, a, in LastAtoms do
%     7.      Clauses = Clauses U {Support Set of A in Peb}
%     8.   end for
%     9. end for
%    10. Perform greedy search over all clauses in Clauses
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(engine_funclog,
           [
             runFuncLog/1
           ]
         ).

% GILPS modules
:- use_module('common', [generate_global_HypothesesAndTheory/2, generate_incremental_HypothesesAndTheory/1, generate_best_hypothesis/6]).
:- use_module('../bottom clause/bottom_clause', [sat/3]).
:- use_module('../bottom clause/clause_reduce', [reduceToHeadOutputVars/4]).
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [id2example/2]).

% YAP modules
:- use_module(library(apply_macros), [maplist/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% runFuncLog(+FileName)
%
% Given:
%   FileName: the filename to store the generated hypotheses and their coverages. If it's a variable it's ignored
%
% Displays the outcome of running funclog in standard output, possibly saving the hypotheses (but not the theory)
% in FileName
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

runFuncLog(FileName):-
  (setting(theory_construction, global) ->
    generate_global_HypothesesAndTheory(genHypFromExample_global, FileName)
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
%   Hypotheses: a list of hypotheses as a list of literals
%
% Notes:
%   This is the main distinguisher between ILP systems: the way hypotheses are generated
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_global(ExampleID, _TPosEIDs, _APosEIDs, _ANegEIDs, MaxHypothesesPerExample, Hypotheses):-
  id2example(ExampleID, Example),
  %format("Computing bottom clause for example ~w...", [Example]),
  sat(Example, Bottom, BottomSig),
  %format("Computed!~n", []),
  reduceToHeadOutputVars(Bottom, BottomSig, MaxHypothesesPerExample, TReducedClauses),
  %length(TReducedClauses, N), format("~w hypotheses reduced from it~n", [N]),
% TReducedClauses has clauses represented as a list of literals and has their signatures
  maplist(reducedClauseToHypothesis, TReducedClauses, Hypotheses).

%reducedClauseToHypothesis(+(ReducedClauseAsLiterals, ReducedClauseSignature), -Hypothesis)
reducedClauseToHypothesis((ReducedClauseAsLiterals, _), ReducedClauseAsLiterals).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% genHypFromExample_incremental(+TPosEIDs, +TNegEIDs, +APosEIDs, +ANegEIDs, +TestFold, -BestHypothesis)
%
% Given:
%  TPosEIDs: ordered list of train positive examples id to generate best hypothesis from
%  TNegEIDs: ordered list of train negative examples id to generate best hypothesis from
%  APosEIDs: ordered list of all positive example ids of the current fold not yet entailed
%            (i.e. TPosEIDs plus the positive examples where one couldn't find compressive clauses)
%  TestFold: test fold
%
% Returns:
%   BestHypothesis: a tuple of the form (Score, Hypothesis, NumLiterals, PosIDsCov, NegIDsCov)
%                   (Hypothesis as a list of literals)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_incremental([TPosEID|_TPosEIDs], TNegEIDs, APosEIDs, TestFold, BestHypothesis):-
  generate_best_hypothesis(genHypFromExample_global, TPosEID, APosEIDs, TNegEIDs, TestFold, BestHypothesis).
