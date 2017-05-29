%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-04-24
%
%   This file has predicates to run TopLog
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(engine_toplog,
           [
             runTopLog/1
           ]
         ).

% GILPS modules
:- use_module('common', [generate_global_HypothesesAndTheory/2, generate_incremental_HypothesesAndTheory/1, generate_best_hypothesis/6]).
:- use_module('../top_theory/hypothesis_generator', [hyp/2]).
:- use_module('../top_theory/compiler', [compile/0, compiled/0]).
:- use_module('../utils/goal_solutions', [collect_solutions/4]).
:- use_module('../settings/settings', [setting/2]).
:- use_module('../examples/examples', [id2example/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% prepare_execution
%
% Notes:
%  This compiles the top_theory, which is needed for TopLog
%  Note that after processing the examples, any changes to the number of folds could be problematic as the folds
%  IDs won't be updated. We can fix this issue later (or ignore it, since it's not very serious)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prepare_execution:-
  compiled,!. % if the Top Theory is already compiled, prepare_execution suceeds (to avoid double compilation)
prepare_execution:-
  compile.    % compiles the top_theory

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% runTopLog(+FileName)
%
% Given:
%   FileName: the filename to store the generated hypotheses and their coverages. If it's a variable it's ignored
%
% Displays the outcome of running toplog in standard output, possibly saving the hypotheses (but not the theory)
% in FileName
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

runTopLog(FileName):-
  prepare_execution,
  (setting(theory_construction, global) ->
    generate_global_HypothesesAndTheory(genHypFromExample_global, FileName)
   ;
  %setting(theory_construction, incremental)
    generate_incremental_HypothesesAndTheory(genHypFromExample_incremental)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% genHypFromExample_global(+Example, +TPosEIDs, +APosEIDs, +ANegEIDs, +MaxHypothesesPerExample, -Hypotheses)
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
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_global(ExampleID, _TPosEIDs, _APosEIDs, _ANegEIDs, MaxHypothesesPerExample, Hypotheses):-
  id2example(ExampleID, Example),
  collect_solutions((Hyp, _HypSig), hyp(Example, Hyp), MaxHypothesesPerExample, Hypotheses). %free hyp sig

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% genHypFromExample_incremental(+TPosEIDs, +TNegEIDs, +APosEIDs, +ANegEIDs, +TestFold, -BestHypothesis)
%
% Given:
%  TPosEIDs: ordered list of train positive examples id to generate best hypothesis from
%  TNegEIDs: ordered list of train negative examples id to test hypothesis on
%  APosEIDs: ordered list of all positive example ids of the current fold not yet entailed
%            (i.e. TPosEIDs plus the positive examples where one couldn't find compressive clauses)
%  TestFold: test fold
%
% Returns:
%   BestHypothesis: a tuple of the form (Score, Hypothesis, HypSig, NumLiterals, PosIDsCov, NegIDsCov)
%                   (Hypothesis as a list of literals)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

genHypFromExample_incremental([TPosEID|_TPosEIDs], TNegEIDs, APosEIDs, TestFold, BestHypothesis):-
  generate_best_hypothesis(genHypFromExample_global, TPosEID, APosEIDs, TNegEIDs, TestFold, BestHypothesis).
