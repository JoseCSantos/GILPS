%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-04-24
%
%   This file has predicates common to several engines (TopLog and FuncLog for now)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(common,
           [
             generate_global_HypothesesAndTheory/2,
             generate_incremental_HypothesesAndTheory/1,
             computeTheoryFromFile/1,
             generate_best_hypothesis/6
           ]
         ).

% GILPS modules
:- use_module('../hypotheses/hypotheses', [compute_hypotheses/5, compute_coverage/4]).
:- use_module('../utils/files', [load_term/2, save_term/2]).
:- use_module('../utils/list', [numbersList/3]).
:- use_module('../settings/settings', [setting/2, set/2]).
:- use_module('../theory/theories', [createTheories/2, showTheories/3]).
:- use_module('../theory/theory_constructor', [construct_incremental_theory/7, highestScoringHypothesis/4]).
:- use_module('../theory/theory', [showTheory/4, output_theory2file/1]).
:- use_module('../examples/examples', [load_examples_term/1, save_examples_term/1, exampleIDs/2, foldSeparate/4]).
:- use_module('../messages/messages', [message/2]).

% YAP modules
:- use_module(library(apply_macros), [maplist/3]).
:- use_module(library(lists), [append/3, reverse/2, member/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% generateGlobalHypothesesAndTheory(+HypGenPred, +FileName)
%
% Given:
%   HypGenPred: predicate to generate hypotheses from an example. It has 3 arguments:
%               +Example, +MaxHypsPerExample, -Hypotheses  (in clause form)
%   FileName: the filename to store the generated hypotheses and their coverages.
%             If filename is a variable it's ignored
%
% Displays the outcome of running the ILP system with the currently selected ILP engine to standard output
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate generate_global_HypothesesAndTheory(:, ?).

generate_global_HypothesesAndTheory(HypGenPred, FileName):-
  setting(theory_construction, global), !, % just to make sure this has been properly called
  exampleIDs(PosExampleIDs, NegExampleIDs),
  compute_hypotheses(PosExampleIDs, PosExampleIDs, NegExampleIDs, HypGenPred, Hypotheses), %compute hypotheses
  compute_coverage(Hypotheses, PosExampleIDs, NegExampleIDs, HypothesesCoverage), %compute coverages
  save_session(FileName, [HypothesesCoverage, PosExampleIDs, NegExampleIDs]),
  buildAndShowTheory(HypothesesCoverage, PosExampleIDs, NegExampleIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% generate_incremental_hypothesesAndTheory(+HypGenPred)
%
% Given:
%   HypGenPred: predicate to generate hypotheses from a set of positive and negative examples. It has 3 arguments:
%               +PosExampleIDs, +NegExampleIDs, -Hypotheses  (in clause form)
%
% Displays the outcome of running the ILP system with the currently selected ILP engine to standard output
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate generate_incremental_HypothesesAndTheory(:).

generate_incremental_HypothesesAndTheory(HypGenPred):- % in incremental mode the FileName is ignored
  setting(theory_construction, incremental), !,  % just to make sure this has been properly called
  setting(cross_validation_folds, NumFolds),
  (NumFolds=1->StartNum=1;StartNum=0),
  numbersList(StartNum, NumFolds, Folds),
  exampleIDs(PosEIDs, NegEIDs),
  % this findall performs the cross-validation for incremental theores
  findall(Theory,
          (member(TestFold, Folds),
           %TestFold>0,
           foldSeparate(PosEIDs, TestFold, _TestPosEIDs, TrainPosEIDs),
           foldSeparate(NegEIDs, TestFold, _TestNegEIDs, TrainNegEIDs),
           construct_incremental_theory(TrainPosEIDs, TrainNegEIDs, PosEIDs, NegEIDs, HypGenPred, TestFold, Theory),
           (NumFolds=1 -> output_theory2file(Theory) ; true),
           message(theory_constructed, [TestFold, NumFolds])
          ),
          Theories),
  showTheories(Theories, PosEIDs, NegEIDs),
  message(program_stats, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% generate_best_hypothesis(+HypGenPred, +PosEID, +PosExIDs, +NegExIDs, +TestFold, -HypothesisInfo)
%
% Given:
%  PosExampleID: positive example id to generate hypothesis from
%  PosExampleIDs: positive example ids to test for coverage
%  NegExampleIDs: negative example ids to test for coverage
%  TestFold: test fold
%
% Returns:
%   HypothesisInfo: tuple (Hypothesis, NumLiterals, PosIDsCov, NegIDsCov), Hypothesis in clause form
%
% Notes:
%   Generates the best possible hypothesis, given a set of positive and negative example ids, and
%   HypGenPred. This is shared in common by TopLog and FuncLog
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate generate_best_hypothesis(:, ?, ?, ?, ?, ?).

generate_best_hypothesis(HypGenPred, PosEID, PosEIDs, NegEIDs, _TestFold, BestHypothesis):- % review later for TestFold
  setting(verbose, Verbosity), set(verbose, -1), %save verbosity, and set it to -1 so nothing is reported
  compute_hypotheses([PosEID], PosEIDs, NegEIDs, HypGenPred, Hypotheses), %compute hypotheses
  compute_coverage(Hypotheses, PosEIDs, NegEIDs, HypothesesCoverage), %compute hypotheses coverages
  set(verbose, Verbosity), % review this, it's awful changing verbosity this way
  maplist(processHypothesis, HypothesesCoverage, HypothesesCoverage1),
  %format("HypCoverage DS=~w~n", [HypothesesCoverage]),nl,halt,
  highestScoringHypothesis(HypothesesCoverage1, PosEIDs, NegEIDs, BestHypothesis).

% processHypothesis(+HypInfo, -(Hypothesis, HypSig, NumLiterals, CoveredPosIDs, CoveredNegIDs))

processHypothesis((Hypothesis, HypSig, NumLiterals, _ListExGen, CoveredPosIDs, CoveredNegIDs),
                  (Hypothesis, HypSig, NumLiterals, CoveredPosIDs, CoveredNegIDs)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% computeTheoryFromFile(+FileName)
%
% Given:
%   FileName: the filename where hypotheses, coverages and examples are stored
%
% Builds the theory from the hypotheses stored in file FileName and displays it to the stdout
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeTheoryFromFile(FileName):-
  load_session(FileName, [HypTotInfo, PosExampleIDs, NegExampleIDs]),
  % we have to prune hypotheses from hyptotinfo that do not meet the constraints
  buildAndShowTheory(HypTotInfo, PosExampleIDs, NegExampleIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% buildAndShowTheory(+Hypotheses, +PosExampleIDs, +NegExampleIDs)
%
% Given:
%   Filename: the filename to save the rb_tree
%   Hypotheses: list of hypotheses info (term with hypotheses and coverages, see createTheories/2)
%   PosExampleIDs: ordered list of positive example ids used to generate the hypotheses and test coverage
%   NegExampleIDs: ordered list of negative example ids used to test coverage
%
% Notes:
%   Constructs the theory and shows it to the stdout
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

buildAndShowTheory(Hypotheses, PosExampleIDs, NegExampleIDs):-
  createTheories(Hypotheses, Theories),
  Theories=[AllDataTheory|_],
  output_theory2file(AllDataTheory),
  showTheories(Theories, PosExampleIDs, NegExampleIDs),
  message(program_stats, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% save_session(+Filename, +[HypTotInfo, PosExampleIDs, NegExampleIDs])
%
% Given:
%   Filename: the filename to save the rb_tree
%   HypTotInfo: list of hypotheses info (term with hypotheses and coverages, see createTheories/2)
%   PosExampleIDs: ordered list of positive example ids used to generate the hypotheses and test coverage
%   NegExampleIDs: ordered list of negative example ids used to test coverage
%
% Notes:
%   We also need to store the actual examples (mainly because of the weights)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

save_session(FileName, _):-
  var(FileName), !. %if it's a variable do not save
save_session(FileName, Term):-
  save_examples_term(Examples),
  save_term(FileName, [Examples|Term]),
  message(session_saved, [FileName]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% load_session(+Filename, -[HypTotInfo, PosExampleIDs, NegExampleIDs])
%
% Given:
%   Filename: the filename to save the rb_tree
%   HypTotInfo: RB tree with hypotheses and coverages
%   PosExampleIDs: ordered list of positive example ids used to generate the hypotheses and test coverage
%   NegExampleIDs: ordered list of negative example ids used to test coverage
%
% Notes:
%   We also need to load the actual examples
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_session(FileName, [HypTotInfo, PosExampleIDs, NegExampleIDs]):-
  load_term(FileName, [Examples, HypTotInfo, PosExampleIDs, NegExampleIDs]),
  load_examples_term(Examples),
  message(session_loaded, [FileName]).
