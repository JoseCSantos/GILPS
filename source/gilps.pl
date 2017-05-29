%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                                      %
% Author: Jose Santos <jcas81@gmail.com>                                               %
% Date: 2009-03-13                                                                     %
%                                                                                      %
% GILPS: General Inductive Logic Programming System                                    %
%                                                                                      %
%      It implements several ILP algorithms:                                           %
%            TopLog                                                                    %
%            FuncLog                                                                   %
%            ProGolem                                                                  %
%            ProGol   (to do)                                                          %
%                                                                                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(gilps,
            [
             %GILPS
              read_problem/1,

             %settings
              set/2,
              setting/2,
              show_settings/0,

             % mode_definitions
              modeh/1,
              modeh/2,
              modeb/2,
              modeb/3,

             % TopLog hypothesis generator (likely to remove later)
              hyp/2,
              prove/3,

             % bottom clause generator
              sat/1,
              sat/2,
              sat/3,
              ground_sat/1,
              ground_sat/2,

             % build theory using the currently selected ILP engine
              build_theory/0,
              build_theory/1,

             % evaluates a previously constructed theory from file
              evaluate_theory/1,
              evaluate_theory/2,

             % common to all engines
             % this is different than above, the file contains all hypotheses with 
             % their coverage but no theory constructed yet, rename this later
              computeTheoryFromFile/1
            ]
         ).

% These prolog flags detect errors in GILP code
:- set_prolog_flag(single_var_warnings, on).
:- set_prolog_flag(unknown, warning).

% GILPS modules
:- use_module('settings/settings', [set/2, setting/2, show_settings/0]).
:- use_module('mode declarations/mode_declarations', [modeh/1, modeh/2, modeb/2, modeb/3, initModeDeclarations/0]).
:- use_module('top_theory/hypothesis_generator', [hyp/2, prove/3]). %likely to remove later
:- use_module('engine/common', [computeTheoryFromFile/1]). % not being used, use later
:- use_module('engine/toplog', [runTopLog/1]).
:- use_module('engine/funclog', [runFuncLog/1]).
:- use_module('engine/progolem', [runProgolem/1]).
:- use_module('bottom clause/bottom_clause', [sat/1, sat/2, sat/3, ground_sat/1, ground_sat/2]).
:- use_module('examples/examples', [processExamples/2, exampleIDs/2, erase_examples/1]).
:- use_module('theory/theory_constructor', [clauses_to_theory/4]).
:- use_module('theory/theory', [showTheory/4]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  read_problem(+File)
%
%  Given:
%    File: can be either a file or a list of files to load. Typically is a single file
%
%  Succeeds:
%    Loads file in user space and, importantly, adds call counting to these user files.
%    Consulting the files with call_counting enabled allows to limit the number of
%    resolutions allowed in proofs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

read_problem(LF):-
% When we load and run user code we want to disable warnings because constructed clauses may
% create and call predicates that don't exist. Also, if the user code has singletons, it's a
% bit ugly to see those warnings when loading the file inside GILPS
  set_prolog_flag(single_var_warnings, off), % for GILPS debugging it may be useful
  set_prolog_flag(unknown, fail),                  % to temporarly comment these two set_prolog_flag
  yap_flag(discontiguous_warnings, off),      % disable discontiguous warnings in user files
  yap_flag(call_counting, on),
  consult(user:LF),
  yap_flag(call_counting, off),
  initModeDeclarations,
  processExamples(_, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% build_theory/0
% build_theory(+FileName)
%
% Runs the ILP system using the currently selected engine. If FileName is given, the
% hypotheses generated are saved onto it
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

build_theory:-
  build_theory(_).%if FileName is a variables it's ignored
build_theory(FileName):-
  setting(engine, toplog), !,
  runTopLog(FileName).
build_theory(FileName):-
  setting(engine, funclog), !,
  runFuncLog(FileName).
build_theory(FileName):-
  setting(engine, progolem), !,
  runProgolem(FileName).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% evaluate_theory(+TheoryFileName)
% evaluate_theory(+TheoryFileName, +ExamplesFileName)
%
% Both predicates evaluate the theory from file FileName.
% The first evaluates it on all the examples loaded. The second evaluates it only
% on the examples given in file ExamplesFileName
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic user:theory_clause/2. % this to avoid an error in case the TheoryFileName
                                 % has no theory_clause/2 facts

evaluate_theory(TheoryFileName):-
  exampleIDs(PosEIDs, NegEIDs),
  evaluate_theory_aux(TheoryFileName, PosEIDs, NegEIDs).

evaluate_theory(TheoryFileName, ExamplesFileName):-
  consult(user:ExamplesFileName),
  processExamples(PosEIDs, NegEIDs),
  evaluate_theory_aux(TheoryFileName, PosEIDs, NegEIDs),
  erase_examples(PosEIDs), % it's not good practice to load the examples and remove them
  erase_examples(NegEIDs), %afterwards...
  retractall(theory_clause(_, _)). % remove the theory_clause/2 terms

%evaluate_theory_aux(+TheoryFileName, +PosEIDs, +NegEIDs)
evaluate_theory_aux(TheoryFileName, PosEIDs, NegEIDs):-
  consult(user:TheoryFileName), % load theory_clause/2 terms from TheoryFile
  findall((Clause, ClauseSig), user:theory_clause(Clause, ClauseSig), Clauses),
  clauses_to_theory(Clauses, PosEIDs, NegEIDs, Theory),
  showTheory(Theory, PosEIDs, NegEIDs, -1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% welcome/0
%
% Displays welcome screen
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

welcome:-
  format("GILPS: General Inductive Logic Programming System~2n", []),
  gilps_version(Version),
  gilps_version_date(VersionDate),
  gilps_webpage(WebPage),
  format("Version: ~w~nDate: ~w~nAuthor: Jose Santos~n", [Version, VersionDate]),
  format("For more information please check: ~w~2n", [WebPage]).

gilps_version('0.15').
gilps_version_date('15th March 2010').
gilps_webpage('http://www.doc.ic.ac.uk/~jcs06').

:- welcome.
