%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-01-27
%
% This file contains the Top Theory compiler
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(top_theory_compiler,
           [
             compile/0,
             compiled/0
           ]
         ).

% GILPS modules
:- use_module('../utils/clause', [signatureIOVars/4, buildPredCall/4]).
:- use_module('../mode declarations/mode_declarations', [mode_head/1, modebDecls/1]).

% YAP modules
:- use_module(library(lists), [append/3]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% bindInputVariablesTerms(+TypedInputVariables, +InTerms, -TermList)
%
% TypedInputVariables is a list of value/type
%
% This predicate generates the part of the atom predicate of the Top Theory that is
% responsible for binding the input variables of the term.
%
% Notice that by using member/2 we are doing the equivalent of 'vars_rep' in TopLog
% which is the most general setting. It would probably be better to use 'no_vars_rep'
% and have support for 'commutative'
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bindInputVariablesTerms([], _, []).
bindInputVariablesTerms([TypedVar|TVars], InTerms, [call_randomMember(TypedVar, InTerms)|Terms]):-
  bindInputVariablesTerms(TVars, InTerms, Terms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% modeb2theory(+ModeBodyDeclaration, -Head, -Body)
%
% Given:
%  ModeBodyDeclaration: (e.g. modeb(1, sum(+int, +int, -int), commutative)
%
% Returns:
%   Head and Body: the atom that is constructed for the Top Theory
%
% E.g. modeb2theory(modeb(1, sum(+int, +int, -int)), Head, Body).
%
% Notes:
%   The structure of a ModeBodyDeclaration is modeb(Recall, Signature, PredInfo)
%   PredInfo is being ignored. We should update this code to deal with the commutative case
%   Body will have a call_modeb/3 term. Its structure is: call_modeb(Recall, Signature, PredCall)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


modeb2theory(modeb(Recall, Signature, _PredInfo), Head, Body):-
  signatureIOVars(Signature, AllVars, TypedInputVars, TypedOutputVars),
  bindInputVariablesTerms(TypedInputVars, InTerms, BindInVarsTerms), %InTerms is a variable appearing in top_theory atom head
  buildPredCall(Signature, AllVars, _Types, PredCall),
  (Signature=not(_)-> % if it is negated: ensure output variables are not binded to input as they will be uninstatiated
     Head = atom(InTerms, OutTerms, InTerms, OutTerms),
     append(BindInVarsTerms,
            [call_modeb(Recall, Signature, PredCall)], % 3 arguments: Recall, Signature, PredToBeCalled
            Body)
   ;% normal case
     Head = atom(InTerms, OutTerms, NInTerms, NOutTerms),
     append(BindInVarsTerms,
            [call_modeb(Recall, Signature, PredCall), % 3 arguments: Recall, Signature, PredToBeCalled
             mergeTerms(TypedOutputVars, InTerms, OutTerms, NInTerms, NOutTerms)], % bind output variables to interms or outterms
             Body)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% modeh2theory(+ModeHDeclaration, -Head, -Body)
%
% Given a ModeHDeclaration (e.g. modeh(sum(+int, +int, -int))
%   returns in Head and Body the Head and Body that are constructed for the Top Theory
%
% modeh2theory(modeh(sum(+int, +int, -int)), Head, Body)
%
% call_modeh has 2 arguments: Signature and Predicate call
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

modeh2theory(modeh(Signature), call_modeh(Signature, PredCall), Body):-
  signatureIOVars(Signature, AllVars, InTermsHead, OutTermsHead),
  buildPredCall(Signature, AllVars, _Types, PredCall),
  Body=
       [
         mergeTerms(InTermsHead, [], OutTermsHead, NInTerms, NOutTerms), %InTermsHead and OutTermsHead were taken from the modeh
         body(NInTerms, NOutTerms)
       ].

%%%%% in the interpreter, at 'call_modeb' we need to ensure the newly added literal doesn't match an already
%%%%%     existing literal in the body.
%%%%%
%%%%% In order to do that we have to abstract the terms and rename the variables starting from 1...
%%%%%         * we aren't outputing an already existing literal


% add2TopTheory(+Number, +Head, +Body)

add2TopTheory(Number, Head, Body):-
  assertz(top_theory:theory(Number, Head, Body)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compile_modes(+mode declarations)
%
% mode declarations is a non empty list of mode declarations. It contains exactly one modeh declaration
% (first element of the list) followed by several (or none) modeb declarations
%
% by succeeding we are compiling the mode declarations to the top theory. This means asserting the
% missing start clause and atom definitions in it
%
% E.g. compile_modes([modeh(class(+animal,#animal)),modeb(1,has_milk(+animal))]).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compile_modes([ModeHDecl|ModeBDecls]):-
  modeh2theory(ModeHDecl, Head, Body),
  add2TopTheory(1, Head, Body),
  compileModeBDecls(100, ModeBDecls).

% compileModeBDecls(+CurrentTopTheoryClauseID, +ListOfModeBDeclsToCompile).

compileModeBDecls(_, []).
compileModeBDecls(N, [ModeBDecl|ModeBDecls]):-
  modeb2theory(ModeBDecl, Head, Body),
  add2TopTheory(N, Head, Body),
  N1 is N+1,
  compileModeBDecls(N1, ModeBDecls).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compile/0
%
% compile the mode declarations to the top theory.
%
% Notice that we are assuming the mode declarations are facts in the user module.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compile:-
  mode_head(ModeHDecl),!,% just get the first modeh
  modebDecls(ModeBDecls),
  compile_modes([modeh(ModeHDecl)|ModeBDecls]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compiled/0
%
% Succeeds if the Top Theory was already compiled
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compiled:-
  top_theory:theory(1, _, _),!. % the theory is compiled if there is a clause 1 (from the modeh)
