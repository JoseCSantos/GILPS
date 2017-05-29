%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-08-13
%
%    This file contains predicates to compute the least general generalization of two clauses
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(least_general_generalization,
            [
              llg/6
            ]
         ).

% GILPS modules
%:- use_module('../settings/settings', [setting/2]).  % because of 'i': number of new variables layers, depth and resolutions
:- use_module('../utils/clause', [atomArgs/4, atomArgsTyped/4]).
%:- use_module('../examples/examples', [example/5, positiveExamplesUnifying/4]). % to retrieve example id
%:- use_module('../mode declarations/mode_declarations', [mode_head/1, modebDecls/1, recursive_mode_declarations/1]).
%:- use_module('../utils/list', [createList/3, split/4]).
%:- use_module('../utils/control', [uniqueInterpretations/3]).

% YAP modules
%:- use_module(library(rbtrees), [rb_new/1, rb_lookup/3, rb_insert/4, rb_visit/2, rb_update/4, rb_update/5]).
%:- use_module(library(lists), [member/2, memberchk/2, reverse/2, append/3]).
%:- use_module(library(apply_macros), [selectlist/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Type of important datastructures for constructing the lgg
%
%    Mapping: an rb_tree where the key is a pair (Term1-Term2) and value is the variable
%             associated with this pair
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% lgg(+Clause1, +ClauseSig1, +Clause2, +ClauseSig2, -lgg, -lggSig)
%
% Given:
%   Clause1: a clause as a list of literals
%   Clause1Sig: Clause1 signature
%   Clause2: a clause as a list of literals
%   Clause2Sig: Clause2 signature
%
% Returns:
%   lgg: least general generalization of Clause1 and Clause2
%   lggSig: lgg signature
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lgg([Head1|Body1], [HeadSig|Body1Sig], [Head2|Body2], [HeadSig|Body2Sig], [LGG_Head|LGG_Body] [HeadSig|LGG_BodySig]):-
  atomArgs(Head1, HeadSig, H1IV, H1OV),
  atomArgs(Head2, HeadSig, H2IV, H2OV),
  initial_mapping(Map0),
  matchVars(H1IV, H2IV, Map0, MIV, Map1),
  matchVars(H1IV, H2OV, Map1, MOV, Map2),
  
atomArgs(Atom, AtomSig, AtomInputVariables, AtomOutputVariables):-

