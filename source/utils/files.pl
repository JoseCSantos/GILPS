%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-02-11
%
%     This file contains misc. utilities to deal with files for Input/Output
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(utils_files,
            [
              load_term/2,
              save_term/2
            ]
         ).

% type checker
%:- use_module('../type_checker/type_check').

% YAP modules
:- use_module(library(rbtrees), [list_to_rbtree/2, rb_visit/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% load_term(+Filename, -Term)
%
% Given:
%   Filename: a filename having the term to load
%
% Returns:
%   Term: the term present in Filename
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_term(Filename, Term):-
  open(Filename, read, File), % File is an handle for Filename which is opened in read-only mode
  read(File, Term),
  close(File).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% save_term(+Filename, +Term)
%
% Given:
%   Filename: a filename to store the term
%   Term: the term to save in Filename
%
% Succeeds if it manage to create a filename with the term
%
% Notes:
%   If the filename already exists it will be overwritten
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

save_term(Filename, Term):-
  open(Filename, write, File), % File is an handle for Filename which is opened in write (no append) mode
  format(File, "~k.", [Term]), % the '.' is needed for read/2 to work
  close(File).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% rbtree_load(+Filename, -RBTree)
%
% Given:
%   Filename: a filename having a red-black tree
%
% Returns:
%   RBtree: the red-black tree present in Filename
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rbtree_load(Filename, RBTree):-
  load_term(Filename, RBTreeAsList),
  list_to_rbtree(RBTreeAsList, RBTree).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% rbtree_save(+Filename, +RBTree)
%
% Given:
%   Filename: a filename to store the red-black tree
%   RBtree: a red-black tree to save in Filename
%
% Succeeds if it manage to create a filename with the rbtree
%
% Notes:
%   If the filename already exists it will be overwritten
%   Using a list representation to write the rbtree is more compact
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rbtree_save(Filename, RBTree):-
  rb_visit(RBTree, RBTreeAsList), % converting to list saves a lot of space in the representation
  save_term(Filename, RBTreeAsList).
