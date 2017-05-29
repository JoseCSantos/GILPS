%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Hindley-Milner Type Checker disabler
%
% Author: Jose Santos
% 13th August 2009
%
% We should load this module if a file is partially typed, we don't want to
% remove the type definitions but wish to disable the type checker
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(type_check_disabler,
	  [ op(1150, fx, type)
	  , op(1130, xfx, --->)
	  , op(1150, fx, pred)
	  , op(1150, fx, trust_pred)
	  , op(500,yfx,::)
	  , op(500,yfx,:<)
	  ]).
/*
:- op(1150, fx, type).
:- op(1130, xfx, ---> ).
:- op(1150, fx, pred).
:- op(500,yfx,::).
:- op(500,yfx,:<).
*/
pred(_).
trust_pred(_).
type(_).


