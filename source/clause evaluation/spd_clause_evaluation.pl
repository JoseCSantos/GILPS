%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-08-15
%
%     This module implements 'smallest_predicate_domain' clause evaluation
%
%     The idea is to replace the depth first left to right standard Prolog evaluation mechanism
%     by selecting at each moment the literal with the fewest number of solutions.
%
% Results: This brings a several order magnitude speedup for clauses with many literals.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(spd_clause_evaluation, %spd stands for 'smallest predicate domain'
            [
              spd_clause_evaluation/3,
             
              % spd_preprocess/3, spd_lits_evaluation/1 and spd_update_litsinfo/3 are only to be called
              % by module common_clause_evaluation (they would have package visibility only in Java)
              spd_preprocess/3,
              spd_lits_evaluation/1,
              spd_update_litsinfo/3              
            ]
         ).

% GILPS modules
:- use_module('../utils/clause', [atomArgs/4]).
:- use_module('../utils/list', [firstNElemsOf/3]).
:- use_module('../utils/goal_solutions', [count_solutions/3]).
:- use_module('../settings/settings', [setting/2]).
:- use_module('common_clause_evaluation', [evaluate_literal/1]).
:- use_module('../mode declarations/mode_declarations', [recursive_mode_declarations/1]).

% YAP modules
:- use_module(library(ordsets), [ord_union/3]).

:- dynamic spd_clause_cache/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% spd_clause_evaluation(+Clause, +ClauseSig, +Atom)
%
% Given:
%   Clause: a clause as a list of literals
%   ClauseSig: Clause's signature
%   Atom: an atom that matches Clause's head
%
% Succeeds if Clause can prove Atom
%
% Notes:
%  Binds Clause's variables with a substitution that entails atom
%  Shouldn't be used if Clause is recursive or if the cut_transformation has been applied
%  (it's in principle possible to conjugate spd clause evaluation with both these scenarios but is more complex)
%  For the moment we are not bounding the number of resolutions. That should be done as well
%
%  InstVars is implicit! we can just check if the input places are ground!
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

spd_clause_evaluation([Atom|Body], [_HeadSig|BodySig], Atom):-
  spd_preprocess(Body, BodySig, BodyInfo),
  spd_lits_evaluation(BodyInfo).

%spd_lits_evaluation(+BodyInfo)
spd_lits_evaluation(BodyInfo):-
  ready_to_be_called(BodyInfo, ReadyToCallLits, LitsInfo),
  spd_body_evaluation(ReadyToCallLits, LitsInfo).

%spd_body_evaluation(+ReadyToCallLits, +LitsInfo)
spd_body_evaluation([], []).
spd_body_evaluation([_-(Lit, _, _Index)|ReadyToCallLits], LitsInfo):-
  evaluate_literal(Lit),
  %call(user:Lit),,% Lit is guaranteed to have it's input variables bound, its output variables will get bound as well
                   % which will make other Lit variables in ReadyToCallLits to be ground as well
  (ReadyToCallLits = [1-_|_] -> % if the next literal had just 1 solution before, continue with it
     NReadyToCallLits = ReadyToCallLits,
     RemainLitsInfo = LitsInfo
    ;
     update_ready_to_call(ReadyToCallLits, UReadyToCallLits), %update ready_to_call
     ready_to_be_called(LitsInfo, TempReadyToCallLits, RemainLitsInfo),
     ord_union(UReadyToCallLits, TempReadyToCallLits, NReadyToCallLits)
  ),
/*
  update_ready_to_call(ReadyToCallLits, UReadyToCallLits), %update ready_to_call
  (UReadyToCallLits = [1-_|_] ->
     NReadyToCallLits = UReadyToCallLits,
     RemainLitsInfo=LitsInfo
    ;
     ready_to_be_called(LitsInfo, TempReadyToCallLits, RemainLitsInfo),
     ord_union(UReadyToCallLits, TempReadyToCallLits, NReadyToCallLits)
  ),
*/
  spd_body_evaluation(NReadyToCallLits, RemainLitsInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% update_ready_to_call(+ReadyToCallLits, -UpdReadyToCallLits)
%
% Given:
%  ReadyToCallLits: an ascending ordered list of tuples, each of the form (LitInVars, NumFreeVars, Lit)
%
% Returns:
%  UpdReadyToCallLits: updates ReadyToCallLits considering to consider the reduction in solutions due to the latest binding
%
% Notes:
%  We only update the solutions of a literal ready to be called iff some of its output variables could bound
%  and it has now less variables than before.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

update_ready_to_call(ReadyToCallLits, UpdReadyToCallLits):-
  update_ready_to_call_aux(ReadyToCallLits, ReadyToCallLitsAux),
  keysort(ReadyToCallLitsAux, UpdReadyToCallLits).

update_ready_to_call_aux([], []).
update_ready_to_call_aux([_NumSols-(Lit, OldNumVars, Index)|RC],
                         [UpNumSols-(Lit, LitNumVars, Index)|URC]):-
  %only update if Lit has less then NumVars free variables
  OldNumVars>0,
  numFreeVariables(Lit, LitNumVars),
  LitNumVars<OldNumVars,!,
  cache(Lit, UpNumSols),
  UpNumSols>0,
  %update_ready_to_call_aux(RC, URC).
  (UpNumSols=1 -> URC = RC ; update_ready_to_call_aux(RC, URC)).

update_ready_to_call_aux([H|T], [H|R]):-%Skip as the literal has the same number of solutions as before
  update_ready_to_call_aux(T, R).

%numFreeVariables(+Term, -NumFreeVars)
numFreeVariables(Term, NumFreeVars):-
  term_variables(Term, Vars), % count the free (output) variables in Literal
  length(Vars, NumFreeVars).  % input variables are guaranteed to be bound in Lit

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% spd_preprocess(+Lits, +LitsSig, -LitsInfo)
%
% Given:
%   Lits: a list of literals
%   LitsSig: Lits signatures
%
% Returns:
%   LitsInfo: a list of (LitInVars, NumFreeVars, Lit, Index)
%             where LitInVars is a sorted list of Lit input variables
%             NumVars is the number of free output variables of Lit (useful later to efficiently update
%                 Lit's solution)
%             Lit is the literal
%             Index: literal position in clause (useful for recording the latest failing literal)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

spd_preprocess(Lits, LitsSig, LitsInfo):-
  preprocess_aux(Lits, LitsSig, 2, LitsInfo).

preprocess_aux([], [], _, []).
preprocess_aux([Lit|Lits], [LitSig|LitSigs], Index, [(LitInVars, NumVars, Lit, Index)|LitInfo]):-
  atomArgs(Lit, LitSig, LitInVars, LitOutVars),
  Index1 is Index+1,
  numFreeVariables(LitOutVars, NumVars),
  preprocess_aux(Lits, LitSigs, Index1, LitInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% ready_to_be_called(+LitsInfo, -ReadyToCall, -RemainLitsInfo)
%
% Given:
%   LitsInfo: a list of tuples, each of the form (LitInVars, LitOutVars, Lit, Index)
%
% Returns:
%  LitsSols: an ordered (ascending by the number of solutions) non-empty list of the literals ready to be called
%            each element of this list is a tuple: NumSolutions-(Literal, NumFreeVars, LitIndex, Literal Solutions)
%  RemainInfo: litsInfo not in LitsSols
%
% Notes:
%   We stop as soon as we find a predicate with 0 solutions
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ready_to_be_called(LitsInfo, ReadyToCall, RemainLitsInfo):-
  ready_to_be_called_aux(LitsInfo, ReadyToCallAux, RemainLitsInfo),
  keysort(ReadyToCallAux, ReadyToCall).

ready_to_be_called_aux([], [], []).
ready_to_be_called_aux([(LitIV, NumVars, Lit, Index)|LitsInfo],
                       [NumSols-(Lit, UpdNumVars, Index)|ReadyToCall], RemainLitsInfo):-
  ground(LitIV),!,% a literal is ready to be called if its input terms are all ground
  cache(Lit, NumSols),
  %format("Before:~w After: ~w~n", [_NumVars, UpdNumVars]),
  NumSols>0,
  UpdNumVars=NumVars, %We should update the number of free variables but if we do, it's in general slower!
  %numFreeVariables(Lit, UpdNumVars),
  (NumSols=1 -> % this will in general speed things up
    ReadyToCall=[],
    RemainLitsInfo=LitsInfo
   ;
    ready_to_be_called_aux(LitsInfo, ReadyToCall, RemainLitsInfo)
  ).

ready_to_be_called_aux([LitInfo|LitsInfo], ReadyToCall, [LitInfo|RemainLitsInfo]):-
  ready_to_be_called_aux(LitsInfo, ReadyToCall, RemainLitsInfo).
  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% spd_update_litsinfo(+VarsLitsInfo, +LastLitIndexToConsider, -NewVarsLitsInfo)
%
% Given:
%  VarsLitsInfo: a VarsLitsInfo term as described in svd_preprocess/3
%  LastIndexToConsider: index of the last literal to consider
%
% Returns:
%  NewVarsInfo: VarsLitsInfo with all literals after LastIndexToConsider removed
%
% Notes: The purpose of this predicate is to update VarsLitsInfo between binary finding first failing literals
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

spd_update_litsinfo(LitsInfo, LastLitIndexToConsider, NewLitsInfo):-
  CutPoint is LastLitIndexToConsider-1,
  firstNElemsOf(LitsInfo, CutPoint, NewLitsInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Cache
%
% Caching solutions makes the spd clause evaluation around 20%-30% faster (at some memory expense)
% This result was with a cache of ~77.000 literals, each having on average 8.7 solutions
%
% If the predicates have very few solutions (e.g. are determinate) then cache can have an adverse effect
% making spd clause evaluation around 5% slower.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%cache(+Pred, -NumSols)
%cache(Pred, NumSols):- !, count_solutions(user:Pred, +inf, NumSols). % this line disables the cache
cache(Pred, NumSols):-
  copy_term(Pred, PredS),
  numbervars(PredS, 0, NumFreeVars),
  setting(recall_bound_on_evaluation, RecallBound),%RecallBound=(+inf),
  (NumFreeVars=0 -> %same as ground(Pred)
    count_solutions(user:Pred, RecallBound, NumSols)
    %Note: Although NumSols should be 0 or 1 since the term is ground, if the same term is repeated several
    % times in the BK it will be more than 1. That's the reason why I'm using (+inf) rather than 1.
    % If I said MaxSols=1 and the term had more solutions, the call(user:Lit) would still succeed several
    % times which could degrade performance as we would be selecting a predicate that may backtrack convinced
    % it wouldn't (because NumSols would be 1). In the proteins dataset there was a situation like this!
    % which made the cached spd clause evaluation more than 30x slower
   ;
    (spd_clause_cache(PredS, NumSols) ->  %PredS already in cache
    %(recorded(PredS, NumSols, _) ->  %PredS already in cache
      true
     ;
      count_solutions(user:Pred, RecallBound, NumSols),
      (NumSols>5 -> % only store a predicate in cache if it has more than 5 solutions, otherwise don't bother
         asserta(spd_clause_cache(PredS, NumSols)) % we add predS
       ;
         %term has less than 5 solutions, do not add it to BD
         true
      )
     % recorda(PredS, NumSols, _)
    )
  ).
