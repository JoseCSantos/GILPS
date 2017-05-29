%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-09-05
%
%     This module implements 'smallest_variable_domain' clause evaluation
%
%     The idea is to replace the depth first left to right standard Prolog evaluation mechanism
%     by selecting at each moment the variable with the fewest number of solutions.
%
% Results: This brings a several order magnitude speedup for clauses with many literals.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(svd_clause_evaluation, %svd stands for 'smallest variable domain'
            [
              svd_clause_evaluation/3,
              % svd_preprocess/3, svd_vars_evaluation/1 and svd_update_varsinfo/3 are only to be called by module
              % common_clause_evaluation (they would have package visibility only in Java)
              svd_preprocess/3,
              svd_vars_evaluation/1,
              svd_update_varsinfo/3
            ]
         ).

% GILPS modules
:- use_module('../utils/clause', [atomArgs/4, skolemize/2, undo_skolemize/2]).
:- use_module('../utils/goal_solutions', [count_solutions/3]).

% YAP modules
:- use_module(library(ordsets), [ord_intersection/3]).
:- use_module(library(lists), [member/2]).

:- dynamic svd_cache/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% svd_clause_evaluation(+Clause, +ClauseSig, +Atom)
%
% Given:
%   Clause: a clause as a list of literals
%   ClauseSig: Clause's signature
%   Atom: an atom that matches Clause's head
%
% Succeeds if Clause subsumes Atom
%
% Notes:
%  Binds Clause's variables with a substitution that entails atom
%  Shouldn't be used if Clause is recursive or if the cut_transformation has been applied
%  (it's in principle possible to conjugate dynamic clause evaluation with both these scenarios but is more complex)
%  For the moment we are not bounding the number of resolutions. That should be done as well
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

svd_clause_evaluation([Atom|Body], [_HeadSig|BodySig], Atom):-
  svd_preprocess(Body, BodySig, VarsLitsInfo),
  %format("VarLitsInfo: ~w ~n", [VarsLitsInfo]),
  svd_vars_evaluation(VarsLitsInfo).
  %format("Clause:~w~n", [[Atom|Body]]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% svd_vars_evaluation(+VarsInfo)
%
% Given:
%  VarsLitsInfo: a term as described in preprocess/3
%
% Notes:
%   This predicate heuristically binds variables from VarsLitsInfo
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

svd_vars_evaluation(VarsInfo):-
  process_ground_vars(VarsInfo, VarsInfo1), % we may need to prune ground vars
  svd_vars_evaluation_aux(VarsInfo1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% process_ground_vars(+VarsInfo, -NVarsInfo)
%
% Given:
%  VarsInfo: a term as described in svd_preprocess/3
%
% Returns:
%  NVarsInfo: updated VarsInfo with the ground vars of VarsInfo removed
%
% Notes:
%  This predicate only succeeds if the predicates to which the ground vars of VarsInfo (if any),
%  are input variables, have a solution
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

process_ground_vars([], []).
process_ground_vars([Var-LitsInfo|VarsInfo], [Var-LitsInfo|NVarsInfo]):-
  var(Var),!,
  process_ground_vars(VarsInfo, NVarsInfo).
process_ground_vars([_Var-(LitInVars, _LitOutVars)|VarsInfo], NVarsInfo):-
  %Var is ground, make sure the literals where it appears as input variables have solutions
  literals_have_solution(LitInVars),
  process_ground_vars(VarsInfo, NVarsInfo).

% svd_vars_evaluation_aux(+VarsInfo)
svd_vars_evaluation_aux([]).
svd_vars_evaluation_aux(VarsInfo):-
  select_most_promising_variable(VarsInfo, Var, Domain, NVarsInfo, VarLitsInfoIn),
  %format("Var: ~w ", [Var]),
  member(Var, Domain),
  literals_have_solution(VarLitsInfoIn), % we have to confirm that the literals where Var appear as input variables are consistent
  %format("has been assigned value ~w~n", [Var]),
  svd_vars_evaluation_aux(NVarsInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% literals_have_solution(+InVarLitsInfo)
% (an inliteral is a literal where the Variable to which InVarLitsInfo belongs is an input variable for that literal)
%
% This predicate makes sure the predicates where Var (to which InVarLitsInfo belongs)
% appears as an input variable still have at least one solution. If we didn't perform this test it would be possible
% to return a solution where one doesn't exist. 
%
% Notice howerver that by making sure there is at least one solution per predicate we don't make sure the whole clause
% is consistent (i.e. all its free variables can be bound) as that would be very expensive.
% In CSP terms: we are doing arc consistency but not path consistency.
%
% Nevertheless, if an inconsistency exists, it will be catch up later when the free variables get bound and one gets
% an empty domain
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

literals_have_solution([]).
literals_have_solution([(Lit, LitInVars, _Index)|VarLitsInfo]):-
  ground(LitInVars),!,
  %format("Checking for solution of ~w~n", [Lit]),
  \+(\+(once(call(user:Lit)))),
  %count_solutions(user:Lit, 2, NumSols),(NumSols=1-> once(call(user:Lit)); true), % this once would bind vars
  literals_have_solution(VarLitsInfo).
literals_have_solution([_|VarLitsInfo]):-
  %If input variables are not ground, assume it's consistent for now (this is safe, the only
  % problem is that it may delay finding an inconsistency until the remaining input variables are all ground
  literals_have_solution(VarLitsInfo).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% select_most_promising_variable(+VarsInfo, -Var, -Domain, -NewVarsInfo, -VarLitsInfoIn)
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
% choose always the first variable
select_most_promising_variable([Var-(VLitsInfoIn, VLitsInfoOut)|R], Var, Domain, R, VLitsInfoIn):-
  !,variable_domain(VLitsInfoOut, Var, Domain).

% select the variable with longer VLitsInfoOut where their LitInVars are ground (because it should be the most constrained), but must have 
select_most_promising_variable(VarsInfo, Var, Domain, NVarsInfo, VLitsInfoIn):-
  most_likely_constrained_var(VarsInfo, +inf, _CurVar, Var),
  get_litsinfo_for_variable(VarsInfo, Var, (VLitsInfoIn, VarLitsInfoOut), NVarsInfo),
  variable_domain(VarLitsInfoOut, Var, Domain).
  %format("Selected Var:~w~nDomain:~w~n", [Var, Domain]).

%most_likely_constrained_var(+VarsInfo, +CurSmallerVarsLitsInfoOut, +CurBestVar, -BestVar).
most_likely_constrained_var([], SmallestVLO, Var, Var):-
  !,
  SmallestVLO < (+inf).
most_likely_constrained_var([V-(_VLitsInfoIn,VLitsInfoOut)|T], SmallestVLO, CurVar, Var):-
  length(VLitsInfoOut, N),
  (N<SmallestVLO ->
     NSmallestVLO=N,
     NCurVar=V
   ;
     NSmallestVLO=SmallestVLO,
     NCurVar=CurVar    
  ),
  most_likely_constrained_var(T, NSmallestVLO, NCurVar, Var).
*/
% choose the variable with smallest domain
select_most_promising_variable(VarsInfo, Var, Domain, NewVarsInfo, VarLitsInfoIn):-
 variable_with_smallest_domain(VarsInfo, Var, Domain, NewVarsInfo, VarLitsInfoIn).

% variable_with_smallest_domain(+VarsLitsInfo, -Var, -Domain, -NewVarsLitsInfo, -VarLitsInfoIn)
variable_with_smallest_domain(VarsInfo, Var, Domain, NewVarsInfo, VarLitsInfoIn):-
  variable_with_smallest_domain_aux(VarsInfo, +inf, _CurVar, _CurDomain, ShortestLength, Var, Domain),
  ShortestLength<(+inf),
  %format("Selected domain has length ~w~n", [ShortestLength]),halt,
  get_litsinfo_for_variable(VarsInfo, Var, (VarLitsInfoIn, _VarLitsInfoOut), NewVarsInfo).

%variable_with_smallest_domain_aux(+VarsLitsInfo, +CurShortestDomainLength, +CurBestVar, +CurShortestDomain,
%                                  -ShortestDomainLength, -BestVar, -ShortestDomain)
variable_with_smallest_domain_aux([], ShortestDLength, BestVar, ShortestDomain, ShortestDLength, BestVar, ShortestDomain).
variable_with_smallest_domain_aux([(Var-(_LitsInfoIn, LitsInfoOut))|T], CurShortestDomainLength,
                                  CurBestVar, CurShortestDomain, ShortestDLength, BestVar, ShortestDomain):-
  variable_domain(LitsInfoOut, Var, Domain),
  %format("Var: ~w~nDomain:~w~n", [Var, Domain]),
  (var(Domain) -> % VarDomain is not ground
     %format("Domain is not ground~n",[]),
     variable_with_smallest_domain_aux(T, CurShortestDomainLength, CurBestVar, CurShortestDomain,
                                       ShortestDLength, BestVar, ShortestDomain)
   ;
     length(Domain, LenDomain),%LenDomain is >=1
     %format("Domain has length ~w (~w)~n",[LenDomain, CurShortestDomainLength]),
     (LenDomain=1 ->
        BestVar = Var,
        ShortestDomain = Domain,
        ShortestDLength = 1
      ;
       (LenDomain<CurShortestDomainLength ->
          variable_with_smallest_domain_aux(T, LenDomain, Var, Domain, ShortestDLength, BestVar, ShortestDomain)
        ;
          variable_with_smallest_domain_aux(T, CurShortestDomainLength, CurBestVar, CurShortestDomain,
                                            ShortestDLength, BestVar, ShortestDomain)     
       )
     )
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% variable_domain(+LitsInfo, +Variable, -VariableDomain)
%
% Given:
%  LitsInfo: list of literals info. Each a term of the form: (LitInVars, Lit)
%            (it's guaranteed that Variable is in term_variables(Lit))
%  Variable: variable which we want to know its domain
%
% Returns:
%  VariableDomain: ordered list of unique possible values for variable Variable
%
% Notes:
%  If all LitsInfo for a variable are not ground, then this predicate still succeeds but the VariableDomain
%  is left free (meaning we can't call variable, but can't dismiss it either)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

variable_domain([], _Variable, _Domain).
variable_domain([LitI|LitIs], Variable, Domain):-
  litinfo_2_variable_domain(LitI, Variable, LitIValues),!,
  variable_domain_aux(LitIs, Variable, LitIValues, Domain).
variable_domain([_|LitIs], Variable, Domain):-
  variable_domain(LitIs, Variable, Domain). %LitI doesn't have its input variables bound

%litinfo_2_variable_domain(+LitInfo, +Variable, -Values)
/*
:- table litinfo_2_variable_domain/3.

% version without cache
litinfo_2_variable_domain((Lit, LitInVars, _Index), Variable, Values):-
  ground(LitInVars), % we can only call Lit if it's input variables are all ground
  findall(Variable, call(user:Lit), Values1),
  sort(Values1, Values).
*/

litinfo_2_variable_domain((Lit, LitInVars, _Index), Variable, Values):-
  ground(LitInVars), % we can only call Lit if it's input variables are all ground
  %format("looking for all values of variable ~w in lit: ~w~n", [Variable, Lit]),
  cache(Variable, Lit, Values).

%cache(+Variable, +Lit, -Values)
cache(Variable, Lit, Values):-
  skolemize((Variable,Lit), (VarS,LitS)),
  (svd_cache(LitS, VarS, Values) ->
     true
   ;
    findall(Variable, call(user:Lit), Values1),
    sort(Values1, Values),
    asserta(svd_cache(LitS, VarS, Values))
  ).

/*
litinfo_2_variable_domain((Lit, LitInVars, _Index), Variable, Values):-
  ground(LitInVars), % we can only call Lit if it's input variables are all ground
  %format("looking for all values of variable ~w in lit: ~w~n", [Variable, Lit]),
  skolemize((Variable,Lit), (VarS,LitS)),
  cache2(VarS, LitS, Values).

:- table cache2/3.

cache2(VarSkolemized, LitSkolemized, Values):-
  undo_skolemize((VarSkolemized, LitSkolemized), (Variable, Lit)),
  findall(Variable, call(user:Lit), Values1),
  sort(Values1, Values).
*/

%variable_domain_aux(+LitsInfo, +Variable, +ValuesSoFar, -FValues)
variable_domain_aux([], _, FValues, FValues).
variable_domain_aux([LitI|LitIs], Variable, ValuesSoFar, FValues):-
  litinfo_2_variable_domain(LitI, Variable, CurValues),!,
  ord_intersection(CurValues, ValuesSoFar, NValuesSoFar),
%  format("After intersection:~w~n", [NValuesSoFar]),
  NValuesSoFar=[UniqueValue|Remain], % There is at least one solution, otherwise fails
  (Remain=[] -> %There is exactly one solution
     FValues=[UniqueValue],
     Variable=UniqueValue,
     literals_have_solution(LitIs) % make sure the remaining literals have a solution
                                   % this will cause less ord_intersections and cache checks
   ;
     variable_domain_aux(LitIs, Variable, NValuesSoFar, FValues)
  ).
variable_domain_aux([_|LitIs], Variable, ValuesSoFar, FValues):-
  variable_domain_aux(LitIs, Variable, ValuesSoFar, FValues). %LitI doesn't have it's input variables bound

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% svd_preprocess(+Lits, +LitsSig, -VarsLitsInfo)
%
% Given:
%   Lits: a list of literals
%   LitsSig: Lits signatures
%
% Returns:
%   VarsLitsInfo: a list where each element is a tuple: Variable-(LitsInfoForVariableIn, LitsInfoForVariableOut) where:
%          Variable: variable appearing in the clause (each Variable occurs just once in LitsVarInfo)
%          LitsInfoForVariableIn: list that, for all the literals in Lits where Variable occurs
%                                  as part of the input arguments, has the tuple: (Lit, LitInVars, Index), where:
%                Lit: the literal itself
%                LitInVars: input variables for Lit
%                Index: index of Lit in Clause (head is index 1, first literal is index 2...)
%          LitsInfoForVariableOut: identical to LitsInfoForVariableIn but has the literals where Variable occurs
%                                  as part of the output arguments.  Same tuple: (Lit, LitInVars, Index)
%                                                                 (it's really LitInVars here and not LitOutVars)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

svd_preprocess(Lits, LitSigs, VarsLitsInfo):-
  preprocess_aux(Lits, LitSigs, 2, [], VarsLitsInfo).

%preprocess_aux(+Lits, +LitSigs, +CurIndex, +CurVarsLitsInfo, -FinalVarsLitsInfo).
preprocess_aux([], [], _, FVarsLitsInfo, FVarsLitsInfo).
preprocess_aux([Lit|Lits], [LitSig|LitSigs], Index, CurVarsLitsInfo, FVarsLitsInfo):-
  atomArgs(Lit, LitSig, LitInVars, LitOutVars),% some of the LitInVars may be ground (e.g. Head Input variables)
  update_vars_info(LitInVars, LitInVars, Lit, Index, input, CurVarsLitsInfo, CurVarsLitsInfo1),
  update_vars_info(LitOutVars, LitInVars, Lit, Index, output, CurVarsLitsInfo1, NCurVarsLitsInfo),
  Index1 is Index+1,
  preprocess_aux(Lits, LitSigs, Index1, NCurVarsLitsInfo, FVarsLitsInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% update_vars_info(+LitOutVars, +LitInVars, +Lit, +Index, +Mode, +CurVarsLitsInfo, -FCurVarsLitsInfo)
%
% Given:
%   LitOutVars: output variables for Lit
%   LitInVars: input variables for Lit
%   Lit: a literal
%   Index: index of Lit in clause
%   Mode: either 'input' or 'output'. input updates the input part of CurVarsLitsInfo, 'output' the output part
%   CurVarsLitsInfo: term as described preprocess/3 (LitVarsInfo there)
%
% Returns:
%   FCurVarsInfo: updated CurVarsInfo to consider the variables in LitOutVars
%
% Notes: this predicate just updates the out part of a VarsLitsInfo
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

update_vars_info([], _LitInVars, _Lit, _Index, _Mode, VarsLitsInfo,  VarsLitsInfo).
update_vars_info([Var|Vars], LitInVars, Lit, Index, Mode, CurVarsLitsInfo, FCurVarsLitsInfo):-
  get_litsinfo_for_variable(CurVarsLitsInfo, Var, (InPart, OutPart), CurVarsLitsInfo1),
  (Mode=input ->
    NCurVarsLitsInfo=[(Var-([(Lit, LitInVars, Index)|InPart], OutPart))|CurVarsLitsInfo1]
   ; % Mode=output
    NCurVarsLitsInfo=[(Var-(InPart, [(Lit, LitInVars, Index)|OutPart]))|CurVarsLitsInfo1]
  ),
  update_vars_info(Vars, LitInVars, Lit, Index, Mode, NCurVarsLitsInfo, FCurVarsLitsInfo).

%get_litsinfo_for_variable(+CurVarsLitsInfo, +Var, -LitsInfoForVar, -NCurVarsLitsInfo)
get_litsinfo_for_variable([], _Var, ([], []), []). % Var does not yet exist
get_litsinfo_for_variable([(VarA-LitsInfoForVar)|R], VarB, LitsInfoForVar, R):-
  VarA==VarB,!.
get_litsinfo_for_variable([H|T], Var, LitsInfoForVar, [H|R]):-
  get_litsinfo_for_variable(T, Var, LitsInfoForVar, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% svd_update_varsinfo(+VarsLitsInfo, +LastLitIndexToConsider, -NewVarsLitsInfo)
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

svd_update_varsinfo([], _, []).
svd_update_varsinfo([Var-(InVarLitsInfo, OutVarLitsInfo)|T], LastLitIndexToConsider, NewVarsLitsInfo):-
  remove_litindexs_above(InVarLitsInfo, LastLitIndexToConsider, NInVarLitsInfo),
  remove_litindexs_above(OutVarLitsInfo, LastLitIndexToConsider, NOutVarLitsInfo),
  (NInVarLitsInfo=[], NOutVarLitsInfo=[] ->
     NewVarsLitsInfo = RemainNewVarsLitsInfo % do not leave Var with no literals associated
   ;
     NewVarsLitsInfo = [Var-(NInVarLitsInfo, NOutVarLitsInfo)|RemainNewVarsLitsInfo]    
  ),
  svd_update_varsinfo(T, LastLitIndexToConsider, RemainNewVarsLitsInfo).

%remove_litindexs_above(+VarLitsInfo, +LastLitIndexToConsider, -NVarLitsInfo)
% note that indexs in VarLitsInfo are in descending order
remove_litindexs_above([(_Lit, _LitInVars, Index)|T], LastIndex, NVarLitsInfo):-
  Index>LastIndex,!,
  remove_litindexs_above(T, LastIndex, NVarLitsInfo).
remove_litindexs_above(L, _, L).
