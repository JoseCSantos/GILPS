%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-10-05
%
%     This module implements an advanced clause evaluation that is based on enumerating variable domains
%     (like svd_clause_evaluation.pl) but has several important new concepts:
%
%     * It identifies components in the variable graph thus evaluating independent components separately
%       and not in series (this is akin to the once transformation of Vitor Santos Costa but done at
%       the variable level)
%     * In addition, for variables that influence no other (a particular case are singletons) there is
%       no need to try values from its domain. Any value consistent with the literals where variable appears
%       as input will do and we will not backtrack there.
%     * There is no computation of the domain at each turn. The heuristic is the variable that is most
%       constrained.
%     * New auxiliar datastructure for the clause evaluation. Tuple: ceval(ClauseInfo, VarInfos), where:
%          ClauseInfo: cinfo(LitInfo1, .., LitInfoN), where:
%                 LitInfo: literal info of the form: linfo(Literal, Literal Input Vars, Literal Output vars)
%                 (there is a LitInfo term for each literal in the original clause)
%                 (note: if a variable appears both as input and output in the same literal, it just appears
%                        in Literal Input Vars)
%          VarInfos: list of VarInfo, where: (there is a VarInfo for each distinct variable in the original clause)
%
%             VarInfo: vinfo(Var, PosIn, PosOut, Interactions)
%                 Var: a variable (from clause)
%                 PosIn: ascending ordered list of positions (1 based) in ClauseInfo, where
%                        there are literals which have Var as an INPUT variable
%                 PosOut: ascending ordered list of positions (1 based) in ClauseInfo, where
%                          there are literals which have Var as an OUTPUT variable
%                    (note: if a variable appears both as input and output in the same literal, it just appears in PosIn)
%                 Interactions: ordered list of vars that Var interacts with (i.e. may change Var's domain and vice-versa)
%
%    A sketch of the clause evaluation loop is:
%
%       1. Build a graph of influences using all (non-ground) Interactions in VarInfos
%       2. Divide this graph into its independent components
%       3. For each of those components // sorted from the one with fewest variable to the one with most variables do
%       4.   Choose a variable V from the current component which has at least one lit invar instantiated
%              and, from those, the one with highest ground lit invar + ground interactions
%       5.   Determine V domain, make sure it's non empty, and iterate over it 
%       6.   If the variables V interacts are all ground (or there are none) commit it solution and don't iterate
%             over V further
%       7.   Goto 1
%          End For
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(adv_clause_evaluation, %adv stands for advanced
            [
              adv_clause_evaluation/1,
              adv_clause_evaluation/3,
              % adv_preprocess/3, adv_clause_evaluation/1 and adv_update_clause_eval_ds/3 are only to be called by module
              % common_clause_evaluation (they would have package visibility only in Java)
              adv_preprocess/3,
              adv_update_clause_eval_ds/3
            ]
         ).

% GILPS modules
:- use_module('../utils/list', [firstNElemsOf/3, custom_qsort/3, member_identical/2, remove_after/3]).
:- use_module('../utils/clause', [atomArgs/4, skolemize/2]).

% YAP modules
:- use_module(library(ordsets), [list_to_ord_set/2, ord_del_element/3, ord_intersection/3, ord_member/2, ord_subtract/3, ord_union/2, ord_union/3]).
:- use_module(library(lists), [append/3, flatten/2, member/2]).
:- use_module(library(apply_macros), [checklist/2, convlist/3, selectlist/3, maplist/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_literal_variable_solution_cache(+Lit, +Var, -Values)
%
%  This dynamic predicate caches (i.e. stores and returns) in Values all the solutions for
%  variable Var (appearing in literal Lit).
%
%  Notice: Lit and Var must be skolemized together prior to storing and retrieving. This has the
%  important effect is that the cache doesn't care about variable names this way. E.g.
%    cache(br1(d1,d1_1,A),A) has the same solutions as cache(br1(d1,d1_1,B),B)
%  (I think it would be incorrect
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic adv_literal_variable_solution_cache/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_clause_evaluation(+Clause, +ClauseSig, +Atom)
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
%  For the moment we are not bounding the number of resolutions. That should be done as well.
%  We assume that each literal in the clause has at least one (possibly the same) variable.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adv_clause_evaluation([Atom|Body], ClauseSig, Atom):-
  adv_preprocess([Atom|Body], ClauseSig, ClauseEvalTerm),
  adv_clause_evaluation(ClauseEvalTerm).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_clause_evaluation(+ClauseEvalTerm)
%
% Given:
%   ClauseEvalTerm: a clause evaluation term as described in adv_preprocess/3
%
% Notes:
%  We assume that each literal in the clause has at least one (possibly the same) variable
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adv_clause_evaluation(CETerm):-
  CETerm=ceval(ClauseInfo, _),
  ClauseInfo=..[cinfo,linfo(_Lit, LitInVars, _LitOutVars)|BodyLitsInfo],
  %format("CETerm:~w~2n", [CETerm]),
  %portray_clause(CETerm),nl,
  convlist(ready_to_call_litinfo, BodyLitsInfo, ReadyToCallLiterals), % find ready to call literals (i.e. literals where the head variables are the only input variables to it)
  %checklist(has_solution, ReadyToCallLiterals),%make sure those predicates have at least one solution
  have_solutions(ReadyToCallLiterals),
  adv_clause_components(CETerm, LitInVars, CETerms),
  checklist(solve_independent_component, CETerms).

%ready_to_call_litinfo(+LitInfo, -ReadyToCallLiteral)
ready_to_call_litinfo(linfo(Literal, LitInVars, _LitOutVars), Literal):-
  ground(LitInVars).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% solve_independent_component(+ClauseEvalTerm)
%
% Given:
%   ClauseEvalTerm: a clause evaluation term as described in adv_preprocess/3
%
% Succeeds: iff ClauseEvalTerm has a solution
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve_independent_component(ceval(_, [])):-!.  % no variables to instantiate, succeed
solve_independent_component(ceval(ClauseInfo, VarsInfo)):-
  choose_most_promising_variable(ClauseInfo, VarsInfo, Variable),
  varinfo(Variable, VarsInfo, VInfo, NVarsInfo),
  VInfo=vinfo(Variable, PosIn, PosOut, Interactions),
  determine_variable_domain(PosOut, Variable, ClauseInfo, VarDomain),
  adv_clause_components(ceval(ClauseInfo, NVarsInfo), [Variable], CETerms),
  %length(CETerms, N),
  %format("CETerms len=~w~n", [N]),
  convlist(callableLiterals(ClauseInfo, Variable), PosIn, CallableLiterals),
  %(ground(Interactions) -> SafeToCut=true ; SafeToCut=false),
  (checklist(ground, Interactions) -> SafeToCut=true ; SafeToCut=false), % stop checking for ground as soon as one free variable found
  %format("Var:~w Inters:~w~n", [Variable, Interactions]),
  member(Variable, VarDomain),
  %checklist(has_solution, CallableLiterals), % replacing checklist/2 by a custom predicate speeds this up by ~3% overall
  have_solutions(CallableLiterals),
  (SafeToCut-> ! ; true),
  checklist(solve_independent_component, CETerms).

%callableLiterals(+ClauseInfo, +Var, +Position, -Literal)
callableLiterals(ClauseInfo, Variable, Position, Literal):-
  arg(Position, ClauseInfo, linfo(Literal, LitInVars, _LitOutVars)), %Variable appears in LitInVars
  ground_ignoring(LitInVars, Variable).

%ground_ignoring(+Variables, +VariableToIgnore).
ground_ignoring([], _).
ground_ignoring([H|T], V):-
  (ground(H);H==V),
  ground_ignoring(T, V).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% has_solution(+Literal)
%
% Given:
%  Literal: a literal (that is guaranteed to have its input variables ground) for which we want to know if it has
%           at least one solution
%
% Notes:
%   This predicate makes sure the literals where the variable we are iterating the domain over still have at least
%   one solution. If we didn't perform this test it would be possible to return a solution where one doesn't exist. 
%   (for instance, in predicates where such variable is the only input variable)
%
%   Notice however that by making sure there is at least one solution per predicate we don't make sure the whole clause
%   is consistent (i.e. all its free variables can be bound) as that would be very expensive.
%   In CSP terms: we are doing arc consistency but not path consistency.
%
%   Nevertheless, if an inconsistency exists, it will be catch up later when the free variables get bound and one gets
%   an empty domain
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%has_solution(+Literal)
has_solution(Literal):-
  \+(\+(once(call(user:Literal)))). % \+\+ to don't bind variables in Literal

%have_solutions(+CallableLiterals)
have_solutions([]).
have_solutions([Lit|Lits]):-
  \+(\+(once(call(user:Lit)))),
  have_solutions(Lits).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% choose_most_promising_variable(+ClauseInfo, +VarsInfo, -Variable)
%
% Given:
%  ClauseInfo: a cinfo term as described in the header of this file
%  VarsInfo: a list of vinfo terms as described in the head of this file
%
% Returns:
%  Variable: a variable from varsinfo that is the "most promising one" (i.e. the one most likely to further reduce
%            the search. The current criteria for such a variable is:
%               1) must have at least one literal (where it appears as output variable) with its input variables bound
%               2) minimizes the sum: total number of literals bound + number of ground variables that influence it
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

choose_most_promising_variable(ClauseInfo, VarsInfo, Variable):-
  highest_scoring_variable(VarsInfo, ClauseInfo, 0, _, Variable). % 0 for most constrained
  %highest_scoring_variable(VarsInfo, ClauseInfo, inf, _, Variable). % inf for least domain

% highest_scoring_variable(+VarsInfo, +ClauseInfo, +CurBestScore, +CurBestVariable, -BestVariable)
highest_scoring_variable([], _, CurBestScore, BestVariable, BestVariable):-
  (CurBestScore>0 -> 
     !
   ; 
    format("Error in advanced clause evaluation (highest_scoring_variable/4)~n",[]),
    format("This error should never happen!~n",[])
  ).
highest_scoring_variable([VInfo|VarsInfo], ClauseInfo, CurBestScore, CurBestVariable, BestVariable):-
  vinfo_score(VInfo, ClauseInfo, VarScore),
%  format("VarScore:~w~n", [VarScore]),
  %(VarScore<CurBestScore ->
  (VarScore>CurBestScore ->
    VInfo=vinfo(Variable, _, _, _Interactions),
    highest_scoring_variable(VarsInfo, ClauseInfo, VarScore, Variable, BestVariable)
   ;
    highest_scoring_variable(VarsInfo, ClauseInfo, CurBestScore, CurBestVariable, BestVariable)
  ).

%vinfo_score(+VInfo, +ClauseInfo, -Score), %score as given by an heuristic
vinfo_score(vinfo(_Variable, _PosIn, PosOut, Interactions), ClauseInfo, Score):-
  count_callable_literals(PosOut, ClauseInfo, NumCallableLiterals),
  (NumCallableLiterals>0 ->
    selectlist(ground, Interactions, GroundInteractions),
    length(GroundInteractions, NumGroundInteractions),
    Score is NumCallableLiterals + NumGroundInteractions
   ;
    Score = 0
  ).

/*
vinfo_score(vinfo(Variable, _PosIn, PosOut, _Interactions), ClauseInfo, Score):-
  determine_variable_domain(PosOut, Variable, ClauseInfo, VarDomain),
  (var(VarDomain) ->
     Score = inf
   ;
     VarDomain=[_|_],
     length(VarDomain, Score)
  ).
*/
% count_callable_literals(+PosOut, +ClauseInfo, -NumCallableLiterals)
count_callable_literals(PosOut, ClauseInfo, NumCallableLiterals):-
  count_callable_literals(PosOut, ClauseInfo, 0, NumCallableLiterals).

% count_callable_literals(+PosOut, +ClauseInfo, +CurNumCallableLiterals, -FinalNumCallableLiterals)
count_callable_literals([], _, NumCallableLiterals, NumCallableLiterals).
count_callable_literals([PosOut|RemainPosOut], ClauseInfo, CurNumCallableLiterals, FinalNumCallableLiterals):-
  arg(PosOut, ClauseInfo, linfo(_Lit, LitInVars, _LitOutVars)), % Variable is a member of LitOutVars
  ground(LitInVars),!,
  CurNumCallableLiterals1 is CurNumCallableLiterals+1,
  count_callable_literals(RemainPosOut, ClauseInfo, CurNumCallableLiterals1, FinalNumCallableLiterals).
count_callable_literals([_PosOut|RemainPosOut], ClauseInfo, CurNumCallableLiterals, FinalNumCallableLiterals):-
  count_callable_literals(RemainPosOut, ClauseInfo, CurNumCallableLiterals, FinalNumCallableLiterals).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% determine_variable_domain(+PosWhereVarOut, +Variable, +ClauseInfo, -VariableDomain)
%
% Given:
%  PosWhereVarOut: list of positions (relative to clauseinfo term) where Variable
%                  is an output variable for a literal
%  Variable: a variable
%  ClauseInfo: a cinfo term as described in the header of this file
%
% Returns:
%  VariableDomain: ordered list of unique possible values for variable Variable
%
% Notes:
%  There is no empty base case as it is guaranteed that there is at least one literal that PosWhereVarOut
%  refers to that has its input variables instantiated
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_variable_domain([], _Variable, _ClauseInfo, _VariableDomain):-!.
  %format("Error in advanced clause evaluation (determine_variable_domain/4)~n",[]),
  %format("This error should never happen!~n",[]).

determine_variable_domain([PosOut|RemainPosOut], Variable, ClauseInfo, FVarDomain):-
  arg(PosOut, ClauseInfo, LitInfo), % Variable is a member of LitOutVars in LitInfo
  litinfo_2_variable_domain(LitInfo, Variable, CurVarDomain),!,
  CurVarDomain=[_|_],
  determine_variable_domain_aux(RemainPosOut, Variable, ClauseInfo, CurVarDomain, FVarDomain).
determine_variable_domain([_|RemainPosOut], Variable, ClauseInfo, VariableDomain):-
  determine_variable_domain(RemainPosOut, Variable, ClauseInfo, VariableDomain).

% determine_variable_domain_aux(+PosWhereVarOut, +Variable, +ClauseInfo, +CurVarDomain, -VariableDomain)
determine_variable_domain_aux([], _, _, VarDomain, VarDomain).
determine_variable_domain_aux([PosOut|RemainPosOut], Variable, ClauseInfo, ValuesSoFar, FValues):-
  arg(PosOut, ClauseInfo, LitInfo), % Variable is a member of LitOutVars in LitInfo
  litinfo_2_variable_domain(LitInfo, Variable, CurValues),!,
  ord_intersection(CurValues, ValuesSoFar, NValuesSoFar),
  NValuesSoFar=[_|_], % must be non empty otherwise fails
  determine_variable_domain_aux(RemainPosOut, Variable, ClauseInfo, NValuesSoFar, FValues).
determine_variable_domain_aux([_PosOut|RemainPosOut], Variable, ClauseInfo, ValuesSoFar, FValues):-
  determine_variable_domain_aux(RemainPosOut, Variable, ClauseInfo, ValuesSoFar, FValues).

%litinfo_2_variable_domain(+LitInfo, +Variable, -Values)
litinfo_2_variable_domain(linfo(Lit, LitInVars, _LitOutVars), Variable, Values):-
  ground(LitInVars), % we can only call Lit if its input variables are all ground
  %format("looking for all values of variable ~w in lit: ~w~n", [Variable, Lit]),
  cache(Variable, Lit, Values).

%cache(+Variable, +Lit, -Values)
cache(Variable, Lit, Values):-
  skolemize((Variable, Lit), (VarS, LitS)),
  (adv_literal_variable_solution_cache(LitS, VarS, Values) ->
     true
   ;
    findall(Variable, call(user:Lit), Values1),
    list_to_ord_set(Values1, Values),
    asserta(adv_literal_variable_solution_cache(LitS, VarS, Values))
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_clause_components(+CETerm, +VarsToIgnore, -CETerms)
%
% Given:
%   CETerm: a clause evaluation term, ceval(ClauseInfo, VarsInfo) as described in the header of this file
%   VarsToIgnore: ordered list of variables to ignore when computing components (possibly empty)
%
% Returns:
%   CETerms: a list of clause evaluation terms, each sharing the clauseinfo part but with their varinfo
%            independent of each other (i.e. there is no overlap of variables in the varinfo section)
%            The clause terms are returned with the ones with fewest variables being first.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adv_clause_components(ceval(ClauseInfo, VarInfos), VarsToIgnore, CETerms):-
  selectlist(consider_var(VarsToIgnore), VarInfos, VarsToConsider),
  maplist(construct_var_interaction(VarsToIgnore), VarsToConsider, VarInteractions),
  adv_find_all_components(VarInteractions, VarsList),
  custom_qsort(VarsList, smaller_list, SVarsList), % sort lists according to their lengths
  create_components(SVarsList, VarInfos, ClauseInfo, CETerms).

%smaller_list(-Result, +List1, +List2)
smaller_list(<, L1, L2):-
  length(L1, N1),
  length(L2, N2),
  N1<N2,!. % this cut is essential as otherwise we would leave a choice point opened
% we do not want equality, otherwise equal lists would be pruned
smaller_list(>, _, _).

%consider_var(+VarsToIgnore, +VarInfo)
consider_var(VarsToIgnore, vinfo(Var, _PosIn, _PosOut, _Interactions)):-
  var(Var),
  \+ ord_member(Var, VarsToIgnore). % VarsToIgnore is not ground and sorted

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% construct_var_interaction(+VarsToIgnore, +VarInfo, -VarInteraction)
%
% Given:
%   VarsToIgnore: ordered list of variables to ignore when considering variables interactions
%   VarInfo: varinfo/4 (as described in the header of this file)
%
% Returns:
%   VarInteraction: a term of the form: vinter(Var, Interactions)
%                   where Interactions is an ordered list of (non ground) variables with whom Var interacts
%
% Notes:
%   This is an auxiliary datastructure to facilitate computing the clause components graph
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_var_interaction(VarsToIgnore, vinfo(Var, _PosIn, _PosOut, Interactions), vinter(Var, VarInteractions)):-
  selectlist(var, Interactions, Inter1), %discard ground interactions
  ord_subtract(Inter1, VarsToIgnore, VarInteractions). %discard variables to ignore

%varsinter_for_vars(+Vars, +VarsInteractions, -VarsVarInteractions, -RemainVarsInteractions)
varsinter_for_vars([], VarsInters, [], VarsInters).
varsinter_for_vars([Var|Vars], AllVarsInters, [VInter|VVInters], RemainVarsInters):-
  varinter(Var, AllVarsInters, VInter, NAllVarsInters),
  varsinter_for_vars(Vars, NAllVarsInters, VVInters, RemainVarsInters).

%varinter(+Var, +VarsInters, -VInter, -NVarsInter)
varinter(VarA, [vinter(VarB, VInters)|VsInters], vinter(VarB, VInters), VsInters):-
  VarA==VarB,!.
varinter(VarA, [CurVInter|VsInters], FinalVInter, [CurVInter|RVInters]):-
  varinter(VarA, VsInters, FinalVInter, RVInters).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_find_all_components(+VarInteractions, -VarsList)
%
% Given:
%   VarInteractions: list of var interactions terms (see construct_var_interaction/2)
%
% Returns:
%   VarsList: list of lists of ordered variables. Each variable belongs to a different component of the clause graph
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adv_find_all_components([], []):- !.
adv_find_all_components(VarInteractions, [VarsInComponent|RemainVarsList]):-
  adv_find_component(VarInteractions, VarsInComponent, RemainVarInteractions),
  adv_find_all_components(RemainVarInteractions, RemainVarsList).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_find_component(+VarInteractions, -VarsInComponent, -RemainVarInteractions)
%
% Given:
%   VarInteractions: list of var interactions terms (see construct_var_interaction/2)
%
% Returns:
%   VarsInComponent: list of variables appearing in a component
%   RemainVarInfos: VarInteractions with vinters corresponding to VarsInComponent removed
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adv_find_component([], [], []).
adv_find_component([vinter(Var, VInter)|VInters], VarsInComponent, RemainVarInters):-
  adv_find_component_aux(VInter, [Var], VarsInComponent, VInters, RemainVarInters).

%adv_find_component_aux(+VariablesToAddToComponent, +CurVarsInCompoment,
%                       -FinalVarsInComponent, +CurVarsInteractions, -RemainVarsInteractions)
adv_find_component_aux([], VarsInComponent, VarsInComponent, VarsInters, VarsInters):- !.
adv_find_component_aux(VarsToAdd, CurVars, FVarsComp, CurVarsInters, RemainVarsInters):-
  varsinter_for_vars(VarsToAdd, CurVarsInters, VarsToAdd_VarInters, NVarsInters),
  get_vars_to_add(VarsToAdd_VarInters, TVarsToAdd), % TVarsToAdd: variables to visit next
  ord_union(VarsToAdd, CurVars, NCurVars),          % NCurVars: variables already visited so far
  ord_subtract(TVarsToAdd, NCurVars, NVarsToAdd),   % NVarsToAdd: unseen variables to visit next
  adv_find_component_aux(NVarsToAdd, NCurVars, FVarsComp, NVarsInters, RemainVarsInters).

% get_vars_to_add(+VarsToAdd_VarInters, -VarsToAdd)
get_vars_to_add(VarsToAdd_VarInters, VarsToAdd):-
  get_vars_to_add(VarsToAdd_VarInters, [], VarsToAdd).

% get_vars_to_add(+VarsToAdd_VarInters, +CurVarsToAdd, -NVarsToAdd)
get_vars_to_add([], VarsToAdd, VarsToAdd).
get_vars_to_add([vinter(_Var, VInter)|VsInters], CurVarsToAdd, FinalVarsToAdd):-
  ord_union(CurVarsToAdd, VInter, NextVarsToAdd),
  get_vars_to_add(VsInters, NextVarsToAdd, FinalVarsToAdd).

%create_components(+VarsList, +VarInfos, +ClauseInfo, -CETerms)
create_components([], _, _, []).
create_components([Vars|T], VarInfos, ClauseInfo, [ceval(ClauseInfo, VarsVarInfos)|R]):-
  varsinfo_for_vars(Vars, VarInfos, VarsVarInfos, RemainVarInfos),
  create_components(T, RemainVarInfos, ClauseInfo, R).

%varsinfo_for_vars(+Vars, +AllVarInfos, -VarsVarInfos, -RemainVarInfos)
varsinfo_for_vars([], VarInfos, [], VarInfos).
varsinfo_for_vars([Var|Vars], AllVarInfos, [VInfo|VVInfos], RemainVarInfos):-
  varinfo(Var, AllVarInfos, VInfo, NAllVarInfos),
  varsinfo_for_vars(Vars, NAllVarInfos, VVInfos, RemainVarInfos).

%varinfo(+Var, +VarsInfo, -VInfo, -NVarsInfo)
varinfo(VarA, [vinfo(VarB, PosIn, PosOut, Inters)|VInfos], vinfo(VarB, PosIn, PosOut, Inters), VInfos):-
  VarA==VarB,!.
varinfo(VarA, [CurVInfo|VInfos], FinalVInfo, [CurVInfo|RInfos]):-
  varinfo(VarA, VInfos, FinalVInfo, RInfos).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_preprocess(+Clause, +ClauseSig, -CETerm)
%
% Given:
%   Clause: clause as a list of literals
%   ClauseSig: Clause signature
%
% Returns:
%   CETerm: a clause evaluation term, ceval(ClauseInfo, VarsInfo) as described in the header of this file
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adv_preprocess(Clause, ClauseSig, ceval(ClauseInfo, VarInfos)):-
  create_clause_info(Clause, ClauseSig, LitsInfo),
  ClauseInfo=..[cinfo|LitsInfo],
  term_variables(Clause, Variables),
  create_var_infos(Variables, ClauseInfo, VarInfos).

%create_clause_info(+Clause, +ClauseSig, -LitsInfo)
create_clause_info([], [], []).
create_clause_info([Lit|Lits], [LitSig|LitSigs], [linfo(Lit, LitInVars, LitOutVars)|LitsInfo]):-
  atomArgs(Lit, LitSig, LitInVars, TLitOutVars),% some of the LitInVars may be ground (e.g. Head Input variables)
  ord_subtract(TLitOutVars, LitInVars, LitOutVars), %ignore output variables that are also input in the same predicate
  create_clause_info(Lits, LitSigs, LitsInfo).

% create_var_infos(+Variables, +ClauseInfo, -VarInfos).
create_var_infos([], _, []).
create_var_infos([Var|Variables], ClauseInfo, [VInfo|VarInfos]):-
  create_var_info(Var, ClauseInfo, VInfo),
  create_var_infos(Variables, ClauseInfo, VarInfos).

% create_var_info(+Var, +ClauseInfo, -VarInfo)
create_var_info(Var, ClauseInfo, vinfo(Var, PosIn, PosOut, Interactions)):-
  ClauseInfo=..[cinfo|LitsInfo],
  indexs_var(Var, LitsInfo, input, PosIn),
  indexs_var(Var, LitsInfo, output, PosOut),
  var_interactions(Var, ClauseInfo, PosIn, PosOut, Interactions).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% var_interactions(+Var, +ClauseInfo, +PosIn, +PosOut, -Interactions)
%
% Given:
%   Var: a variable
%   ClauseInfo: a clause info (i.e. cinfo(linfos)) term as described in the header of this file
%   PosIn: literal indexs (relative to ClauseInfo) where var appears as input variable 
%   PosOut: literal indexs (relative to ClauseInfo) where var appears as output variable
%
% Returns:
%   Interactions: ordered list of variables (some may be ground) that interact with Var
%                 (i.e. appear in the same predicate at least once)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
var_interactions(Var, ClauseInfo, PosIn, PosOut, Interactions):-
  append(PosIn, PosOut, AllPos), % AllPos does not need to be ordered
  maplist(process_all_indexs(ClauseInfo), AllPos, InteractionsAux),
  ord_union(InteractionsAux, TInteractions),
  ord_del_element(TInteractions, Var, Interactions).

%process_all_indexs(+ClauseInfo, +Position, -Interactions)
process_all_indexs(ClauseInfo, Pos, Interactions):-
  arg(Pos, ClauseInfo, linfo(_Lit, LitInVars, LitOutVars)),
  list_to_ord_set(LitInVars, SLitInVars), %sort LitInVars because some of their variables may be ground now
  list_to_ord_set(LitOutVars, SLitOutVars), %sort LitOutVars because some of their variables may be ground now
  ord_union(SLitInVars, SLitOutVars, Interactions).
*/

var_interactions(Var, ClauseInfo, PosIn, PosOut, Interactions):-
  append(PosIn, PosOut, AllPos), % AllPos does not need to be ordered
  maplist(process_all_indexs(ClauseInfo), AllPos, InteractionsAux),
  flatten(InteractionsAux, TInteractions1),
  list_to_ord_set(TInteractions1, TInteractions),
  ord_del_element(TInteractions, Var, Interactions).

process_all_indexs(ClauseInfo, Pos, [LitInVars, LitOutVars]):-
  arg(Pos, ClauseInfo, linfo(_Lit, LitInVars, LitOutVars)).

%indexs_var(+Var, +LitsInfo, +Mode, -Positions)
indexs_var(Var, LitsInfo, Mode, Positions):-
  indexs_var_aux(LitsInfo, 1, Var, Mode, Positions).

indexs_var_aux([], _, _, _, []).
indexs_var_aux([LitInfo|LitInfos], CurPos, Var, Mode, [CurPos|Positions]):-
  var_in_litinfo(Var, Mode, LitInfo),!,
  CurPos1 is CurPos+1,
  indexs_var_aux(LitInfos, CurPos1, Var, Mode, Positions).
indexs_var_aux([_|LitInfos], CurPos, Var, Mode, Positions):-
  CurPos1 is CurPos+1,
  indexs_var_aux(LitInfos, CurPos1, Var, Mode, Positions).

%var_in_litinfo(+Var, +Mode, +LitInfo)
var_in_litinfo(Var, input, linfo(_, LitInVars, _LitOutVars)):-
  member_identical(Var, LitInVars),!.
var_in_litinfo(Var, output, linfo(_, _LitInVars, LitOutVars)):-
  member_identical(Var, LitOutVars),!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% adv_update_clause_eval_ds(+CETerm, +LastLitIndexToConsider, -NCETerm)
% (updates clause evaluation datastructure)
%
% Given:
%  CETerm: original clause evaluation term, ceval(ClauseInfo, VarsInfo) as described in the header of this file
%          considering all the literals
%  LastIndexToConsider: index of the last literal to consider
%
% Returns:
%  NCETerm: a new clause evaluation term considering only literals up to position LastIndexsToConsider
%
% Notes: The purpose of this predicate is to update the clause evaluation datastructure
%        so that it can be used for the binary finding of first failing literals
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

adv_update_clause_eval_ds(ceval(ClauseInfo, VarInfos), LastLitIndexToConsider, ceval(NClauseInfo, NVarInfos)):-
  ClauseInfo=..[cinfo|LitsInfo],
  firstNElemsOf(LitsInfo, LastLitIndexToConsider, NLitsInfo),
  NClauseInfo=..[cinfo|NLitsInfo],
  term_variables(NLitsInfo, Variables),% Note: term_variables does NOT sort the Variables, this could be a problem
  length(Variables, NumVariables),
  firstNElemsOf(VarInfos, NumVariables, TVarInfos),%remove all variables after the first NumVariables
  update_variables_info(TVarInfos, LastLitIndexToConsider, NClauseInfo, NVarInfos).

% update_variables_info(+VarInfos, +LastLitIndexToConsider, +ClauseInfo, -NVarInfos).
update_variables_info([], _, _, []).
update_variables_info([VInfo|VInfos], LastLitIndexToConsider, ClauseInfo, [UVInfo|RVInfos]):-
  update_variable_info(VInfo, LastLitIndexToConsider, ClauseInfo, UVInfo),
  update_variables_info(VInfos, LastLitIndexToConsider, ClauseInfo, RVInfos).

%update_variable_info(+VInfo, +LastLitIndexToConsider, +ClauseInfo, -UVInfo)
update_variable_info(vinfo(Var, PosIn, PosOut, _Interactions),
                     LastLitIndexToConsider, ClauseInfo,
                     vinfo(Var, NPosIn, NPosOut, NInteractions)):-
  remove_after(PosIn, LastLitIndexToConsider, NPosIn),
  remove_after(PosOut, LastLitIndexToConsider, NPosOut),
  var_interactions(Var, ClauseInfo, NPosIn, NPosOut, NInteractions).
