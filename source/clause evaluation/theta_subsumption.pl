%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2010-03-05
%
%     This theta-subsumption module builds upon advanced clause evaluation. The main novelty is that the example is given as a ground clause
%     rather than goals keep being called from the background knowledge. This allows to precompute the domain of the variables
%     beforehand and being able to call any predicate regardless of the input/output restrictions.
%
% Areas to improve:
%  1) The index of a variable in a given literal can be shared across all the literals where the same variable is in the same placeholder
%  for the same predicate symbol. This will save significant(?) memory at very minor cpu time expense.
%  2) At least, when indexs are computed (and computing indexs is an expensive operation), those indexs only need to be computed per unique
%  (variable placeholder in predicate symbol)
%  3) The PredValues in each linfo can be taken out and factorized away having as key the predicate symbol only
%  This will save memory at the expense of very little extra cpu time.
%
% Changes from 15-Fev-2010 version :
%   * Fixed a bug that would cause subsumer to fail to detect subsumption in some cases where there were more than one variable
%     in the hypothesis head. This would only happen if we were using subsumer with example ids rather than with the full ground
%     bottom clause and was because the hypothesis datastructure were computed prior to binding and could possible be out of order
%     later on (if head argument 1>argument 2). The fix was simply to replace two ord_list_to_rbtree/2 by list_to_rbtree/2.
%
% Changes from 12-Fev-2010 version :
%   * Fixed a bug that would generate false subsumptions in case the subsumer clause was fully ground after head binding.
%     In such cases, as long as the subsumee had the same predicate symbols, the terms weren't checked for compatibility!)
%     E.g.  theta_subsumes([c(X),h(X),f(X,b)], [c(d), h(d), f(d,c)]) should fail (but was succeeding before)
%
% Changes from initial (Dec 2009) version :
%    * Fixed a bug that prevented testing subsumption properly when the subsumee clauses had variables
%      This was due to findalls renaming variables and skolemizing the head terms when they were variables
%      E.g. theta_subsumes([a(A),b(A,B)],[a(X),b(X,Y)]) 
%    * A consequence of this bug fix is that now the subsumption test is ~20-25% faster!
%
% A bug was found in Resumer2 and Django. If the subsumer clause is disconnected they fail the subsumption test. Eg.
%   theta_subsumes([a(A),b(A,B),c(C,C)],[a(a),b(a,b),c(c,c)]) should succeed (and succeeds with Subsumer, but fails with Resumer2 and Django)
%
% Main datastructures for ground subsumption:
% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%
%    *  The main data structure that is used for evaluation is a term: ceval(ClauseInfo, VarsInfo, PairwiseVarInteractions)  where:
%          ClauseInfo: a term cinfo/N (N=#literals in hypothesis (including head)) of the form: cinfo(linfo1, ..., linfoN), where at the i-th position there is
%                 a term linfo/5 with information on the i-th literal in the hypothesis. 
%
%                 linfo(Pred, Args, ArgVars, Index, PredValues) where:
%                    Pred: literal signature (i.e. Name/Arity)
%                    Args: predicate arguments
%                    ArgVarIDs: sorted list of distinct variable ids in Args
%                    Index: sorted list where, for each variable in ArgVars, we have an element of the form: VarID-ValueInfoPos, where:
%                             VarID: a variable ID for a variable in ArgVars
%                             ValueInfoPos: a term vpos/N (N=length of initial Var domain) where the ith argument (corresponding to the ith
%                                           possible value of Var) contains the sorted list of all the positions in PredValues that have that value for Var.
%                    PredValues: is a term values/N (N=number of uniq values for predicate) where at position ith there is a list representing the
%                                ith solution for this predicate. (the length of this list is the Arity of the predicate) and this is constructed
%                                from the sorted list of values at CondensedExampleBody.
%
%               E.g. LitInfo=linfo(br0/3, [d1,B,C], [2,3], Index, values([d1,b1,c1],[d1,b2,c1],[d1,b3,c2])).
%                    Index=[2-vpos([1],[2],[3]),3-vpos([1,2],[3],[])]. % supposing 2 is the ID for B, 3 is the ID for C and that
%                                                                      % B's values are [b1,b2,b3], and C's values are: [c1,c2,c3]
%
%       VarsInfo: a term varsinfo/N (N=#distinct variables in hypothesis), of the form: varsinfo(vinfo1, ..., vinfoN), where at the i-th position
%                     there is a vinfo/4 term with information on the i-th variable.
%
%            vinfo(Var, ID, Inters, InitialDomain) where:
%               Var: variable being considered
%               ID: a variable unique ID (first variable has ID 1, second ID 2, nth, ID n) (that is its i-th position on VarsInfo term)
%               Inters: sorted list of distinct variables IDs with whom Var interacts (i.e. shares a literal with) excluding Var itself
%               InitialDomain: a term of the form idom(v1, ..., vn) where each vi is a possible value for Var
%
%               E.g.: VarsInfo= varsinfo(vinfo(A,[2,3],idom(a,b,c,d)),...)
%
%      PairwiseVarInters: red-black tree where the key is of the form (VarID1,VarID2)  where VarID1 and VarID2 are variables that interact 
%                     Both (V1,V2) and (V2,V1) appear as key. The value is the list of positions (relative to HypBody) where Var1 and Var2
%                     share a predicate (first literal of the body is position 2)
%                     Note tht we also have (V1,V1) and the meaning is the list of positions where V1 appears
%
%                     Example of the rb_tree in list format:  [(1,1)-[1,2,3,4,5],(1,2)-[2],(2,1)-[2],(2,2)-[2,3,4,5]]
%
%      Notice the ceval/3 term is static, i.e. neither of its members will be updated. CEval is the result of preprocessing an example and hypothesis
%
%     There are two other important datastructures:
%
%     *  VarsInComponent:  an ordered list of variable ids that belong to the component under consideration. E.g. VarsInComponent=[1,2,3,4,5,6,7,8,9]
%        A component is a list of variable ids that influence each other (even if indirectly). Variables V1 and V2 are in the same component iff:
%             same_component(V1, V2):-
%                neighbours(V1, NV1),
%                memberchk(V2, NV1).
%             same_component(V1, V2):-
%                neighbours(V1, NV1),
%                checklist(same_component(V2), NV1).
%
%        Notice that all variables involved in the path from V1 to V2 must not be ground (including V1 and V2)
%
%     * VarsAllowedPositions: a term vars_allowed_pos/N (N=#distinct variables in hypothesis), of the form vars_allowed_pos(AllowedPos1, .., AllowedPosN)
%                              where AllowedPos_I is a term DomainLen-DomainValues where DomainLen is the length of DomainValues and
%                                           DomainValues is ordered list of indexs allowed for variable I (i.e. the i-th variable from a VarsInfo term)
%
%                              E.g. vars_allowed_pos([3-[1,4,8], 2-[1,3], 5-[1,2,7,8,9], ...)
%
% Auxiliary datastructures for theta subsumption:
% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%
%  CondensedExampleBody: an ordered list where each argument is a distinct predName/Arity is put in evidence followed by a list of all
%                        possible values for the predicate. Each element is of the form: predName/Arity-PredicateArgValues
%
%                E.g.:   ExampleBody= [b0(a,b,c),b1(a,d,x), b0(a,g, h), b1(a,e, f)],
%                        CondensedExampleBody= [b0/3-[[a,b,c], [a,g,h]], ,b1/3-[[a,d,x], [a,e,f]]
%
%  VarsDomain: a list with all the distinct variables appearing in hypothesis. Each variable is a term:
%                 vdomain(Var, AllowedDomainPos, InitialDomain) where:
%                      Var: the variable
%                      AllowedDomainPos: an ordered list of the values from InitialDomain that are still consistent
%                      InitialDomain: an ordered list of the possible values for Var
%                 E.g. [vdomain(A, [1,3,4], [a,b,c,d,e,f]), vdomain(B, [2,4,5], [1,5,6,7,8]), ...]
%                         (the above would mean that current valid A values are: 'a','c' or 'd' and for B: '5','7' or '8'.
%
%  VarPredicateCalls: sorted list where each element is of the form: Var-VarUniqLitArgsCall where 
%                     VarUniqLitArgsCall is a list where each element is of the form:
%                        Pred/Arity-Args, where Args is the list of all the unique* arguments of predicates having Var as argument
%     unique*= after skolemization. ('$VAR'(0) is the skolemized variable that matters for the variable in cause)
%
%           E.g.: [B-[br0/3-[[$'VAR'(1),$'VAR'(0),$'VAR'(2)],[$'VAR'(1),$'VAR'(2),$'VAR'(0)])], ... ]
%
%  UniqPredCallDomain: sorted list where each term is: (Name/Arity,SkolemLitArgs)-DomainPos where:
%                         DomainPos: ordered list where each term is: Value-Positions, 
%                         where Positions is the list of positions where Value appears in place of '$VAR'(0)
%                          (relative to the domain for Name/Arity in CondensedExampleBody)
%
%                     E.g. [(br0/3, [d1, '$VAR'(0), '$VAR'(1)])-[a-[1,2,3],b-[4,5,6]]
%
%  FullVarInters: a list where each element is of the form: Var-ListInteractions, where ListInteractions is the sorted list of all variables
%                        with whom Var interacts
%
%                      E.g. [A-[B,C,D,E,F], B-[A,C,D], C-[A,B,E], D-[A,B], E-[A,C], F-[A]]
%
%  Var2ID: an rb_tree that has as key a variable and as value its ID.
%              E.g. (rbtree represented as list): [A-1, B-2, C-3, D-4]
%
%
% Ideas for further improvements (may not pay off, though):
% ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
%
% Order the possible values for a variable in order to minimize the domain of the subsequent variables
% Choose a variable that minimizes the product complexity of the  new components rather than by smallest domain.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(theta_subsumption, 
    		  [
                    load_example/3, % this is needed for GILPS integration
		    load_examples/2,
    		    theta_subsumes/2,
    		    theta_subsumes_exampleids/3,
    		    theta_subsumes_exampleids/5,
    		    first_failing_literal/3,
    		    first_failing_literal/4
                    %remove_failing_literals/6
    		  ]
         ).

% GILPS modules
:- use_module('../bottom clause/bottom_clause', [ground_sat/4]). %to compute the ground bottom clause from one example
:- use_module('../settings/settings', [setting/2]). % to get recall bound
:- use_module('../utils/list', [append_keys/2, append_sorted_keys/2, custom_qsort/3, merge_keys/2, merge_sorted_keys/2, numbersList/3, firstNElemsOf/3]).
:- use_module('../utils/clause', [skolemize/2, skolemize_ignoring/3, undo_skolemize/2]).

% YAP modules
:- use_module(library(ordsets), [list_to_ord_set/2, ord_del_element/3, ord_intersection/3, ord_subtract/3, ord_union/3]).
:- use_module(library(lists), [append/3, delete/3, member/2, memberchk/2, min_list/2, nth/4, reverse/2]).
%:- use_module(library(apply_macros), [checklist/2, convlist/3, selectlist/3, maplist/3]).
:- use_module(library(maplist), [checklist/2, convlist/3, selectlist/3, maplist/3]).
:- use_module(library(rbtrees), [list_to_rbtree/2, ord_list_to_rbtree/2, rb_lookup/3, rb_visit/2]).
%:- use_module(library(terms), [term_variables/2]).

:- set_prolog_flag(single_var_warnings, on).
:- set_prolog_flag(unknown, warning).

% there is a term in the blackboard which has the ExampleID (an integer) as key, and as body a term
% example(Weight, Head, CondensedBody)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% load_example(+ExampleAtom, +ExampleWeight, +ExampleID)
%
% Given:
%  ExampleAtom: a single atom (e.g. 'p(d0)'). It's NOT a list of literals!
%  ExampleWeight: a float, the integer of example ExampleAtom
%  ExampleID: an integer representing the ID of this example
%
% As side effect:
%  Computes the ground bottom clause for this example and assigns to it the id ExampleID
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_example(ExampleAtom, Weight, ExampleID):-
  setting(recall_bound_on_evaluation, RecallBound), % to support recall bound..
  ground_sat(ExampleAtom, RecallBound, [ExampleAtom|ExampleGroundBodyBottom], _ExampleSig),% if we didn't support recall bound, we want to use infinite recall, not the star_default_recall
  preprocess_example(ExampleGroundBodyBottom, ExampleCondensedBody),
  %(ExampleCondensedBody=[]->format("Bad: ~w~n", [ExampleID]) ; format("Good: ~w~n",[ExampleID])),halt,
  %format("Adding example id ~w with weight ~w,EB:~w~n", [ExampleID, Weight, ExampleCondensedBody]),
  bb_put(ExampleID, example(Weight, ExampleAtom, ExampleCondensedBody)). %bb_put/2 is similar to recorda/3 but module specific

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% load_examples(+Examples, -ExampleIDs)
%
% Given:
%  Examples: list of examples (each is a list of literals)
%
% Returns:
%  ExampleIDs: list of uniq integers for each example in Examples
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_examples(Examples, ExampleIDs):-
  load_examples_aux(Examples, 1, ExampleIDs).

load_examples_aux([], _, []).
load_examples_aux([Example|Examples], EID, [EID|EIDs]):-
  Example=[Head|Body],
  preprocess_example(Body, CondensedBody),
  bb_put(EID, example(1, Head, CondensedBody)), %bb_put/2 is similar to recorda/3 but module specific, assign weight 1
  EID1 is EID+1,
  load_examples_aux(Examples, EID1, EIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% theta_subsumes(+Clause, +Example)
%
% Given:
%   Clause: a clause as a list of literals
%   Example: an example as a list of literals with everything that is true about it
%
% Succeeds if Clause subsumes Example. Clauses free variables get bound with possible solutions
%
% Notes:
%  Binds Clause's variables with a substitution that subsumes atom
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theta_subsumes(Clause, Example):-
  compute_clause_eval_term(Clause, Example, CEvalTerm, VarsAllowedPos),
  theta_subsumes_aux(CEvalTerm, VarsAllowedPos).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% theta_subsumes_exampleids(+Clause, +ExampleIDs, -SubsumedExampleIDs)
% theta_subsumes_exampleids(+Clause, +ExampleIDs, +MaxAbsWeightToCover, -AbsFinalWeightCovered, -SubsumedExampleIDs)
%
% Given:
%   Clause: a clause as a list of literals
%   ExampleIDs: a list of example ids
%   MaxAbsWeightToCover: maximum absolute value for the total sum of weights of the examples covered
%
% Returns:
%   AbsFinalWeightcovered: final value for the maximum abs weight coverage
%   SubsumedExampleIDs: list of subsumed example ids (a subset of ExampleIDs), in the order given by ExampleIDs
%
% Notes:
%   Does not binds Clause's variables. The advantage of using this predicate is that both the preprocess_hypothesis/6 and preprocess_example/2 needs to be executed only once
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theta_subsumes_exampleids(Hypothesis, ExampleIDs, SubsumedExampleIDs):-
  theta_subsumes_exampleids(Hypothesis, ExampleIDs, inf, _, SubsumedExampleIDs).

theta_subsumes_exampleids([Head|Body], ExampleIDs, MaxWeight2Cover, WeightCovered, SubsumedExampleIDs):-
  %skolemize([Head|Body], Hyp),
  %portray_clause(Hyp),nl,
  preprocess_hypothesis([Head|Body], PLitsInfo, VarPredCalls, UniqPredCalls, PairwiseVarInters, FullVarInters),
  HypDS=hyp_ds(Head, PLitsInfo, VarPredCalls, UniqPredCalls, PairwiseVarInters, FullVarInters),
  theta_subsumes_exampleids(ExampleIDs, HypDS, MaxWeight2Cover, 0, WeightCovered, SubsumedExampleIDs).

% theta_subsumes_exampleids(+ExampleIDs, +HypDS, +MaxWeight2Cover, +CurWeightCovered, -FinalWeightCovered, -SubsumedExampleIDs)
theta_subsumes_exampleids([], _HypDS, _MaxWeights2Cover, WeightsCovered, WeightsCovered, []).
theta_subsumes_exampleids([EID|ExampleIDs], 
                        hyp_ds(HypHead, PLitsInfo, VarPredCalls, UniqPredCalls, PairwiseVarInters, FullVarInters), 
                        MaxWeight2Cover, CurWeightCovered, FinalWeightCovered,
                        SubsumedExampleIDs):-
  bb_get(EID, example(Weight, ExampleHead, CondensedExampleBody)),
%  format("Testing:~w Example:~k~n", [EID, ExampleHead]),
  %format("Testing:~w Example:~w Cond:~w~n", [EID, ExampleHead, CondensedExampleBody]),halt,
  (\+(\+((
            % try to simplify this later
             HypHead=ExampleHead,
             compute_predcall_domain(UniqPredCalls, CondensedExampleBody, UniqPredCallDomain),
             compute_variables_domain(UniqPredCallDomain, VarPredCalls, VarsDomain),
             compute_clause_info(PLitsInfo, CondensedExampleBody, UniqPredCallDomain, VarsDomain, ClauseInfo),
             create_variables_info(VarsDomain, FullVarInters, VarsInfo, VarsAllowedPos),
             theta_subsumes_aux(ceval(ClauseInfo, VarsInfo, PairwiseVarInters), VarsAllowedPos)
           ))) -> 
   %              format("Entailed~n",[]),
                 SubsumedExampleIDs = [EID|RemainSubsumedExampleIDs],
                 NCurWeightCovered is CurWeightCovered + abs(Weight)
             ;
                 SubsumedExampleIDs = RemainSubsumedExampleIDs,
                 NCurWeightCovered = CurWeightCovered
  ),
  (NCurWeightCovered > MaxWeight2Cover ->
    fail
   ;
    theta_subsumes_exampleids(ExampleIDs, 
			      hyp_ds(HypHead, PLitsInfo, VarPredCalls, UniqPredCalls, PairwiseVarInters, FullVarInters),
			      MaxWeight2Cover, NCurWeightCovered, FinalWeightCovered,
			      RemainSubsumedExampleIDs)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% theta_subsumes_aux(+ClauseEvalTerm, +VarsAllowedPos)
%
% Given:
%   ClauseEvalTerm: a clause evaluation term as described in preprocess/3
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

theta_subsumes_aux(ceval(ClauseInfo, VarsInfo, PairwiseVarInters), VarsAllowedPos):-
  functor(VarsInfo, varsinfo, NumVars), % the last variable has id NumVars
  (NumVars=0 -> % it may be possible that there are no variables to instantiate in the hypothesis (they all got ground when unifying with example)
     true       % in that case, we succeed. The clause evaluation term computation ensures the predicate name and arities match
   ;
     numbersList(1, NumVars, VarIDsToConsider),
     clause_components(VarsInfo, VarIDsToConsider, none, Components),
     checklist(solve_independent_component(ceval(ClauseInfo, VarsInfo, PairwiseVarInters), VarsAllowedPos), Components)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% solve_independent_component(+ClauseEvalTerm, +CurVarsAllowedPos, +VarsInComponent)
%
% Given:
%   ClauseEvalTerm: a clause evaluation term as described in the file header (this is a static term that never changes)
%   CurVarsAllowedPos: list with current variable domains of the form: vars_allowed_pos(AllowedPos1, .., AllowedPosN)
%                       where AllowedPos_I has the ordered list of indexs allowed for variable I (i.e. the i-th variable from the VarsInfo term of ClauseEvalTerm)
%   VarsInComponent: ordered list of the variables in the current component
%
% Succeeds: iff ClauseEvalTerm has a solution with the current CurVarDomains and VarsInComponent
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve_independent_component(ceval(_ClauseInfo, VarsInfo, _PairwiseVarInters), CurVarsAllowedPos, [VarID]):-
  !,  % single variable in component, it impacts no other variables, we don't have to iterate over its domain
  arg(VarID, VarsInfo, vinfo(Var, VarID, _VInters, InitialDomain)), % for no impact variables just assign the first value to it
  arg(VarID, CurVarsAllowedPos, _-AllowedPositionsForVarID),        % in the future consider iterating over all values, but in order to
  AllowedPositionsForVarID=[FirstValueIndex|_],                     % do that effectively, it's fundamental that the most promising variable
  arg(FirstValueIndex, InitialDomain, Var).                         % first returns all variables that have impact. No impact variables must be the last to be returned  
solve_independent_component(ceval(ClauseInfo, VarsInfo, PairwiseVarInters), CurVarsAllowedPos, VarsInComponent):-
  choose_most_promising_variable(VarsInComponent, VarsInfo, CurVarsAllowedPos, VarID),
  arg(VarID, VarsInfo, vinfo(Var, VarID, VInters, InitialDomain)),
  clause_components(VarsInfo, VarsInComponent, VarID, Components), % this line does the once_transformation
  %ord_del_element(VarsInComponent, VarID, RVarsInComponent), Components=[RVarsInComponent],  % this line disable once transformation and does only cut-transformation
  arg(VarID, CurVarsAllowedPos, _NumAllowed-AllowedPositionsForVarID),
  iterate_over_var_domain(AllowedPositionsForVarID, Var, InitialDomain, VarValueIndex),
  update_neighbours_domain(VarID, VarValueIndex, ceval(ClauseInfo, VarsInfo, PairwiseVarInters), VInters, CurVarsAllowedPos, NewVarsAllowedPos), % this is expensive!
  checklist(solve_independent_component(ceval(ClauseInfo, VarsInfo, PairwiseVarInters), NewVarsAllowedPos), Components).

%  iterate_over_var_domain(+AllowedPositionsForVarID, +Var, +InitialDomain, -VarValueIndex)
iterate_over_var_domain([ValueIndex|_], Var, InitialDomain, ValueIndex):-
  arg(ValueIndex, InitialDomain, Var).
iterate_over_var_domain([_|T], Var, InitialDomain, ValueIndex):-
  iterate_over_var_domain(T, Var, InitialDomain, ValueIndex).
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  choose_most_promising_variable(+VarsInComponent, +VarsInfo, +CurVarAllowedPos, -VarID)
%
% Given:
%   VarsInComponent: non empty list of the variables ids in the current component
%   VarsInfo: see main data structures
%   CurVarAllowedPos: a term vars_allowed_pos(AllowedPos1, .., AllowedPosN) with the variable positions allowed currently
%
% Returns:
%  VarID: The variable ID from VarsInComponent which has the smallest domain (this may later be changed to more sophisticated heuristics)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

choose_most_promising_variable(VarsInComponent, _VarsInfo, CurVarAllowedPos, BestVarID):- % pick variable with smallest domain t=5s
  choose_smallest_domain_variable(VarsInComponent, CurVarAllowedPos, inf, _, BestVarID).

%choose_smallest_domain_variable(+VarsID, +CurVarAllowedPos, +CurShortestDomainSize, +CurBestVarID, -BestVarID)
choose_smallest_domain_variable([], _, _, VarID, VarID).
choose_smallest_domain_variable([VarID|VarIDs], CurVarAllowedPos, CurShortestDomainSize, CurBestVarID, BestVarID):-
  arg(VarID, CurVarAllowedPos, DomainSize-_PositionsAllowed),
  (DomainSize<CurShortestDomainSize ->
     choose_smallest_domain_variable(VarIDs, CurVarAllowedPos, DomainSize, VarID, BestVarID)
   ;
     choose_smallest_domain_variable(VarIDs, CurVarAllowedPos, CurShortestDomainSize, CurBestVarID, BestVarID)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% clause_components(+VarsInfo, +VarIDsToConsider, +VarIDAboutToBeGround, -IndependentComponents)
%
% Given:
%  VarsInfo: a term varsinfo/N (N=#distinct variables in hypothesis), of the form: varsinfo(vinfo1, ..., vinfoN), where at the i-th position
%                there is a vinfo/4 term with information on the i-th variable.
%  VarIDsToConsider: ordered list of variable ids to consider (from VarsInfo) (they are guaranteed to be all free variables)
%  VarIDAboutToBeGround: variable id to ignore when computing the variables interactions. This is the variable that is about to get ground. (it's not a list, is a single number)
%                                          This variable id is in VarIDsToConsider list. If there is no variable id about to be ground, any term not a positive number should be entered.
%                                          (e.g. 'none', '0')
%
% Returns:
%   IndependentComponents: list of indepenent components. Each component is the (sorted) list of variables ids in it.
%                           Two varibles belong to the same component if there is a non ground path of variables connecting them.
%
% Example:
%    example_components(Components):-
%      VInfo1 = vinfo(a1, 1, [2,3], idom(a1,a2,a3)),
%      VInfo2 = vinfo(B, 2, [1], idom(b1,b2,b3)),
%      VInfo3 = vinfo(C, 3, [1,4], idom(c1,c2,c3)),
%      VInfo4 = vinfo(D, 4, [3], idom(d1,d2,d3)),
%      VarsInfo=varsinfo(VInfo1, VInfo2, VInfo3, VInfo4),
%      VarsToConsider=[1,2,3,4],
%      VarIDToBeGround=1,
%      clause_components(VarsInfo, VarsToConsider, VarIDToBeGround, Components).
%
% Components = [[2],[3,4]]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clause_components(VarsInfo, VarsToConsider, VarIDToBeGround, Components):-
  convlist(construct_ground_var_interaction(VarsInfo, VarIDToBeGround), VarsToConsider, VarInteractions),
  find_all_components(VarInteractions, VarsList),
  % sort components according to their lengths, shortest ones first
  % we could potentially refine this by sorting the components by their worst case complexity (which is given by the product of the variables)
  custom_qsort(VarsList, smaller_list, Components). 

%smaller_list(-Result, +List1, +List2)
smaller_list(<, L1, L2):-
  length(L1, N1),
  length(L2, N2),
  N1<N2,!. % this cut is essential as otherwise we would leave a choice point opened
% we do not want equality, otherwise components which happen to have the same length (i.e. number of variables) would be pruned
smaller_list(>, _, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% construct_ground_var_interaction(+VarsInfo, +VarIDToBeGround, +VarID, -VarInteraction)
%
% Given:
%   VarsInfo: a varsinfo/N term as described in the header of this file
%   VarIDAboutToBeGround: variable id to ignore when computing variables interactions. This is the variable that is about to get ground.
%   VarID: a variable ID to compute its interactions
%
% Returns:
%   VarInteraction: a term of the form: vinter(VarID, Interactions)
%                           where Interactions is an ordered list of (non ground) variables ids with whom VarID interacts
%
% Notes:
%   VarInteraction is an auxiliary datastructure to facilitate computing the clause components graph
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_ground_var_interaction(VarsInfo, VarIDToBeGround, VarID, vinter(VarID, GroundVarIDInters)):-
  VarIDToBeGround\=VarID,
  arg(VarID, VarsInfo, vinfo(_Var, VarID, Inters, _Domain)),
  free_vars(Inters, VarsInfo, VarIDToBeGround, GroundVarIDInters). % discard ground interactions, this is about 20-25% faster than selectlist/3
                                                                   % which has an impact of ~5% in the total subsumption speed!
  %selectlist(free_var(VarsInfo, VarIDToBeGround), Inters, GroundVarIDInters). % discard ground interactions
  
%free_var(+VarsInfo, +VarIDToBeGround, +VarID)
%free_var(VarsInfo, VarIDToBeGround, VarID):-
%  VarIDToBeGround\=VarID,
%  arg(VarID, VarsInfo, vinfo(Var, VarID, _Inters, _Domain)),
%  var(Var).

%free_vars(+Inters, +VarsInfo, +VarIDToBeGround, -GroundVarIDInters)
free_vars([], _VarsInfo, _VarIDToBeGround, []).
free_vars([VarID|InterIDs], VarsInfo, VarIDToBeGround, GroundVarIDInters):-
  ((VarIDToBeGround\=VarID,
    arg(VarID, VarsInfo, vinfo(Var, VarID, _Inters, _Domain)),
    var(Var)) ->
      GroundVarIDInters=[VarID|RemainGroundVarIDInters],
      free_vars(InterIDs, VarsInfo, VarIDToBeGround, RemainGroundVarIDInters)
   ;
      free_vars(InterIDs, VarsInfo, VarIDToBeGround, GroundVarIDInters)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% find_all_components(+VarInteractions, -VarsList)
%
% Given:
%   VarInteractions: list of var interactions terms: vinter(VarID, VInterIDs).
%
% Returns:
%   VarsList: list of components. Each component is an ordered list of variable ids. Each variable id belongs to a different component
%             of the clause graph
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

find_all_components([], []):- !.
find_all_components(VarInteractions, [VarsInComponent|RemainVarsList]):-
  find_component(VarInteractions, VarsInComponent, RemainVarInteractions),
  find_all_components(RemainVarInteractions, RemainVarsList).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% find_component(+VarInteractions, -VarsInComponent, -RemainVarInteractions)
%
% Given:
%   VarInteractions: a non-empty list of var interactions terms: vinter(VarID, VInterIDs).
%
% Returns:
%   VarsInComponent: list of variables appearing in a component
%   RemainVarInfos: VarInteractions with vinters corresponding to VarsInComponent removed
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

find_component([vinter(VarID, VInter)|VInters], VarsInComponent, RemainVarInters):-
  find_component_aux(VInter, [VarID], VarsInComponent, VInters, RemainVarInters).

%find_component_aux(+VariableIDsToAddToComponent, +CurVarIDsInCompoment,
%                                  -FinalVarIDsInComponent, +CurVarsInteractions, -RemainVarsInteractions)
find_component_aux([], VarIDsInComponent, VarIDsInComponent, VarsInters, VarsInters):- !.
find_component_aux(VarsToAdd, CurVars, FVarsComp, CurVarsInters, RemainVarsInters):-
  varsinter_for_vars(VarsToAdd, CurVarsInters, VarsToAdd_VarInters, NVarsInters),
  get_vars_to_add(VarsToAdd_VarInters, TVarsToAdd), % TVarsToAdd: variables to visit next
  ord_union(VarsToAdd, CurVars, NCurVars),          % NCurVars: variables already visited so far
  ord_subtract(TVarsToAdd, NCurVars, NVarsToAdd),   % NVarsToAdd: unseen variables to visit next
  find_component_aux(NVarsToAdd, NCurVars, FVarsComp, NVarsInters, RemainVarsInters).

% get_vars_to_add(+VarsToAdd_VarInters, -VarsToAdd)
get_vars_to_add(VarsToAdd_VarInters, VarsToAdd):-
  get_vars_to_add(VarsToAdd_VarInters, [], VarsToAdd).

% get_vars_to_add(+VarsToAdd_VarInters, +CurVarsToAdd, -NVarsToAdd)
get_vars_to_add([], VarsToAdd, VarsToAdd).
get_vars_to_add([vinter(_Var, VInter)|VsInters], CurVarsToAdd, FinalVarsToAdd):-
  ord_union(CurVarsToAdd, VInter, NextVarsToAdd),
  get_vars_to_add(VsInters, NextVarsToAdd, FinalVarsToAdd).

%varsinter_for_vars(+Vars, +VarsInteractions, -VarsVarInteractions, -RemainVarsInteractions)
varsinter_for_vars([], VarsInters, [], VarsInters):-!.
varsinter_for_vars([VarA|Vars], [vinter(VarB, VarInters)|VsInters], [vinter(VarB, VarInters)|VVInters], RemainVarsInters):-
  VarA==VarB,!,
  varsinter_for_vars(Vars, VsInters, VVInters, RemainVarsInters).
varsinter_for_vars(Vars, [VInter|VsInters],  VarsVarInters, [VInter|RemainVVInters]):-
  %VInter head is smaller than Vars head
  varsinter_for_vars(Vars, VsInters, VarsVarInters, RemainVVInters).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_clause_eval_term(+Hypothesis, +Example, -CEvalTerm, -VarsAllowedPos)
%
% Given:
%   Hypothesis: a list of literals 
%   Example: example as a list of ground literals
%
% Returns:
%   CEvalTerm: a term of the form: ceval(ClauseInfo, VarsInfo, PairwiseVarInters) (see main datastructures)
%   VarsAllowedPos: see main datastructures
%
% Notes:
%  Binding the hypothesis head with the example is quite important as it reduces very significantly the amount of work that needs to be done to
%  CEvalTerm (this is specially true is many literals in the body of Hypothesis have the head input variables).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_clause_eval_term([Head|HypBody], [Head|ExBody], ceval(ClauseInfo, VarsInfo, PairwiseVarInters), VarsAllowedPos):-
  preprocess_hypothesis([Head|HypBody], PLitsInfo, VarPredCalls, UniqPredCalls, PairwiseVarInters, FullVarInters),
  %Note that we could match the hypothesis Head and the example head after preprocess_hypothesis and it would still work
  preprocess_example(ExBody, CondensedExampleBody),
  compute_predcall_domain(UniqPredCalls, CondensedExampleBody, UniqPredCallDomain),
  compute_variables_domain(UniqPredCallDomain, VarPredCalls, VarsDomain),
  compute_clause_info(PLitsInfo, CondensedExampleBody, UniqPredCallDomain, VarsDomain, ClauseInfo),
  create_variables_info(VarsDomain, FullVarInters, VarsInfo, VarsAllowedPos).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_predcall_domain(+UniqPredCalls, +CondensedExampleBody, -PredCallDomain)
%
% Given:
%  UniqPredCalls: see preprocess_hypothesis/6
%
% Returns:
%  PredCallDomain: list where each element is of the form: (Name/Arity,LitArgs)-VarValues
%                  VarValues is a sorted list of terms: (Value-Positions) where Value is a possible value for the implicit 
%                  variable '$VAR'(0) of LitArgs and positions are the positions in the LitArgs argument where it occurs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_predcall_domain([], _, []).
compute_predcall_domain([Pred1-CallModes|UPCalls], [Pred2-_|CEB], PredCallDomain):-
  Pred1@>Pred2,!,%Pred2 only exists in Example, not in hypothesis
  compute_predcall_domain([Pred1-CallModes|UPCalls], CEB, PredCallDomain).
compute_predcall_domain([Pred-CallModes|UPCalls], [Pred-PredDomain|CEB], PredCallDomain):-
  maplist(add_pred_domain_aux(Pred, PredDomain), CallModes, CurCallModesDomain),
  append(CurCallModesDomain, RPredCallDomain, PredCallDomain),
  compute_predcall_domain(UPCalls, CEB, RPredCallDomain).

%add_pred_domain_aux(+Name/Arity, +PredDomain, +LitArgs, -((Name/Arity,LitArgs)-VarDomain))% VarDomain is the domain of '$VAR'(0) from LitArgs
add_pred_domain_aux(Name/Arity, PredDomain, LitArgs, (Name/Arity, LitArgs)-PlaceHolderVarDomain):- 
  undo_skolemize(('$VAR'(0), LitArgs), (PlaceHolderVar, CallArgs)),
  var_domain(PlaceHolderVar, CallArgs, PredDomain, PlaceHolderVarDomain).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% var_domain(+Var, +LiteralArgs, +AllLiteralArgValues, -Domain) %Var occurs in LiteralArgs
%
%
% Returns:
%   Domain: a ordered list where each term is of the form: Value-Positions (1-based relative to AllLiteralArgValues)
%           where Positions is a ordered list of integers. E.g. [a-[2,3,5,7],b-[1,4,6,8]]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

var_domain(Var, LitArgs, AllLiteralArgValues, Domain):-
  find_domain_positions(AllLiteralArgValues, 1, Var, LitArgs, LVPos), % if Var is ground we could do with a simpler findall
  %findall(Var-Pos, nth(Pos, AllLiteralArgValues, LitArgs), LVPos), % Var occurs in LitArgs somewhere
  append_keys(LVPos, Domain). % we cannot assume LVPos to be already keysorted because Var may not be the first argument of LitArgs
                              % there is no need to sort the value (Pos) because it's already sorted

%find_domain_positions(+AllLiteralArgValues, +CurPos, +Var, +LitArgs, -DomainPositions)
find_domain_positions([], _, _, _, []).
find_domain_positions([ArgValues|T], CurPos, Var, LitArgs, DomainPositions):- 
  NCurPos is CurPos+1,
  (ArgValues\=LitArgs -> % we don't do equal here to save a copy_term/2
      find_domain_positions(T, NCurPos, Var, LitArgs, DomainPositions)
    ;
      copy_term((Var, LitArgs), (NVar, NLitArgs)),
      ArgValues=LitArgs, %This binds Var as well
      DomainPositions=[Var-CurPos|RDomainPositions],
      find_domain_positions(T, NCurPos, NVar, NLitArgs, RDomainPositions)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_clause_info(+PartialLitsInfo, +CondensedExampleBody, +UniqPredCallDomain, +VarsDomain, -ClauseInfo)
%
% Given:
%   PartialLitsInfo: see preprocess_hypothesis/6
%   Hypothesis: hypothesis as a list of literals (including head)
%   VarsDomain: see auxiliar datastructures. E.g. [vdomain(A, [1,3,4], [a,b,c,d,e,f]), vdomain(B, [2,4,5], [1,5,6,7,8]), ...]
%   UniqPredCallDomain: see main datastructures
%
% Returns:
%   ClauseInfo: see main datastructures
%
% Notes:
%   The time complexity of this predicate can be improved from its current O(NumLiterals*NumVariables per literal) to
%   O(Num distinct variables in clause).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_clause_info([HeadPLInfo|BodyPLitsInfo], CondensedExampleBody, UniqPredCallDomain, VarsDomain, ClauseInfo):-
  list_to_rbtree(UniqPredCallDomain, RB_UniqPredCalls), % notice that in general we cannot use ord_list_to_rbtree here!
  % the reason is subtle: it's when we have more than one variable in the head and we are subsuming the examples all at once
  % (i.e. given their ids, not given their ground bottoms). In this case the UniqPredCallDomain structure just gets bound
  % after computation and it may not be sorted
  VarsID_Domain=..[varsdomain|VarsDomain],
  term_variables(HeadPLInfo, HeadVars),
  list_to_ord_set(HeadVars, SHeadVars),
  maplist(create_literal_info(CondensedExampleBody, RB_UniqPredCalls, VarsID_Domain, SHeadVars), BodyPLitsInfo, FullLitsInfo),
  ClauseInfo=..[cinfo|[HeadPLInfo|FullLitsInfo]]. % same as [cinfo,LitHeadInfo|LitsBodyInfo], head is a plinfo, does not need to be updated

%create_literal_info(+CondensedExampleBody, +Var2ID, +RB_UniqPredCalls, +VarsDomain, +SortedHeadVars, +PLInfo, -LitInfo)
create_literal_info(CondensedExampleBody, RB_UniqPredCalls, VarsDomain, SHeadVars, plinfo(Pred, LitArgs, LitVars), linfo(Pred, LitArgs, LitVars, LitIndex, LitValues)):-
  memberchk(Pred-Values, CondensedExampleBody),
  LitValues=..[values|Values],
  (LitVars=[] ->
     has_compatible_binding(Values, LitArgs), LitIndex=[]
    ;
     create_literal_index(LitVars, LitArgs, Pred, VarsDomain, RB_UniqPredCalls, SHeadVars, LitIndex)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% has_compatible_binding(+LitValues, +LitArgs)
%
% Notes: this test only needs to be performed if LitArgs if fully ground  (i.e. LitVars=[])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

has_compatible_binding([LitValue|_], LitArgs):-
  \+(\+(LitArgs=LitValue)),!. % don't bind variables!
has_compatible_binding([_|T], LitArgs):-
  has_compatible_binding(T, LitArgs).
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_literal_index(+LitVarIDs, +LitArgs, +LitName/Arity, +VarsDomain, +RB_UniqPredCall, +SortedHeadVars, -LitIndex)
%
% Given:
%
%
% Returns:
%   LitIndex: list where each element is of the form: (there are LitVars elements)
%                 VarID-ValueInfoPos where ValueInfoPos is a term values/N (N maximum values for Var)
%                 where at position I we have the list of positions (relative to LitValues) where Var appears in LitValues,
%                 when the value of Var is it's Ith value
%                  (corresponding to the value at position I in var value domain term)
%
%  Example: 
%   LitVarIDs = [2,4] %B=2, D=4
%   LitArgs = [f(B),D]
%   LitValues : [[f(a),g], [f(c),g], [f(a),g], [f(b),h], [f(a),f]]
%   VarsDomain: varsdomain(vdomain(A, [1,3], [x,y,z]),vdomain(B, [1,2,3], [a,b,c]),vdomain(C, [1], [7,8]), vdomain(D, [1,2,3], [f,g,h])).
%
%   LitIndex: [2-vpos([1,3,5],[4],[2]),4-vpos([5],[1,2,3],[4])]
%
% Notes:
%  The complexity for create_literal_index/6 is NV*(log2(UniqPredCalls) + max_var_domain)
%
%  Where NV is length(LitVarIDs) and max_var_domain is the length of the domain of the variable with largest domain
%
%  This complexity is quite acceptable. A naive implementation would be PD*max(VarsDomain)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_literal_index([], _LitArgs, _LitDesc, _VarsDomain, _RBUniqPredCall, _SHeadVars, []).
create_literal_index([VarID|LitVarIDs], LitArgs, LitDesc, VarsDomain,  RBUniqPredCall, SHeadVars, [VarID-VIndex|RIndex]):-
  arg(VarID, VarsDomain, vdomain(Var, _AllowedPos, InitialVarDomain)),
  %write(create_var_index(Var, InitialVarDomain, LitArgs, LitDesc, VIndex)),nl,
  create_var_index(Var, InitialVarDomain, LitArgs, LitDesc, RBUniqPredCall, SHeadVars, VIndex),
  %write(VIndex),nl,
  create_literal_index(LitVarIDs, LitArgs, LitDesc, VarsDomain, RBUniqPredCall, SHeadVars, RIndex).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_var_index(+Var, +InitialVarDomain, +LitArgs, +(LitName/Arity), +RBUniqPredCall, +SortedHeadVars, -VarIndex)
%
%
% Notes:  The worst case complexity of this predicate is: log2(UniqPredCalls) + InitialVarDomain
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_var_index(Var, InitialVarDomain, LitArgs, LitName/Arity, RBUniqPredCall, SHeadVars, Index):-
  skolemize_ignoring((Var, LitArgs), SHeadVars, (_VarSkolem, ArgsSkolem)), %VarSkolem is always '$VAR'(0), this is here to ensure '$VAR'(0) appears in the correct place
  rb_lookup((LitName/Arity, ArgsSkolem), ValuesForVarWithPos, RBUniqPredCall),
  create_var_index_args(ValuesForVarWithPos, InitialVarDomain, VarIndexArgs),
  Index=..[vpos|VarIndexArgs].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_var_index_args(+ValuesForVarWithPos, +InitialVarDomain, -VIndexArgs)
%
% Given:
%  ValuesForVarWithPos: list where each term is of the form: Value-ListOfPositions (relative to the possible values for the predicate in cause)
%                                      where Value appears (as a possible substitution for Var). E.g. [a-[1,4,5],b-[3,6,7],d-[2,4]]
%  InitialVarDomain: the domain of a variable (an ordered list of values). E.g. [a,b,c,d]
%
% Returns:
%   VIndexArgs: list of arguments for a variable index (has length VarDomain) values. E.g. [[1,4,5],[3,6,7],[],[2,4]]
%                      (meaning that the 1st value for VarDomain appears at position 5, the 2nd appears at positions 1,4, the 3rd at positions 6,7.
%                       (positions are relative to the possible values for the arguments of the predicate in cause)
%
% Notes:
%   All values in ValuesForVarWithPos are guaranteed to appear in VarDomain (but not the other way round).
%   The complexity of this predicate is: O(#InitialVarDomain)
%
% Example:
%   ValuesForVarWithPos=[a-[1,4,5],b-[3,6,7],d-[2,4]],
%   VarDomain=[a,b,c,d],
%   create_var_index_args(ValuesForVarWithPos, VarDomain, VIndexArgs),
%   VIndexArgs=[[1,4,5],[3,6,7],[],[2,4]]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_var_index_args([], Vals, Args):-
  maplist(create_empty_list, Vals, Args).
create_var_index_args([ValA-Pos|VPos], [ValB|Vals], IArgs):-
  (ValA==ValB ->
     IArgs=[Pos|RArgs],
     create_var_index_args(VPos, Vals, RArgs)
   ;%ValA@>ValB
     IArgs=[[]|RArgs],
     create_var_index_args([ValA-Pos|VPos], Vals, RArgs)
  ).

%create_empty_list(+Val, -EmptyList)
create_empty_list(_Val, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_variables_info(+VarsDomain, +FullVarInters, -VarsInfo, -VarsAllowedPos)
%
% Given:
%   VarsDomain: see auxiliary datastructures
%   FullVarInters: list where each term is a (Var-IntersIDs), where IntersIDs is a sorted list with the ids of the variables with whose Var interacts
%
% Returns:
%   VarsInfo: see main datastructures
%   VarsAllowedPos: see main datastructures
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_variables_info(VarsDomain, FullVarInters, VarsInfo, VarsAllowedPos):-
  create_variables_info_aux(VarsDomain, FullVarInters, VarsInfoArgs, VarsAllowedPosArgs), % we don't need Var2Id because variables are in the same order in VarsDomain and FullVarInters
  VarsInfo=..[varsinfo|VarsInfoArgs],
  VarsAllowedPos=..[vars_allowed_pos|VarsAllowedPosArgs].

% create_variables_info_aux(+VarsDomain, +FullVarInters, -VarsInfoArgs, -VarsAllowedPosArgs)
create_variables_info_aux([], [], [], []).
create_variables_info_aux([vdomain(Var, AllowedPos, Domain)|RDomains], [VarID-VInters|RInters], [vinfo(Var, VarID, VInters, IDomain)|R1], [Len-AllowedPos|R2]):-
  IDomain=..[idom|Domain],
  length(AllowedPos, Len),
  create_variables_info_aux(RDomains, RInters, R1, R2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% preprocess_example(+ExampleBody, -CondensedExampleBody)
%
% Given:
%  ExampleBody: a list of all ground facts to be known about example (except its head)
%
% Returns:
%  CondensedExampleBody: a list where each argument is a distinct predName/Arity is put in evidence followed by a list of all possible values for the predicate
%                                            Each element is of the form: predName/Arity-PredicateArgValues
%
% Notes:
%  We assume there are no duplicate literals in the Example (as there won't if Example is generated from a ground bottom clause).
%  If there are one should use merge_keys/2 instead of append_keys/2, otherwise, to speed preprocess an example by a few % we can incur
%  in runtime overhead due to considering repeated literal values.
%
% Example:
%   ExampleBody=[b0(a,b,c),b1(a,d,x), b0(a,g, h), b1(a,e, f)]
%   CondensedExampleBody= [b0/3-[[a,b,c], [a,g,h]], ,b1/3-[[a,d,x], [a,e, f]]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

preprocess_example(ExBody, CondensedExampleBody):-
  maplist(pred2nameArityArgs, ExBody, MappedExBodyLiterals),
  append_keys(MappedExBodyLiterals, CondensedExampleBody). %we do not need to merge_keys as there are no duplicate literals in ExBody
  %merge_keys(MappedExBodyLiterals, CondensedExampleBody).

%pred2nameArityArgs(+Literal, -MappedLiteral)
pred2nameArityArgs(Literal, Name/Arity-Args):-
  functor(Literal, Name, Arity),
  Literal=..[Name|Args].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% preprocess_hypothesis(+Hypothesis, -PartialLitsInfo, -VarPredicateCalls, -UniqPredCalls, -PairwiseVarInters, -FullVarInters)
%
% Given:
%  Hypothesis: lists of literals representing an hypothesis (head is present)
%  
% Returns:
%  PartialLitsInfo: list of terms: plinfo(Name/Arity, Args, Vars)
%  VarPredicateCalls: sorted list where each element is of the form: Var-VarUniqLitArgsCall where 
%                     VarUniqLitArgsCall is a list where each element is of the form:
%                        Pred/Arity-Args, where Args is the list of all the unique* arguments of predicates having Var as argument
%     unique*= after skolemization). ('$VAR'(0) is the skolemized variable that matters for the variable in cause)
%
%           Sample VarPredicateCalls: [B-[br0/3-[[$'VAR'(1),$'VAR'(0),$'VAR'(2)],[$'VAR'(1),$'VAR'(2),$'VAR'(0)])], ... ]
%
%  UniqPredCalls: list of unique predicate calls.E.g.[br0/3-[[$'VAR'(1),$'VAR'(0),$'VAR'(2)],[$'VAR'(1),$'VAR'(2),$'VAR'(0)]]]
%
%  PairwiseVarInters: rb tree where each element is of the form (VarID1,VarID2)  where VarID1 and VarID2 are variables that interact.
%                      The value is the list of positions (relative to HypBody) where VarID1 and VarID2 share a predicate (first literal of the body is position 2)
%                     Example in list format:  [(1,1)-[1,2,3,4],(1,2)-[2,4,5],(1,3)-[3,4,5],(2,3)-[4,5]]
%
%  FullVarInters: a list where each element is of the form: VarID-ListInteractions, where ListInteractions is the sorted list of all variables ID with whom VarID interacts
%                      E.g. [1-[2,3,4,5,6], 2-[1,3,4], 3-[1,2,4], 4-[1,2,3], ...]
%
% Notes:
%   The rationale for this predicate is that we only need, for each variable, the predicate information where it appears. E.g. if a variable B appears several times as
%   the second variable of a pred (e.g. br4(A,B,C), br4(A,B,D)), we don't care what the neighbouring variables are.
%   The LitInfo for the head is never used so we don't bother computing it.
%   Preprocessing the hypothesis is a bit complex because the Head of the Hypothesis may be free but we still want the datastructures to be in a state that
%   as soon as we match the head's variables its as if the head was matched before calling this predicate. This allows for a more efficient batch subsumption.
%   (i.e. constant hypothesis, set of different examples)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

preprocess_hypothesis([Head|Body], [linfo(Head)|PartialLitsInfo], VarPredicateCalls, UniqPredCalls, PairwiseVarInters, FullVarInters):-
  term_variables(Head, HeadVars),
  list_to_ord_set(HeadVars, SHeadVars),
  process_hyp_literals(Body, SHeadVars, 2, TPLitsInfo, TVarPredicateCalls, TPairwiseVarInters), % 2 because first literal is the head which is not being passed
  merge_keys(TVarPredicateCalls, VarPredicateCalls),
  create_var2ID(VarPredicateCalls, Var2ID),
  create_var_inters(TPairwiseVarInters, Var2ID, PairwiseVarInters, FullVarInters),
  get_uniq_predcalls(TVarPredicateCalls, UniqPredCalls), %notice that it's TVarPredicateCalls and not VarPredicateCalls
  maplist(update_partial_litsinfo(Var2ID), TPLitsInfo, PartialLitsInfo). % to convert Vars to VarIDs

% create_var2ID(+VarPredicateCalls, -Var2ID)
create_var2ID(VarPredicateCalls, Var2ID):-
  create_var2ID_aux(VarPredicateCalls, 1, VarIDs),
  ord_list_to_rbtree(VarIDs, Var2ID). % because VarPredicateCalls were already sorted by variable

create_var2ID_aux([], _, []).
create_var2ID_aux([Var-_PredCalls|VPs], N, [Var-N|R]):-
  N1 is N+1,
  create_var2ID_aux(VPs, N1, R).

%update_partial_litsinfo(+Var2ID, +PartialLitInfo, -PartialLitInfoWithIDs)
update_partial_litsinfo(Var2ID, plinfo(Pred, Args, Vars), plinfo(Pred, Args, VarIDs)):-
  maplist(convert_to_var_id(Var2ID), Vars, VarIDs).

%convert_to_var_id(+Var2ID, +Var, -VarID)
convert_to_var_id(Var2ID, Var, VarID):-
  rb_lookup(Var, VarID, Var2ID).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% create_var_inters(+TempPairwiseVarInters, +Var2ID, -PairwiseVarIDInters, -FullVarInters)
%
% Given:
%   TempPairwiseVarInters: list where each term is (Var1,Var2)-Position (just a position, not a list of positions!)
%
% Returns:
%   PairwiseVarIDInters: RB tree where each key is (VarID1, VarID2) and value is the list of positions where VarID1 and VarID2 interact 
%   FullVarInters: a list where each element is of the form: Var-ListInteractions, where ListInteractions is the sorted list of all variables IDs with whom Var interacts
%                       E.g. [A-[2,3,4,5,6], B-[1,3,4], C-[1,2,4], D-[1,2], E-[1,3], F-[1]]
%
% Notes:
%   There may be variables that do not interact with any variable but still need to be considered. (E.g. hyp=[p(X),q(X,Y)], 
%   Y will interact with no variables since X will get bound upon matching with the example head
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_var_inters(TempPairwiseVarInters, Var2ID, PairwiseVarIDInters, FullVarInters):-
  complete_and_convert_to_var_id(TempPairwiseVarInters, Var2ID, TempPairwiseVarIDInters),
  create_var_inters_aux(TempPairwiseVarIDInters, PairwiseVarIDInters, FullVarInters).

%create_var_inters_aux(+TempPairwiseVarIDInters, -PairwiseVarIDInters, -FullVarInters)
create_var_inters_aux(TempPairwiseVarIDInters, PairwiseVarIDInters, FullVarInters):-
  maplist(prepare_full_var_inters, TempPairwiseVarIDInters, TFullVarInters), % the value removed is the position
  merge_keys(TFullVarInters, MFullVarInters),
  maplist(remove_empty_list, MFullVarInters, FullVarInters),
  merge_keys(TempPairwiseVarIDInters, MPairwiseVarIDInters),
  ord_list_to_rbtree(MPairwiseVarIDInters, PairwiseVarIDInters).

%complete_and_convert_to_var_id(+TempPairwiseVarInters, +VarToID, -TempPairwiseVarIDInters)
complete_and_convert_to_var_id([], _, []).
complete_and_convert_to_var_id([(Var1,Var2)-Pos|T1], VarToID, TempPairwiseVarIDInters):-
  rb_lookup(Var1, Var1ID, VarToID),
  (Var1==Var2 ->
    TempPairwiseVarIDInters=[(Var1ID, Var1ID)-Pos|T2]
  ;
    rb_lookup(Var2, Var2ID, VarToID),
    TempPairwiseVarIDInters=[(Var1ID, Var2ID)-Pos,(Var2ID, Var1ID)-Pos|T2]
  ),
  complete_and_convert_to_var_id(T1, VarToID, T2).

%remove_empty_list(+VarID-Inters, -VarID-RInters) %an empty list in Inters represents the interaction of the variable with itself
remove_empty_list(VarID-Inters, VarID-RInters):-
  delete(Inters, [], RInters). %delete the empty list element

%prepare_full_var_inters(+((VarID1,VarID2)-Pos), -(VarID1-VarID2))
prepare_full_var_inters((VarID1,VarID1)-_Pos, VarID1-[]):-!.
prepare_full_var_inters((VarID1,VarID2)-_Pos, VarID1-VarID2). %:-VarID1\=VarID2

%get_uniq_predcalls(+VarPredCalls, -UniqPredCalls)
get_uniq_predcalls(VarPredCalls, UniqPredCalls):-
  maplist(remove_key, VarPredCalls, TVarPredCalls),
  merge_keys(TVarPredCalls, UniqPredCalls).

%remove_key(-(Var-PredCalls), +VarPredCalls).
remove_key(_Var-PredCalls, PredCalls).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% process_hyp_literals(+HypBodyLits, +HeadVariables, +CurIndex, -PartialLitsInfo, -RawVarPredCalls, -PairwiseVarInters)
%
% Given:
%   HypBodyLits: list of literals in hypothesis
%   HeadVariables: ordered list of the variables in the head of hypothesis
%   CurIndex: Index of the first literal in HypBodyLits
% 
% Returns:
%  PartialLitsInfo: list of partial literal info, each of the form: plinfo(Name/Arity, Args, Vars)
%  VarPredCalls: a list of terms: Var-(Name/Arity-ArgsSkolem), for each Var in each predicate (with Name/Arity)
%  PairwiseVarInters: a list of terms (V1,V2)-Position, where V1 and V2 are variables and Position is the literal position 
%                     (relative to hypothesis) where they interact.  E.g. (A,B)-3, (B,A)-3, (C,D)-4
%                     Note that when we have (V1,V1)-Pos, then Pos is a position where Var appears
%
% Notes:
%  Variables in a literal are skolemized ignoring the head variables because we want to be able to bind those variables later on.
%  This allows for precomputing the hypothesis datastructure before knowning the actual example beforehand
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

process_hyp_literals([], _HVars, _Index, [], [], []).
process_hyp_literals([Lit|Lits], HVars, Index, [plinfo(Name/Arity, Args, RVars)|PLInfos], VACalls, PVIs):-
  Lit=..[Name|Args],
  length(Args, Arity),
  term_variables(Args, Vars), % ArgsVars includes head variables which will later get bound
  list_to_ord_set(Vars, SVars),
  ord_subtract(SVars, HVars, RVars), % RVars stands for Real Variables (the variables in literal not appearing in the head)
  maplist(construct_var_call(Name/Arity, Args, HVars), RVars, VACall), % E.g. Lit=br0(A,B,C), VACall= [A-(br0/3-['$VAR'(0),'$VAR'(1),'$VAR'(2)]), B-(br0/3-['$VAR'(1),'$VAR'(0),'$VAR'(2)]), C-(br0/3-['$VAR'(1),'$VAR'(2),'$VAR'(0)])]
  append(VACall, RemainVACalls, VACalls),
  create_pairwise_var_inters(RVars, Index, LitPVI),
  append(LitPVI, RemainPVIs, PVIs),
  Index1 is Index+1,
  process_hyp_literals(Lits, HVars, Index1, PLInfos, RemainVACalls, RemainPVIs).

%construct_var_call(+Name/Arity, +Args, +HeadVars, +Var, +VarArgsCall).
construct_var_call(Name/Arity, Args, HeadVars, Var, Var-(Name/Arity-ArgsSkolem)):-
  skolemize_ignoring((Var, Args), HeadVars, (_VarSkolem, ArgsSkolem)). %VarSkolem is always '$VAR'(0), this is here to ensure '$VAR'(0) appears in the correct place

% create_pairwise_var_inters(+RemainVars, +Index, -LitPVI)
create_pairwise_var_inters([], _, []).
create_pairwise_var_inters([Var|RemainVars], Index, PVIs):-
  maplist(create_varinteraction_pair(Var, Index), [Var|RemainVars], VPair),
  append(VPair, RemainPVIs, PVIs),  
  create_pairwise_var_inters(RemainVars, Index, RemainPVIs).

create_varinteraction_pair(VarA, Index, VarB, (VarA, VarB)-Index).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% process_hypothesis_body(+HypBody, +SummarizedExampleBodyLiterals, +CurVarsInfo, -FinalVarsInfo),
%
% Given:
%  HypBody: body of an hypothesis as a list of literals (head is not present)
%  SummarizedExampleBodyLiterals: list of body literals of an example given in a compressed form. Each element of this list is a term: (PredName/Arity-ListOfValues)
%                                   where:
%                                       PredName: is the predicate name of a literal in example body
%                                       Arity: number of arguments of the predicate
%                                       ListOfValues: ordered list of all the possible values for the given predicate (each element of this list has length Arity)
%                                   notes: PredName/Arity are a key and do not appear repeated
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

process_hypothesis_body([], _, VarsInfo, VarsInfo).
process_hypothesis_body([Lit|Lits], SummarizedExBodyLiterals, CurVarsInfo, FinalVarsInfo):-
  functor(Lit, Name, Arity),
  member((Name/Arity-ArgValues), SummarizedExBodyLiterals),!,
  Lit=..[Name|Args],
  update_vars_info(Args, ArgValues, CurVarsInfo, NCurVarsInfo),
  process_hypothesis_body(Lits, SummarizedExBodyLiterals, NCurVarsInfo, FinalVarsInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_variables_domain(+UniqPredCallDomain, +VarPredicateCalls, -VarsDomain)
%
% Given:
%   UniqPredCallDomain: see auxiliar datastructures at top of this file
%   VarPredicateCalls: see preprocess_hypothesis/5
%
% Returns:
%   VarsDomain: sorted list of length equal to the number of distinct variables in hypothesis. Each element is a term of the form:
%                        vdomain(Var, AllowedDomainPos, InitialDomain) where:
%
%                         Var: variable appearing in hypothesis
%                         AllowedDomainPos: list of integers with the currently allowed positions (relative to InitialDomain) 
%                                           for Var's domain
%                         Domain: a term dom(v1, v2, ..., vN), where each vI is a distinct possible value for Var 
%
% Importante note: Contrary to the standalone subsumer, in the subsumer integrated in GILPS we need to say the initial domain
%  is the union domain. Otherwise we wouldn't be able to efficiently update the subsumption datastructures when doing the
%  identification of the first failing literal
%  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_variables_domain(UniqPredCallDomain, VarPredicateCalls, VarsDomain):-
  maplist(remove_position, UniqPredCallDomain, UniqPredCallDomainValues),
  list_to_rbtree(UniqPredCallDomainValues, RB_VarDomain), % notice that in general we cannot use ord_list_to_rbtree here!
  % the reason is subtle: it's when we have more than one variable in the head and we are subsuming the examples all at once
  % (i.e. given their ids, not given their ground bottoms). In this case the UniqPredCallDomain structure just gets bound
  % after computation and it may not be sorted
  maplist(compute_var_domain(RB_VarDomain), VarPredicateCalls, VarsDomain).
  %format("aqui2~n",[]).

remove_position((Name/Arity,LitArgs)-DomainWPos, (Name/Arity,LitArgs)-Domain):-
  maplist(remove_value, DomainWPos, Domain).

remove_value(Key-_Value, Key).

%compute_var_domain(+RB_VarDomain, +VarPredicateCalls, -VarDomain)
compute_var_domain(RB_VarDomain, Var-PredCalls, vdomain(Var, AllowedDomainPos, UnionDomain)):-
  compute_var_domain_aux(PredCalls, RB_VarDomain, undeterminate, [], IntersectDomain, UnionDomain),
  construct_allowed_domain_pos(IntersectDomain, UnionDomain, 1, AllowedDomainPos).

%compute_var_domain_aux(+UnfoldedPredCalls, +RB_VarDomain, +CurIntersectDomain, +CurUnionDomain, -FinalIntersectDomain, -FinalUnionDomain)
compute_var_domain_aux([], _, IntersectDomain, UnionDomain, IntersectDomain, UnionDomain).
compute_var_domain_aux([Name/Arity-LitArg|PredCalls], RB_VarDomain, CurIntD, CurUnionD, FinalIntD, FinalUnionD):-
  rb_lookup((Name/Arity, LitArg), VarDomainForPredCall, RB_VarDomain),
  (CurIntD==undeterminate ->  NCurIntD = VarDomainForPredCall  ;  ord_intersection(CurIntD, VarDomainForPredCall, NCurIntD)),
  ord_union(CurUnionD, VarDomainForPredCall, NCurUnionD),
  %NCurIntD=[_|_], % we cannot stop even if it the intersection is empty, as the datastructure may be useful when we consider a prefix of the current hypothesis (e.g. in identifing first failing literal).
  compute_var_domain_aux(PredCalls, RB_VarDomain, NCurIntD, NCurUnionD, FinalIntD, FinalUnionD).

%construct_allowed_domain_pos(+IntersectDomain, +UnionDomain, +CurPos, -AllowedDomainPos)
construct_allowed_domain_pos([], _, _, []).
construct_allowed_domain_pos([H1|T1], [H2|T2], CurPos, AllowedDomainPos):-
  NCurPos is CurPos+1,
  (H1==H2 ->
      AllowedDomainPos = [CurPos|R],
      construct_allowed_domain_pos(T1, T2, NCurPos, R)
   ; % H1@>H2
      construct_allowed_domain_pos([H1|T1], T2, NCurPos, AllowedDomainPos)
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% update_neighbours_domain(+IVarID, +IVarIDValueIndex, +ClauseEvalTerm, +NeighbourVars, +CurVarAllowedPositions, -NewVarAllowedPositions)
%
% Given:
%   IVarID: variable ID for which we have just updated the domain (the one which influences the variables in NeighboursVar)
%   IVarIDValueIndex: index of the value (relative to VarID's variable initial domain)
%   ClauseEvalTerm: a term ceval(ClauseInfo, VarsInfo, PairwiseVarInters) where 
%                                    ClauseInfo: see main datastructures
%                                    VarsInfo: see main datastructures
%                                    PairwiseVarInters: RB tree where the key is a pair (VarID1,VarID2) and value is the list of literal positions (relative to the hypothesis) that Var1 and Var2 share
%   NeighbourVars: sorted list of variable IDs that interact with Var  (notice that some of these IDs may correspond to variables already bound)
%   CurVarAllowedPositions: a term vars_allowed_pos(AllowedPos1, .., AllowedPosN) with the current available domains for all variables in VarsInfo
%
% Returns:
%   NewVarAllowedPositions: a term vars_allowed_pos(AllowedPos1, .., AllowedPosN) where
%                                            AllowedPos_I has the ordered list of indexs allowed for variable I (i.e. the i-th variable from the VarsInfo term of ClauseEvalTerm)
%
% Example:
%    example_update_domains(NewVarAllowedPos):-
%      IVarID=1, IVarIDValueIndex=1,
%      NeighboursVar = [2,3],
%      LInfo1= linfo(p/2, [f(A),g(B)], [A,B], [1-vpos([1],[],[]),2-vpos([], [1], [])], values([f(a1),g(b2)])),
%      LInfo2= linfo(p/2, [f(A),g(C)], [A,C], [1-vpos([1,2],[],[]),3-vpos([], [1], [2])], values([f(a1),g(c2)],[f(a1),g(c3)])),
%      ClauseInfo=cinfo(LInfo1,LInfo2),
%      list_to_rbtree([(1,2)-[1],(2,1)-[1],(1,3)-[2],(3,1)-[2]], PairwiseVarInters),
%      VInfo1 = vinfo(a1, 1, [2], idom(a1,a2,a3)),
%      VInfo2 = vinfo(B, 2, [1], idom(b1,b2,b3)),
%      VInfo3 = vinfo(C, 3, [1], idom(c1,c2,c3)),
%      VarsInfo=varsinfo(VInfo1, VInfo2, VInfo3),
%      CurVarAllowedPos=vars_allowed_pos(1-[1],2-[2,3],3-[1,2,3]),
%      update_neighbours_domain(IVarID, IVarIDValueIndex, ceval(ClauseInfo, VarsInfo, PairwiseVarInters), NeighboursVar, CurVarAllowedPos, NewVarAllowedPos).
%
% VarAllowedPos = vars_allowed_pos(1-[1],1-[2],2-[2,3])
%
% Notes:
%   This predicate fails if any of the NewVarInfos has an empty domain. Note that one should be extra careful when devising new examples. It's very easy to forget
%   to set all datastructures properly and consistently. Some of the information is redundant but still needs to be there.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

update_neighbours_domain(IVarID, IVarIDValueIx, CEval, NeighbourVars, CurVarsAllowedPos, NewVarsAllowedPos):-
  CurVarsAllowedPos=..[vars_allowed_pos|CVAPArgs],
  update_neighbours_domain_aux(NeighbourVars, 1, IVarID, IVarIDValueIx, CEval, CVAPArgs, NVAPArgs),
  NewVarsAllowedPos=..[vars_allowed_pos|NVAPArgs].

%update_neighbours_domain_aux(+NeighbourVars, +CurVarID, +IVarID, +IVarIDValueIndex, +ClauseEvalTerm, +CurVarAllowedPos, -NewVarAllowedPos)
update_neighbours_domain_aux([], _CVID, _IVarID, _IVarIDValueIx, _CEval, AllowedPos, AllowedPos).
update_neighbours_domain_aux([ID|IDs], ID, IVarID, IVarIDValueIx, ceval(ClauseInfo, VarsInfo, PairwiseVarInters), [CurAllowedPos|R1], [NewAllowedPos|R2]):-
  !,
  arg(ID, VarsInfo, VInfo),
  update_variable_domain(IVarID, IVarIDValueIx, PairwiseVarInters, ClauseInfo, VInfo, CurAllowedPos, NewAllowedPos),
  NVID is ID+1,
  update_neighbours_domain_aux(IDs, NVID, IVarID, IVarIDValueIx, ceval(ClauseInfo, VarsInfo, PairwiseVarInters), R1, R2).
update_neighbours_domain_aux([ID|IDs], CVID, IVarID, IVarIDValueIx, CEval, [AllowedPos|R1], [AllowedPos|R2]):-
  NVID is CVID+1,
  update_neighbours_domain_aux([ID|IDs], NVID, IVarID, IVarIDValueIx, CEval, R1, R2).

%update_variable_domain(+IVarID, +IVarIDValueIndex, +PairwiseVarInters, +ClauseInfo, +VarInfo, +CurAllowedPos, -NAllowedDPos)
update_variable_domain(IVarID, IVarValueIx, PairwiseVarInters, ClauseInfo, vinfo(Var, ID, _Inters, IDom), Len-AllowedDPos, NAllowedDPos):-
  (ground(Var) ->
      NAllowedDPos = Len-AllowedDPos % if Var is already ground do not update its allowed positions (would be a waste of time, and is already known)
    ;
      rb_lookup((IVarID, ID), LitsPositions, PairwiseVarInters),
      maplist(get_litinfo_from_position(ClauseInfo), LitsPositions, LitsInfoForVar),
      determine_values_for_variable_in_literals(LitsInfoForVar, IVarID, IVarValueIx, dom(Var, AllowedDPos, IDom), NAllowedDPos)
  ).

%get_litinfo_from_position(+LitsInfo, +Position, -LitInfo)
get_litinfo_from_position(LitsInfo, Position, LitInfo):-
  arg(Position, LitsInfo, LitInfo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% determine_values_for_variable_in_literals(+LiteralInfos, +InfluencingVarID, +InfluencingVarIDValueIndex, +DomVar, -NewVarAllowedPos)  %notice it's plural- a list of literals
%
% Given:
%   LiteralInfos: list of litinfo/4 terms that are know to have Var and InfluencingVariableID
%   InfluencingVarID: variable ID of the variable that is influencing the domain of Var
%   InfluencingVarIDValueIndex: position (in the initial domain of variable ID) of the value that was assigned to InfluencingVarID
%   DomVar: a term dom(Var, VarAllowedPos, VarInitDomain), where Var is a variable that is influenced by InfluencingVarID and both appear in all LiteralsInfo
%
% Returns:
%   NewVarAllowedPos: updated VarAllowedPos (from DomVar) with intersection of all values from all the literals that are consistent with the new value (InfluencingVarIDValueIndex)
%                                    for the variable that is being assigned (InfluencingVarID)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_values_for_variable_in_literals([LitInfo|LitsInfo], IVarID, IVarValueIx, dom(Var, VarAllowedPos, VarInitDomain),  Len-NewVarAllowedPos):- % Var occurs in Vars and in Args
  determine_values_for_variable_in_literal(IVarID, IVarValueIx, LitInfo, Var, CurVarValues),
  determine_values_for_variable_in_literals_aux(LitsInfo, IVarID, IVarValueIx, Var, CurVarValues, NewAllowedValuesForVar),
  update_variable_allowed_positions(NewAllowedValuesForVar, VarAllowedPos, VarInitDomain, NewVarAllowedPos),
  length(NewVarAllowedPos, Len), %NewVarAllowedPos=[_|_]. 
  Len>0. % make sure there is at least one value in the new allowed domain

% determine_values_for_variable_in_literals_aux(+LiteralInfos, +InfluencingVarID, +InfluencingVarIDValueIndex, +Var, +CurVarValues, -FinalVarValues) 
determine_values_for_variable_in_literals_aux([], _, _, _, Values, Values).
determine_values_for_variable_in_literals_aux([LitInfo|LitsInfo], IVarID, IVarValueIx, Var, CurVarValues, FinalVarValues):-
  determine_values_for_variable_in_literal(IVarID, IVarValueIx, LitInfo, Var, VarValuesForLit),
  ord_intersection(CurVarValues, VarValuesForLit, NCurVarValues),
  NCurVarValues=[_|_],% make sure NCurVarValues has at least one element
  determine_values_for_variable_in_literals_aux(LitsInfo, IVarID, IVarValueIx, Var, NCurVarValues, FinalVarValues).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% determine_values_for_variable_in_literal(+InfluencingVarID, +InfluencingVarIDValueIndex, +LiteralInfo, +Var, -VarValues) 
%    notice it's singular: i.e. a single literal
%
% Given:
%   InfluencingVarID: variable ID of the variable that is influencing the domain of Var
%   InfluencingVarIDValueIndex: position (in the initial domain of variable ID) of the value that was assigned to InfluencingVarID
%   LiteralInfo: a litinfo term, see main datastructures
%   Var: a variable that is influenced by InfluencingVarID and appears in LiteralInfo
%
% Returns:
%   VarValues: the list of possible Values for Var in Literal
%
% Notes:
%   The idea is to find all the positions where InfluencingVarID has value InfluencingVarIDValueIndex. These are already precomputed and are VPos from retrieved
%    here: arg(IVarValueIx, VPos, Positions)
%    Now the arg(Pos, PredValues, PredArgs) within the findall, gets the possible values for Var (Var appears in PredArgs), taking into account the bindings of the
%    other variables in PredArgs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_values_for_variable_in_literal(IVarID, IVarValueIx, linfo(_Pred, PredArgs, _Vars, Index, PredValues), Var, VarValues):- % Var occurs in Vars and in Args
  memberchk(IVarID-VPos, Index),%get the influencing var VPos from Index 
  arg(IVarValueIx, VPos, Positions), % list of positions relevant for finding the new domain of Var (they are the positions where IVarID has value IVarValuePos)
  %
  % IF THERE ARE OTHER VARIABLES IN LITINFO WHICH ARE GROUND, THEN, INSTEAD OF DOING THE FINDALL, over all the positions
  % DO IT INSTEAD OVER THE INTERSECTION OF all the positions
  %
  %format("IVarID:~w Ix:~w Positions:~w~n", [IVarID, IVarValueIx, Positions]),
  %findall(Var, (member(Pos, Positions), arg(Pos, PredValues, PredArgs)), VarValues1), % THIS IS A HUGE BOTTLENECK WHEN A VARIABLE HAS VERY FEW DISTINCT VALUES AND THEY ARE EVENLY SPREAD
  find_values_for_variable(Positions, Var, PredArgs, PredValues, VarValues1),
  list_to_ord_set(VarValues1, VarValues).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% find_values_for_variable(+Positions, +Var, +PredArgs, +PredValues, -VarValue) % Var appears in PredArgs
%
% Notes:
%  This predicate is equivalent to:
%     findall(Var, (member(Pos, Positions), arg(Pos, PredValues, PredArgs)), VarValues1),%  THIS IS A HUGE BOTTLENECK WHEN A VARIABLE HAS VERY FEW DISTINCT VALUES AND THEY ARE EVENLY SPREAD
%
% But the findall wouldn't work when Var is not ground. This works in cases where Var is not ground (useful when the example contains variables) and is about 25% faster!
%
% Notice that we use convlist/3 rather than maplist/3, because some of the matchings may fail.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

find_values_for_variable([], _Var, _PredArgs, _PredValues, []).
find_values_for_variable([Position|Positions], Var, PredArgs, PredValues, VarValues):-
  copy_term((Var,PredArgs), (NVar,NPredArgs)), % this copy_term/2 is a bottleneck. It can be avoided if we extract the placeholder
  (arg(Position, PredValues, NPredArgs)-> VarValues=[NVar|RVarValues] ; VarValues=RVarValues),
  % in most scenarios the arg/3 call will succeed. But it could fail. E.g. when Var appears more than once in PredArgs
  % E.g. Positions=[1,2], Var=X, PredArgs=[X,X,a], and PredValues=[[1,2,a],[2,2,a]], then VarValues=[2], arg/3 fails when Position=1
  find_values_for_variable(Positions, Var, PredArgs, PredValues, RVarValues).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% update_variable_allowed_positions(+ValuesAllowedForPred, +CurVarAllowedPos, +VarInitDomain, -NewVarAllowedPos)
%
% Given:
%   ValuesAllowedForPred: an ordered list of values allowed for var Var in a given predicate or sets of predicates (given a set of restrictions on other variables)
%   CurVarAllowedPos: list of positions currently allowed  for the domain of a variable (relative to VarInitDomain)
%   VarInitDomain: a term idom/N where N is the initial domain of Var
%
% Returns:
%   NewVarAllowedPos: an updated CurVarAllowedPos (equal or smaller to CurVarAllowedPos)
%
% Example:
%   update_variable_allowed_positions([b,c,d], [1,3,5], idom(a,b,c,d,e), NewAllowedPos).
%        NewAllowedPos =  [3]  % i.e. only 'c' is allowed now for the domain of A
%
%   update_variable_allowed_positions([c,d,f], [1,2,3,4,5], idom(a,b,c,d,e), NewAllowedPos).
%        NewAllowedPos =  [3,4]  % i.e. only 'c' and 'd' are now allowed for the domain of A
%
% Notes:
%   Complexity: max(length(ValuesAllowedForPred), VarAllowedPositions). This predicate is identical to ord_intersection/3 except that we cannot compare the sets
%   directly. We have to dereference CurVarAllowedPos to be able to intersect it with ValuesAllowedForPred
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

update_variable_allowed_positions([], _, _, []):-!.
update_variable_allowed_positions([_|_], [], _, []):-!.
update_variable_allowed_positions([Val|Vals], [Pos|Poss], Domain, NewAllowedPos):-
  arg(Pos, Domain, ValueAtPos), % dereference Pos to a value (ValueAtPos) in Domain
  (Val==ValueAtPos ->
     NewAllowedPos = [Pos|Tail],
     update_variable_allowed_positions(Vals, Poss, Domain, Tail)
   ;
     Val @< ValueAtPos ->
     update_variable_allowed_positions(Vals, [Pos|Poss], Domain, NewAllowedPos)
    ;
     % Val @> ValueAtPos 
     update_variable_allowed_positions([Val|Vals], Poss, Domain, NewAllowedPos)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% first_failing_literal(+Clause, +ExampleID, -FailLitPos)
% first_failing_literal(+Clause, +ExampleID, +AfterPos, -FailLitPos)
%
% Given:
%   Clause: list of literals (with head variables needing to be instantiated)
%   ExampleID: integer, the index (id) of the example to use
%   (optional) AfterPos: indicates where to start the search for the failing literal (inclusive)
%
% Returns:
%   FailLitPos: position (1 based) of the first failing literal of Clause when matched with Example
%               (between 1 and Length, or between AfterPos and Length if AfterPos is defined).
%               If there is no failing literal 0 is returned. If head is the failing literal 1 is returned,
%               if it's a literal in the body its index is returned (first literal in the body has index 2)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

first_failing_literal(Clause, ExampleID, FailLitPos):-
  first_failing_literal(Clause, ExampleID, 1, FailLitPos).

% first_failing_literal(+Clause, +Example, +AfterPos, -FailLitPos)
first_failing_literal(Hypothesis, ExampleID, AfterPos, FailLitPos):-
  length(Hypothesis, Len),
  (AfterPos>Len ->  % we have reached end of clause, no further test
     FailLitPos=0
   ;
    copy_term(Hypothesis, [Head|HypBody]),
    (bb_get(ExampleID, example(_Weight, Head, CondensedExampleBody)) -> 
       first_failing_literal_aux([Head|HypBody], CondensedExampleBody, AfterPos, FailLitPos)
     ;
       FailLitPos = 1 % Heads do not match, FailLitPos is 1
    )
  ).

%first_failing_literal_aux(+Hypothesis, +CondensedExampleBody, +AfterPos, -FailLitPos)
% Pre: Head of condensed example body has been matched with Hypothesis Head
first_failing_literal_aux(Hypothesis, CondensedExampleBody, AfterPos, FailLitPos):-
  (compute_consistent_clause_eval_term(Hypothesis, CondensedExampleBody, AfterPos, CEvalTerm, VarsAllowedPos, PrefixLen) ->
    (
%        format("PrefixLen:~w~n", [PrefixLen]),
	\+(\+ once(theta_subsumes_aux(CEvalTerm, VarsAllowedPos))) ->
	  (PrefixLen=0 -> FailLitPos = 0 ; FailLitPos is PrefixLen+1)
      ;
          (PrefixLen=0 -> length(Hypothesis, NLen) ; NLen=PrefixLen),
	  AfterPos1 is max(1, min(2*AfterPos-NLen, NLen)),
	  binary_first_failing_literal(AfterPos1, NLen, CEvalTerm, FailLitPos)
    )
   ;
      FailLitPos = AfterPos
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% compute_consistent_clause_eval_term(+Hypothesis, +CondensedExampleBody, +MinPrefixLen, -CEvalTerm, -VarsAllowedPos, -PrefixLen)
%
% Given:
%   MinPrefixLen: first position (inclusive) to start searching for the prefix of hypothesis consistent with example
%
% Returns:
%   PrefixLen: the longest length prefix of Hypothesis with which it's possible to construct a consistent clause eval term
%              (a value of 0 means that all the hypothesis was used as the prefix)
%
% Notes:
%   This predicate fails if there is no consistent prefix starting after InitPos (inclusive)
% 
% This is identical do compute_clause_eval_term with an important exception.
% compute_clause_eval_term/4 would fail if a predicate in Hypothesis does not exist in example or if a variable
% has empty domain. In these cases, we now want to remove all literals from Hypothesis starting at the conflict
% point.
%
% The CEvalTerm and VarsAllowedPos returned by this predicate are not necessarily of Hypothesis but of
% the longest prefix of hypothesis that is consistent with Example (note that it still may not subsume it).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

compute_consistent_clause_eval_term([Head|HypBody], CondensedExampleBody, MinPrefixLen,
                                    CEvalTerm, VarsAllowedPos, PrefixLen):-
  preprocess_hypothesis([Head|HypBody], PLitsInfo, VarPredCalls, UniqPredCalls, PairwiseVarInters, FullVarInters),
  (
   (compute_predcall_domain(UniqPredCalls, CondensedExampleBody, UniqPredCallDomain),
    compute_variables_domain(UniqPredCallDomain, VarPredCalls, VarsDomain),
    compute_clause_info(PLitsInfo, CondensedExampleBody, UniqPredCallDomain, VarsDomain, ClauseInfo),
    create_variables_info(VarsDomain, FullVarInters, VarsInfo, VarsAllowedPos)
   ) ->
     CEvalTerm=ceval(ClauseInfo, VarsInfo, PairwiseVarInters),
     PrefixLen=0
   ;
     length([Head|HypBody], Len),
     MaxPrefixLen=Len,
     find_longest_consistent_prefix(MinPrefixLen, MaxPrefixLen, Len, [Head|HypBody], CondensedExampleBody,
                                    CEvalTerm, VarsAllowedPos, PrefixLen)
  ).

% find_longest_consistent_prefix(+MinPrefixLen, +MaxPrefixLen, +LastFail, +FullHypothesis, +CondensedExampleBody, -CEvalTerm, -VarsAllowedPos, -PrefixLen)
find_longest_consistent_prefix(MinPrefixLen, MaxPrefixLen, LastFail, FullHypothesis, CondensedExampleBody, CEvalTerm, FVarsAllowedPos, FPrefixLen):-
  PrefixLen is (MinPrefixLen+MaxPrefixLen)//2,
%  format("MinPrefixLen:~w MaxPrefixLen:~w~n", [MinPrefixLen, MaxPrefixLen]),
%  format("CurPrefixLen:~w~n", [PrefixLen]),
  firstNElemsOf(FullHypothesis, PrefixLen, PrefixHyp),  
  %portray_clause(PrefixHyp),nl,
  preprocess_hypothesis(PrefixHyp, PLitsInfo, VarPredCalls, UniqPredCalls, PairwiseVarInters, FullVarInters),
  (
    (compute_predcall_domain(UniqPredCalls, CondensedExampleBody, UniqPredCallDomain),
     compute_variables_domain(UniqPredCallDomain, VarPredCalls, VarsDomain),
     compute_clause_info(PLitsInfo, CondensedExampleBody, UniqPredCallDomain, VarsDomain, ClauseInfo),
     create_variables_info(VarsDomain, FullVarInters, VarsInfo, VarsAllowedPos)
     ) ->
	  (PrefixLen=:=LastFail-1 ->
		 CEvalTerm=ceval(ClauseInfo, VarsInfo, PairwiseVarInters),
                 FVarsAllowedPos=VarsAllowedPos,
		 FPrefixLen=PrefixLen
	    ;
		 NMinPrefixLen is PrefixLen + 1,
                 find_longest_consistent_prefix(NMinPrefixLen, MaxPrefixLen, LastFail, FullHypothesis, CondensedExampleBody, CEvalTerm, FVarsAllowedPos, FPrefixLen)
	  )
   ;
   (
    NMaxPrefixLen is PrefixLen - 1,
    find_longest_consistent_prefix(MinPrefixLen, NMaxPrefixLen, PrefixLen, FullHypothesis, CondensedExampleBody, CEvalTerm, FVarsAllowedPos, FPrefixLen)
   )
  ).
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% binary_first_failing_literal(+StartPos, +LastPos, +CEval, -FailLitPos)
%
% Notes:
%  This is done using a binary search algorithm. Note that we only preprocess the clause and example once
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

binary_first_failing_literal(LitPos, LitPos, _, LitPos):- !.%format("Failing literal pos=~w~n", [LitPos]),!. %StartLit=LastLit
binary_first_failing_literal(StartLit, LastLit, CEval, FailLitPos):-
  LitsUntilCut is (StartLit + LastLit)//2,
  %format("StartLit:~w LastLit:~w LitsUntilCut:~w~n", [StartLit, LastLit, LitsUntilCut]),
  %format("CEval before:~w~n", [CEval]),
  prefix_evaluation_term(CEval, LitsUntilCut, NCEval, NVarsAllowedPositions),
  %format("CEval after:", []),portray_clause(NCEval),nl,
  %format("NVarsAllowedPositions:~w~n", [NVarsAllowedPositions]),halt,
  (\+(\+ once(theta_subsumes_aux(NCEval, NVarsAllowedPositions))) ->
     NStartLit is LitsUntilCut+1,
     binary_first_failing_literal(NStartLit, LastLit, CEval, FailLitPos) % notice that we pass the original CEval!!
   ;
     binary_first_failing_literal(StartLit, LitsUntilCut, CEval, FailLitPos)  % notice that we pass the original CEval!!
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% prefix_evaluation_term(+CETerm, +LastLitIndexToConsider, -NCETerm, -NVarsAllowedPositions)
% (updates clause evaluation datastructure to consider only the first LastLitIndexToConsider literals of the hypothesis in CETerm)
%
% Given:
%  CETerm: original clause evaluation term: ceval(ClauseInfo, VarsInfo, PairwiseVarInters) as described in the header of this file considering all the literals of an hypothesis
%  LastIndexToConsider: index of the last literal to consider
%
% Returns:
%  NCETerm: a new clause evaluation term considering only literals up to position LastIndexsToConsider
%  NVarAllowedPositions: new list of positions allowed when only the first LastLitIndexToConsider literals are considered
%                           (a superset of VarAllowedPos)
%
% Notes: 
%    The purpose of this predicate is to update the clause evaluation datastructure to just consider the first Last
%        so that it can be used for the binary finding of first failing literals. 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prefix_evaluation_term(ceval(ClauseInfo, VarsInfo, _PairwiseVarIDInters), LastLitIndexToConsider, 
                       ceval(NClauseInfo, NVarsInfo, NPairwiseVarIDInters), NVarsAllowedPositions):-
  %update ClauseInfo
  ClauseInfo=..[cinfo|LitsInfo],
  firstNElemsOf(LitsInfo, LastLitIndexToConsider, NLitsInfo),
  NClauseInfo=..[cinfo|NLitsInfo],
  %update VarsInfo
  %term_variables(NLitsInfo, Variables),% this term_variables may be a bit expensive, we could get the variables cheaply
  create_temp_pairwise_var_inters(NLitsInfo, TempPairwiseVarIDInters),%TempPairwiseVarInters is a list of VarID1,VarID2
  create_var_inters_aux(TempPairwiseVarIDInters, NPairwiseVarIDInters, FullVarInters),
  readjust_varsinfo(VarsInfo, FullVarInters, NVarsInfo),
  construct_vars_allowed_positions(ceval(NClauseInfo, NVarsInfo, NPairwiseVarIDInters), NVarsAllowedPositions).

% create_temp_pairwise_var_inters(+NClauseInfo, -TempPairwiseVarInters)
create_temp_pairwise_var_inters([_HeadInfo|BodyLitsInfo], TempPairwiseVarInters):-
  create_temp_pairwise_var_inters_aux(BodyLitsInfo, 2, TempPairwiseVarInters).

%create_temp_pairwise_var_inters_aux(+BodyLitsInfo, +Index, -TempPairwiseVarInters)
create_temp_pairwise_var_inters_aux([], _Index, []).
create_temp_pairwise_var_inters_aux([linfo(_Pred, _Args, ArgVarIDs, _, _)|TLitsInfo], Index, CLitPVI):-
  create_pairwise_var_inters(ArgVarIDs, Index, LitPVI), %notice that we are using variable ids here rather than the actual variables as in previous calls to create_pairwise_var_inters/3
  complete_var_inters(LitPVI, CLitPVI, CLitPVI_Tail), %CLitPVI_Tail is the tail of CLitPVI
  Index1 is Index+1,
  create_temp_pairwise_var_inters_aux(TLitsInfo, Index1, CLitPVI_Tail).

%complete_var_inters(+LitPVI, -CLitPVI, -CLitPVI_Tail), %CLitPVI_Tail is the tail of CLitPVI
complete_var_inters([], T, T).
complete_var_inters([(V1,V2)-Index|LitPVIs], CLitPVI, R):-
  CLitPVI=[(V1,V2)-Index|Tail],
  (V1==V2 ->
     Tail2=Tail
   ;
     Tail=[(V2,V1)-Index|Tail2]
  ),
  complete_var_inters(LitPVIs, Tail2, R).

%readjust_varsinfo(+VarsInfo, +FullVarInters, -NVarsInfo)
readjust_varsinfo(VarsInfo, FullVarInters, NVarsInfo):-
  VarsInfo=..[varsinfo|VarsInfoArgs],
  readjust_varsinfo_args(FullVarInters, VarsInfoArgs, NVarsInfoArgs),
  NVarsInfo=..[varsinfo|NVarsInfoArgs].

%readjust_varsinfo_args(+FullVarInters, +VarsInfoArgs, -NVarsInfoArgs)
readjust_varsinfo_args([], _, []).
readjust_varsinfo_args([VarID-VInters|FVInters], [vinfo(Var,VarID,_OldVInters,IDom)|VIs], [vinfo(Var,VarID,VInters,IDom)|NVIs]):-
  readjust_varsinfo_args(FVInters, VIs, NVIs).

%construct_vars_allowed_positions(+ceval(ClauseInfo, VarsInfo, PairwiseVarInters), NVarsAllowedPositions)
construct_vars_allowed_positions(ceval(ClauseInfo, VarsInfo, PairwiseVarInters), VarsAllowedPositions):-
  VarsInfo=..[varsinfo|VarsInfoArgs],
  maplist(construct_var_allowed_positions(ClauseInfo, PairwiseVarInters), VarsInfoArgs, VarsAllowedPosL),
  VarsAllowedPositions=..[vars_allowed_pos|VarsAllowedPosL].

%construct_var_allowed_positions(+ClauseInfo, +PairwiseVarInters, +VarInfo, -VarAllowedPos)
construct_var_allowed_positions(ClauseInfo, PairwiseVarInters, vinfo(_Var, VarID, _VInters, _InitialDomain), Len-AllowedDomainPos):-
  rb_lookup((VarID, VarID), LitsPositions, PairwiseVarInters), % LitsPositions has the positions where Var appears in ClauseInfo
  construct_var_allowed_positions_aux(LitsPositions, ClauseInfo, VarID, undeterminate, AllowedDomainPos), % AllowedDomainPos is \= undeterminate, otherwise something is wrong
  length(AllowedDomainPos, Len).

% construct_var_allowed_positions_aux(+LitsPositions, +ClauseInfo, +VarID, +CurAllowedDomainPos, -FinalAllowedDomainPos)
construct_var_allowed_positions_aux([], _, _, AllowedDomainPos, AllowedDomainPos).
construct_var_allowed_positions_aux([Pos|LPos], ClauseInfo, VarID, CurAllowedDomainPos, FinalAllowedDomainPos):-
  arg(Pos, ClauseInfo, linfo(_Pred, _Args, _ArgVars, Index, _PredValues)),
  memberchk(VarID-VPos, Index),  %get the VPos from Index
  VPos=..[vpos|VPosArgs],
  allowed_domain_for_vpos(VPosArgs, 1, AllowedDomainPosForPred),
  (CurAllowedDomainPos == undeterminate ->  
     NAllowedDomainPos = AllowedDomainPosForPred 
   ;
     ord_intersection(CurAllowedDomainPos, AllowedDomainPosForPred, NAllowedDomainPos)
  ),
  construct_var_allowed_positions_aux(LPos, ClauseInfo, VarID, NAllowedDomainPos, FinalAllowedDomainPos).

%allowed_domain_for_vpos(+VPos, +CurPos, -AllowedDomainPosForPred)
allowed_domain_for_vpos([], _, []).
allowed_domain_for_vpos([P|Pos], CurPos, AllowedDomainForPred):-
  NCurPos is CurPos+1,
  (P=[_|_] -> % P is not empty
     AllowedDomainForPred = [CurPos|RemainAllowedDomainForPred],
     allowed_domain_for_vpos(Pos, NCurPos, RemainAllowedDomainForPred)
   ;
     allowed_domain_for_vpos(Pos, NCurPos, AllowedDomainForPred)
  ).

%test:-
%  theta_subsumes([c(X),h(X),f(X,b)], [c(d), h(d), f(d,c)]).
%  theta_subsumes([h(X),f(X,Y),g(X,Z),diff(Y,Z)], [h(b),f(b,c),diff(c,x),g(b,x)]).
%  theta_subsumes([class(X, mammal),has_milk(X),friend(X,bat)], [class(dog, mammal), has_milk(dog),friend(dog,cat)]).
  %load_examples([[c(a),h(a,b),h(a,c),f(x,e),f(g,h)]], [ExampleID]),
  %first_failing_literal([c(X),h(X,Y),h(X,_Z),h(X,_W),f(Y,_W)], ExampleID, FailLitPos),


%:- test.
