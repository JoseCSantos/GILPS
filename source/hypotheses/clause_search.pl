%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-05-04
%
%    This file has predicates to generate the set of successor clauses given a starting
%  clause. The search is done in a way identically to the refinement graph search with
%  a bottom clause but with no need of having a bottom clause!
%
%    We do not need the bottom clause but search the clauses in the same order as if
%    we have it. The key idea is that the literals to appear are ordered according
%    to the mode following:
%
%    The literal to add 'next' to the last one is one that:
%     is after the current one in the mode declaration or
%     the global settings that are relevant are:
%         'i': depth of new variables
%         clause_length: number of literals in a clause (including the head)
%         splitvars: if true split the input/output variables of the head and the output variables
%                    of the body literals
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(clause_search,
           [
             initialClause/4
%             nextClause/6
           ]
         ).

% GILPS modules
:- use_module('../mode declarations/mode_declarations', [mode_head/1, modebDecls/1]).
:- use_module('../settings/settings', [setting/2]).
:- use_module('../messages/messages', [message/2]).

% YAP modules
:- use_module(library(lists), [memberchk/2, member/2, select/3]).
%:- use_module(library(apply_macros), [maplist/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Datastructures for representing a clause/constructing the sucessors of a given example/clause
% The below datastructures have some similarities with the bottom clause datastructures but
% have been optimized for the current purpose
%
%    InTerms: a list of tuples: t(Type,Term,Variables) where Variables is a list
%             of all variables Type,Term (normally the list has only one variable unless
%             splitvars is true). Each variable is a tuple of the form: Variable-Depth
%             where Depth represents the depth (in the 'i' sense) of Variable
%
%    OutTerms: list of tuples like InTerms but having only the output variables of the head.
%              Notice that OutTerms these variables do not appear on InTerms. However a given tuple
%              Term/Type may appear both in InTerms and OutTerms (if splitvars=true)
%
%    Depth: depth of clause (i.e. depth of the deepest input variable in use)
%
%    LastLitPos: position of the last literal in the mode body declarations (0 when we have only
%                the head). This is important so that we know what appears next.
%
%    Literals: list of variablized literals representing the current clause (in reverse order)
%
%    LiteralsSignatures: signature of Literals
%
%    UsedLiterals: a grounded version of clause (as a list of literals) with numbervars/3
%
% The same variable never appears
%
% How to determine what literals to add next:
%
%   The literals to add after the current clause are ones that:
%            1) do not appear in UsedLiterals
%            2) have ModeBodyPosition > LastLitPos and at least one input variable
%                  of depth equal to Depth
%            3) have at least one input variable of depth equal to Depth+1
%
% Theorem 1: The successors of a clause have depth = clause depth or clause depth+1
% Theorem 2: The successors of a clause have clause length = clause length+1
%
% Notes:
%   These datastructures allow for splitvars
%   For lookups, a list is faster than rbtrees for N<=32
%   For normal updates (one element at a time), a list is faster than rbtrees for N<=14
%   For updates (all elements in a row), the list is faster than rbtrees for N<=57
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                             Predicates to manipulate InTerms                               %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% add2Terms(+(Term/Type), +Var, +Terms, -NewTerms)
%    Terms: a list of tuples: t(Type,Term,Variables) where Variables is a list of Variables
add2Terms(Term/Type, Var, Depth, Terms, [t(Term, Type, [Var-Depth|Vars])|Terms1]):-
  select(t(Term, Type, Vars), Terms, Terms1),!. %Term/Type already exists in InTerms
add2Terms(Term/Type, Var, Depth, Terms, [t(Term, Type, [Var-Depth])|Terms]).% %Term/Type does not exist in InTerms


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processInputArgument(+WM, +Depth, +Term/Type, +InTerms, +OutTerms, -VarCreated, -Var, -NInTerms, -NOutTerms)
%
% Returns:
%  VarCreated: either leave it unground or bind it to 'yes' if a variable is created
%
% Notes:
%   We want to return the variable associated with Term/Type. If we are processing a body literal this
%   term is guaranteed to exist. Otherwise, if we are processing the head literal, three situations may occur:
%    1) term already exists in OutTerms
%          Move it to InTerms and return it. If splitvars=true, then return the additional solution:
%            Leave OutTerms as it is and create a new InTerm term for it
%    2) term already exists in InTerms
%          Return it. If splitvars=true, then return the additional solution:
%            Create new InTerm term for it
%    3) term does not exist
%          Create new InTerm t(Type, Term, Variable) for it
%
%   Note that if splitvars=true the situations cumulative (otherwise it is guaranteed only one occurs)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processInputArgument(body, _, Term/Type, InTerms, OutTerms, _, Var, InTerms, OutTerms):-
  !,
  memberchk(t(Term, Type, Vars), InTerms),
  member(Var-_, Vars). %if splitvars=false then Vars is a list with a single element. Ignore depth

processInputArgument(head, Depth, Term/Type, InTerms, OutTerms, _, Var, NInTerms, NOutTerms):-
  select(t(Term, Type, Vars), OutTerms, OutTerms1), % term already exists in OutTerms
  (setting(splitvars, false)-> !; true),%if splitvars=false we cut here
  select(Var-Depth, Vars, Vars1),
  (Vars1=[]->%No more variables for this term, we can remove it from OutTerms
     NOutTerms=OutTerms1
   ;
     NOutTerms=[t(Term, Type, Vars1)|OutTerms1]
  ),
  add2Terms(Term/Type, Var, Depth, InTerms, NInTerms).

processInputArgument(head, _, Term/Type, InTerms, OutTerms, _, Var, InTerms, OutTerms):-
  memberchk(t(Term, Type, Vars), InTerms), % term already exists in InTerms
  (setting(splitvars, false)-> !; true),%if splitvars=false we cut here
  member(Var-_, Vars).

processInputArgument(head, Depth, Term/Type, InTerms, OutTerms, yes, Var, NInTerms, OutTerms):-
% create new variable if splitvars=true or if variable does not exist both in InTerms and OutTerms
  add2Terms(Term/Type, Var, Depth, InTerms, NInTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processOutputArgument(+WM, +Depth, +Term/Type, +InTerms, +OutTerms, -VarCreated, -Var, -NInTerms, -NOutTerms)
%
% Given:
%
% Returns:
%   VarCreated: either leave it unground or bind it to 'yes' if a variable is created
%
% Notes:
%   We want to return(create a variable associated with Term/Type. 
%
%   If we are processing a body literal then we are in the same situation as processing an Input argument
%   for the head. That is:
%
%    1) term already exists in OutTerms
%          Move it to InTerms and return it (update depth to current depth).
%          If splitvars=true, then return the additional solution:
%            Leave OutTerms as it is and create a new InTerm term for it
%    2) term already exists in InTerms
%          Return it. If splitvars=true, then return the additional solution:
%            Create new InTerm term for it
%    3) term does not exist
%          Create new InTerm t(Type, Term, Variable) for it
%
%   If we are processing an head literal then:
%    Three situations may occur:
%    1) term already exists in OutTerms
%          Return associated variable. If splitvars=true, then return the additional solution:
%            Add a new variable for it in OutTerms
%    2) term already exists in InTerms
%          Return associated variable. If splitvars=true, then return the additional solution:
%            Add a new variable for it in OutTerms
%    3) term does not exist
%          Create new OutTerm t(Type, Term, Variable) for it
%
%   Note that if splitvars=true the situations cumulative (otherwise it is guaranteed only one occurs)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processOutputArgument(body, Depth, Term/Type, InTerms, OutTerms, VarCreated, Var, NInTerms, NOutTerms):-
  !,
  processInputArgument(head, Depth, Term/Type, InTerms, OutTerms, VarCreated, Var, NInTerms, NOutTerms).

processOutputArgument(head, _, Term/Type, InTerms, OutTerms, _, Var, InTerms, OutTerms):-
  memberchk(t(Term, Type, Vars), OutTerms), % term already exists in OutTerms
  (setting(splitvars, false)-> !; true),%if splitvars=false we cut here
  member(Var-_, Vars).

processOutputArgument(head, _, Term/Type, InTerms, OutTerms, _, Var, InTerms, OutTerms):-
  memberchk(t(Term, Type, Vars), InTerms), % term already exists in InTerms
  (setting(splitvars, false)-> !; true),%if splitvars=false we cut here
  member(Var-_, Vars).

processOutputArgument(head, Depth, Term/Type, InTerms, OutTerms, yes, Var, InTerms, NOutTerms):-
% create new variable if splitvars=true or if variable does not exist both in InTerms and OutTerms
  add2Terms(Term/Type, Var, Depth, OutTerms, NOutTerms).

%groundLiteral(+Literal, -GroundLiteral)
groundLiteral(Literal, GroundLiteral):-
  copy_term(Literal, GroundLiteral),
  numbervars(GroundLiteral, 0, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initialClause(+Example, -Clause, -ClauseSignature, -ClauseDS)
%
%  Given:
%   Example: an example as a ground fact
%
%  Returns:
%    Clause: list of literals
%    ClauseSignature: Clause's signatures 
%    ClauseDS: a tuple: (InTerms, OutTerms, Depth, LastLitPos, UsedLiterals)
%              these datastructures are as described above
%
%  Notes:
%    This predicate returns through backtracking all possible next clauses
%
%  Some examples:
%       :- modeh(1, p(+int,+int,-int,-int)).
%
%       initialClause(p(0,0,0,0), C, CS, CDS).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initialClause(Example, [Head], [Head_Signature], (InTerms, OutTerms, 0, 0, [GHead])):-
  mode_head(Head_Signature),
  generalizeLiteral(Head_Signature, Example, 0, [], [], head, Head, _, InTerms, OutTerms),
  groundLiteral(Head, GHead).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% generalizeLiteral(+Signature, +Literal, +Depth, +InTerms, +OutTerms, +LiteralSource,
%                   -GeneralizedLiteral, -DepthIncrease, -NewInTerms, -NewOutTerms)
%
% Given:
%   Signature: signature of a literal (e.g. a(+char,-int,#class))
%   Literal: ground literal (e.g. (a(c,5,mammal)))
%   InTerms: as described above. E.g. []
%   LiteralSource: either head or body.
%
% Returns:
%   GeneralizedLiteral: Literal generalized (e.g. (a(A,B,mammal)))
%   NewInTerms: InTerms after processing this literal. E.g. [(5,int), (c/char)]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generalizeLiteral(Signature, GroundLit, Depth, InTerms, OutTerms, LiteralSource,
                  GeneralizedLiteral, DepthIncrease, NewInTerms, NewOutTerms):-
  Signature=..[PredName|SigArgs],
  GroundLit=..[PredName|LitArgs],
  processLiteralArgs(SigArgs, LitArgs, Depth, InTerms, OutTerms, LiteralSource,
                     Args, DepthIncrease, NewInTerms, NewOutTerms),
  GeneralizedLiteral=..[PredName|Args].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% processLiteralArgs(+SigArgs, +LitArgs, +Depth, +InTerms, +OutTerms, +WorkingMode,
%                    -Args, -DepthIncrease, -NewInTerms, -NewOutTerms)
%
% Given:
%   SigArgs: list of signature arguments. E.g.: [+char,-int,#class])
%   LitArgs: list of ground literal argumens. E.g.: [c,5,mammal]
%   Depth: highest depth of the input variables in LitArgs
%   InTerms: as described above. E.g. []
%   OutTerms: as described above. E.g. []
%   WorkingMode: either head or body. The only difference between the two modes is that in the latter
%                variables of -type add added to InTerms. E.g.: 'head'
%
% Returns:
%   Args: arguments according to the signature and LitArgs. E.g.: [A,B,mammal].
%   DepthIncrease: either 'yes' or 'no'. if 'yes' there is at least one output variable of depth
%                  exactly Depth+1 (there are never output variables of higher depth)
%   NewInTerms: InTerms after processing this literal. E.g. [(5,int), (c/char)]
%   NewOutTerms: OutTerms after processing this literal. E.g. [(5,int)]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processLiteralArgs([], [], _, InTerms, OutTerms, _, [], DepthIncrease, InTerms, OutTerms):-
  !,
  (var(DepthIncrease) -> DepthIncrease=no ; true).
processLiteralArgs([#_Type|SigArgs], [Term|LitArgs], Depth, InTerms, OutTerms, WM, 
                   [Term|Args], DI, NInTerms, NOutTerms):-
  !,
  processLiteralArgs(SigArgs, LitArgs, Depth, InTerms, OutTerms, WM, Args, DI, NInTerms, NOutTerms).
processLiteralArgs([+Type|SigArgs], [Term|LitArgs], Depth, InTerms, OutTerms, WM,
                   [Var|Args], DI, NInTerms, NOutTerms):-
  !,
  processInputArgument(WM, Depth, Term/Type, InTerms, OutTerms, _, Var, InTerms1, OutTerms1),
  processLiteralArgs(SigArgs, LitArgs, Depth, InTerms1, OutTerms1, WM, Args, DI, NInTerms, NOutTerms).

processLiteralArgs([-Type|SigArgs], [Term|LitArgs], Depth, InTerms, OutTerms, WM,
                   [Var|Args], DI, NInTerms, NOutTerms):-
  !,
  processOutputArgument(WM, Depth, Term/Type, InTerms, OutTerms, DI, Var, InTerms1, OutTerms1),
  processLiteralArgs(SigArgs, LitArgs, Depth, InTerms1, OutTerms1, WM, Args, DI, NInTerms, NOutTerms).

processLiteralArgs([ComplexType|SigArgs], [ComplexTerm|LitArgs], Depth, InTerms, OutTerms, WM,
                   [ComplexArg|Args], DI, NInTerms, NOutTerms):-
  !,
  ComplexType=..[ComplexTermName|ComplexTermSigs],
  ComplexTerm=..[ComplexTermName|ComplexTermArgs],
  processLiteralArgs(ComplexTermSigs, ComplexTermArgs, Depth, InTerms, OutTerms, WM,
                     ComplexArgs, DI, InTerms1, OutTerms1),
  ComplexArg=..[ComplexTermName|ComplexArgs],
  processLiteralArgs(SigArgs, LitArgs, Depth, InTerms1, OutTerms1, WM, Args, DI, NInTerms, NOutTerms).



/*
%Some tests

test(N):-
  set(splitvars, true),
  utils_list:createList(N, -int, SigArgs),
  utils_list:createList(N, 0, PredArgs),
  Sig=..[p|SigArgs],
  Pred=..[p|PredArgs],
  modeh(Sig),
  findall(_C,
          initialClause(Pred, _C, _CS, _CDS), %fail.
          Result),
  %portray_clause(Result),nl,
  length(Result, NumSols),
  format("N=~w~n", [NumSols]).

test(_):-
  mode_declarations:eraseModeDeclarations.

:- measureTime(test(1), 1000, 'N=1').
:- measureTime(test(2), 1000, 'N=2').
:- measureTime(test(3), 1000, 'N=3').
:- measureTime(test(4), 1000, 'N=4').
:- measureTime(test(5), 1000, 'N=5').
:- measureTime(test(6), 10, 'N=6').
:- measureTime(test(7), 10, 'N=7').
:- measureTime(test(8), 10, 'N=8').
:- measureTime(test(9), 10, 'N=9').
:- measureTime(test(10), 1, 'N=10').
:- measureTime(test(11), 1, 'N=11').

%:- measureTime(test(12), 100000, 'N=12').

*/
