%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-01-15
%
%     This file contains misc. utility predicates to deal with clauses, bodies,
%  mode declarations and predicate themselves
%
%     All predicates support function symbols in arguments
%
%     Notes: we probably should divide this module in two: one for utilities on clauses
%            another for utilities on terms
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(utils_clauses,
            [
              op(500, fx, (#)), % is this module the best place for this definition?
              signature2PredArity/2,
              signatureConstIndexs/2,
              signatureIOVars/4,
              getIOVars/4,
              buildPredCall/4,
              atomArgsTyped/4,
              atomArgs/4,
              variables/2,
              list2Body/2,
              literals2clause/2,
              firstNLiterals/3,
              clauseLength/2,
              singletons/2,
              prettyPrintLiterals/1,

              get_placeholders/4,
              skolemize/2,                % skolemize/2, skolemize_ignoring/3 
              skolemize/3,
              skolemize_ignoring/3, % and undo_skolemize/2 should be moved
              undo_skolemize/2,      % to some other library (utilities on terms)

              % clause transformations
              remove_redundant/2,
              cut_transformation/2,
              once_transformation/2
            ]
         ).

% GILPS modules
:- use_module('../settings/settings', [setting/2]). % because of 'print' (number literals per line)

% YAP modules
:- use_module(library(lists), [member/2, append/3, delete/3, nth0/3, select/3, reverse/2]).
:- use_module(library(apply_macros), [maplist/3]).
:- use_module(library(ordsets), [ord_subset/2, ord_subtract/3, ord_union/3, ord_disjoint/2]).
:- use_module(library(terms), [subsumes/2]).
:- use_module(library(varnumbers), [varnumbers/2]). % for undo_skolemize/2
% this is an undocumented YAP library. varnumbers/2 does the inverse of numbervars/3

%:- set_prolog_flag(single_var_warnings, on).
%:- set_prolog_flag(unknown, warning).

%:- op(500, fx, user:(#)). % is this module the best place for this definition?
% Note: With Yap6 this was moved to the module exported list
% this is supported in swi and yap. In swi this syntax is to apply the operator
% redefinition at the user module (where user files are read). otherwise the redefinition
% is just applied to the current module where it is not useful.

% type checker
%:- use_module('../type_checker/type_check').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% signature2PredArity(+Signature, -PredName/Arity)
%
% Given:
%   Signature: e.g. (a(+int, -char))
%
% Returns:
%   PredName/Arity: e.g. a/2
%
% Notes:
%   This is a straightforward predicate, except when signature starts with not. In that case
%   the PredName is not(Normal PredName)/4
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- pred signature2PredArity(signature, not(name)/integer).

signature2PredArity(not(Signature), not(PredName)/Arity):-
  !,
  signature2PredArity(Signature, PredName/Arity).
signature2PredArity(Signature, PredName/Arity):-
  functor(Signature, PredName, Arity).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% getConstIndexs(+Args, +CurArg, -ConstantIndexs)
%
%  given Args from a predicate signature and Current Arg number, this predicate will output a
%  list of the constant indexs on its third argument
%
%   e.g. getConstIndexs([+int,#(int),#(int),-nat], 1, [2,3]))
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- pred getConstIndexs(list(ioMode), integer, list(integer)).  % type checker signature

getConstIndexs([], _, []):-!.
getConstIndexs([#_|T], N, [N|CIs]):-
  !, N1 is N+1,
  getConstIndexs(T, N1, CIs).
getConstIndexs([+_|T], N, CIs):-
  !, N1 is N+1,
  getConstIndexs(T, N1, CIs).
getConstIndexs([-_|T], N, CIs):-
  !, N1 is N+1,
  getConstIndexs(T, N1, CIs).
getConstIndexs([ComplexTerm|T], N, CIs):-
  ComplexTerm=..[TermName|ComplexTermArgs],
  \+member(TermName, [+,-,#]),%TermName is not a regular IO term or constant
  append(ComplexTermArgs, T, NT),
  getConstIndexs(NT, N, CIs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% signatureConstIndexs(+Signature, -ConstIndexList)
%
%  given a predicate signature (e.g. a(+int, #int)), returns a list with its constants (#) indexs
%
%  ConstIndexList = [int], list of indexs in Predicate.
%    e.g. signatureConstIndexs(a(+int,#(int),#(int),-nat), [2,3])
%    e.g. signatureConstIndexs(a(-int,b(#char)),[2])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

signatureConstIndexs(Signature, ConstIndexs):-
  Signature=..[_|Args],
  getConstIndexs(Args, 1, ConstIndexs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% getIOVars(+IOTypes, ?AllVars, -TypedInputVars, -TypedOutputVars)
%
% Given:
%   IOTypes: list of IO types (e.g. [f(+int), -char, #int])
%   AllVars: list of variables in IOTypes (including constants). Can also be an output variable.
%
% Returns:
%   TypedInputVars: input variables from AllVars together with type (e.g [A/int])
%   TypedOutputVars: output variables from AllVars together with type (e.g. [B/char])
%
% E.g.
%
%  e.g. getIOVars([+int,-float,+float,#int,-char], [A,B,C,D,E], [A/int, C/float], [B/float,E/char])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

getIOVars([], [], [], []):-!.
getIOVars([+Type|T], [V|Vars], [V/Type|IVs], OVs):-
  !,getIOVars(T, Vars, IVs, OVs).
getIOVars([-Type|T], [V|Vars], IVs, [V/Type|OVs]):-
  !,getIOVars(T, Vars, IVs, OVs).
getIOVars([#_|T], [_|Vars], IVs, OVs):-
  !,getIOVars(T, Vars, IVs, OVs).
getIOVars([ComplexTerm|IOArgs], Vars, IVs, OVs):-
  ComplexTerm=..[_|ComplexTermArgs],
  append(ComplexTermArgs, IOArgs, NIOArgs),
  getIOVars(NIOArgs, Vars, IVs, OVs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% signatureIOVars(+Signature, -AllVars, -TypedInputVars, -TypedOutputVars)
%
%  given a predicate signature returns:
%     Input variables in TypedInputVars
%     Output variables in TypedOutputVars
%     Just the variables (without types) in AllVars (includes singletons for constants, i.e. '#')
%
%  All variables in Input and Output appear in AllVars
%
%  e.g. signatureIOVars(a(+int,-float,+float,#int,-char), [A,B,C,D,E], [A/int, C/float], [B/float,E/char])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

signatureIOVars(Signature, AllVars, TypedInputVars, TypedOutputVars):-
  Signature=..[_|Args],
  getIOVars(Args, AllVars, TypedInputVars, TypedOutputVars).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% buildPredCall(+Signature, +IOCVariables, -Types, -PredCall)
%    Builds a predicate call from its signatures and Input/Output/Constant variables
%    Returns variable types as well
%
%  E.g. buildPredCall(a(f(-int), +atom, #char, -char), [5,c,a,b], Types, P).
%         P = a(f(5),c,a,b)
%         Types = [-int, +atom, #char, -char]
%
% buildPredCall(+Signature, -IOCVariables, -Types, +PredCall)
%    Returns the variables/constants given a signature and predicate call
%    Returns variable types as well
%
%  E.g. buildPredCall(a(f(-int), +atom, #char, -char), Vars, Types, a(f(3), a, b, d)).
%          Vars = [3,a,b,d] ?
%          Types = [-int,+atom,#char,-char],
%
% buildPredCall(+Signature, -IOCVariables, -Types, -PredCall)
%    Given a signature, returns all variables and builds the predicate call
%    Returns variable types as well
%
%  E.g. buildPredCall(a(f(-int), +atom, #char, -char), Vars, Types, PredCall).
%
%        Types = [-int,+atom,#char,-char],
%         Vars = [_A,_B,_C,_D] ? ;
%     PredCall = a(f(_A),_B,_C,_D),
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% buildPredCallArgs(+SignatureArgs, +IOCVariables, -RemainIOCVariables, -Types, -RemainTypes, -PredCallArgs).

buildPredCallArgs([], V, V, T, T, []).
buildPredCallArgs([ComplexTerm|SigArgs], [V|Vars], RemVars, [ComplexTerm|Types], RemTypes, [V|PredCallArgs]):-
  functor(ComplexTerm, IOMode, 1),
  member(IOMode, [+,-,#]),!, % IOMode is a regular IO term or constant
  buildPredCallArgs(SigArgs, Vars, RemVars, Types, RemTypes, PredCallArgs).
buildPredCallArgs([ComplexTerm|SigArgs], Vars, RemVars, Types, RemTypes, [CurPredArg|PredCallArgs]):-
  ComplexTerm=..[ComplexTermName|ComplexTermArgs],
  buildPredCallArgs(ComplexTermArgs, Vars, TRemVars, Types, TRemTypes, ComplexTermPredCallArgs),
  CurPredArg=..[ComplexTermName|ComplexTermPredCallArgs],
  buildPredCallArgs(SigArgs, TRemVars, RemVars, TRemTypes, RemTypes, PredCallArgs).
buildPredCall(Signature, IOCVariables, Types, PredCall):-
  Signature=..[PredName|SignatureArgs],
  buildPredCallArgs(SignatureArgs, IOCVariables, [], Types, [], PredCallArgs),
  PredCall=..[PredName|PredCallArgs].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% atomArgsTyped(+Atom, +AtomSignature, -AtomTypedInputTerms, -AtomTypedOutputTerms)
%
% Given:
%  Atom: an atom (with variables instantiated or not)
%  AtomSignature: Atom's signature
%
% Returns
%  AtomTypedInputTerms: sorted unique atom's typed input terms (may be variables)
%  AtomTypedOutputTerms: sorted unique atom's typed output terms (may be variables)
%
% E.g.
%  atomArgsTyped(a(p1, 4, c), a(+person,+int,-char), [4/int, p1/person], [c/char])
%  atomArgsTyped(a(A, B, C), a(+person,+int,-char), [A/person, B/int], [C/char])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

atomArgsTyped(Atom, AtomSig, AtomTypedInputTerms, AtomTypedOutputTerms):-
  buildPredCall(AtomSig, IOCVariables, Types, Atom),
  getIOVars(Types, IOCVariables, RepAtomTypedInputTerms, RepAtomTypedOutputTerms),
  sort(RepAtomTypedInputTerms, AtomTypedInputTerms),
  sort(RepAtomTypedOutputTerms, AtomTypedOutputTerms).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% atomArgs(+Atom, +AtomSignature, -AtomInputTerms, -AtomOutputTerms)
%
% Given:
%  Atom: an atom (with variables instantiated or not)
%  AtomSignature: Atom's signature
%
% Returns
%  AtomInputTerms: sorted unique atom's input terms (may be variables)
%  AtomOutputTerms: sorted unique atom's output terms (may be variables)
%
% E.g.
%  atomArgs(a(p1, 4, c), a(+person,+int,-char), [4, p1], [c])
%  atomArgs(a(A, B, C), a(+person,+int,-char), [A, B], [C])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

atomArgs(Atom, AtomSig, AtomInputVariables, AtomOutputVariables):-
  atomArgsTyped(Atom, AtomSig, AtomTypedInputVariables, AtomTypedOutputVariables),
  maplist(removeType, AtomTypedInputVariables, RepAtomInputVariables),
  maplist(removeType, AtomTypedOutputVariables, RepAtomOutputVariables),
  % we sort it just because it could be possible (although unlikely), that, after removal of the type
  % there are repeated values (if different types share the same constant)
  sort(RepAtomInputVariables, AtomInputVariables),
  sort(RepAtomOutputVariables, AtomOutputVariables).

% removeType(+TypedVariable, -Variable)
removeType(Var/_Type, Var).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% list2Body(+L, -B): Given a non empty list L, converts it to body B
% list2Body(-L, +B): Given a body B, converts it to a (non empty) list L
%
%   This predicate may be used either way, depending which of its 2 arguments is instantiated
%
%   e.g. list2Body([a(X),b(X),c],(a(X),b(X),c))
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list2Body([], true):-!.
list2Body([A,B|C], (A,R)):-
  !, list2Body([B|C], R).
list2Body([A], A):-!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% literals2clause(+Literals, -Clause): Given a non empty list L of literals, converts it to a clause
% literals2clause(-Literals, +Clause): Given a clause, converts it to a non empty list of literals
%
%  Given:
%    Literals: a set of literals as a list (the first element is the head of a clause)
%
% E.g.
%   literals2clause([good(X)], good(X)).
%   literals2clause([good(X),small(X)], (good(X):-small(X))).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

literals2clause([Head], Head):-
  functor(Head, Functor, _NumArgs), Functor\=(:-), !.
literals2clause([Head|BodyLiterals], (Head:-Body)):-
  !, list2Body(BodyLiterals, Body).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% firstNLiterals(+Goal, +N, -NGoal)
%
% Given:
%  Goal: a Prolog goal (i.e. literals separated by ',')
%     N: an integer, the number of literals of Goal to put in NGoal
%
% Returns:
%  NGoal: the first N literals of Goal (separated by ',' as well)
%
% Notes:
%  If Goal is shorter than N, NGoal=Goal
%
% Example:
%   e.g. firstNLiterals((a(X),b(X),c(X)), 2, (a(X),b(X)))
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

firstNLiterals(Goal, N, NGoal):-
  firstNLiterals(Goal, 1, N, NGoal).

firstNLiterals((A,_), N, N, A):-!.
firstNLiterals((A,T), CurN, N, (A,R)):-
  !, CurN1 is CurN+1,
  firstNLiterals(T, CurN1, N, R).
firstNLiterals(A, N, N, A):-!. % N is precisely the last literal in Goal
firstNLiterals(A, _, _, A):-!. % Goal is shorter than N literals

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% get_placeholders(+Term1, +Term2, +ActionMode, -Placeholders)
% get_placeholders(-Term1, +Term2, +ActionMode, -Placeholders)
%
% Given:
%   Term1: a term that we will look to be strictly contained (i.e can't be Term1) in Term2
%   Term2: a term where we will look for Term1 places in
%   ActionMode: 'equal' or 'unify'. In equal mode the terms must be strictly equal (no unification occurs)
%               In unify, terms are allowed to be unified (only useful if either Term1 or Term2 contains variables)
%
% Returns:
%  PlaceHolders: list of placeholders where Term2 contains Term1.
%                 Each placeholder is of the form:
%                        Placeholder --> null
%                        Placeholder --> function symbol/arity/Index/Placeholder
%  Where Index is an integer from 0..Arity
%  Function symbols ',' and '.' (i.e. lists) have a special treatment
%  Function symbol ',' is not supported (i.e. undefined behaviour)
%
% E.g.
%  get_placeholders(x, [a,x], [./2/2/./2/1])
%  get_placeholders(x, f(x,y,z), [f/3/1])
%  get_placeholders(z, f([x,y,z]), [f/1/./2/./2/3])
%  get_placeholders(x, f(x,g(x)), [f/2/1,f/2/2/g/1/1])
%  get_placeholders(g(x), f(x,g(x)), [f/2/2])
%  get_placeholders(x, f(z), [])
%  get_placeholders(x, x, []) % nothing is returned because Term1 must be a subterm of Term2.
%                             % if we were to support this the return would be x/0/0
%                             % but then the placeholders for the other cases would have to be suffixed too
%
% Notes:
%  if ActionMode=equal then it's valid to use the calling mode:
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_placeholders(Term1, Term2, ActionMode, PlaceHolders):-
  get_placeholders_term(Term2, Term1, ActionMode, _Stack, [], TPlaceHolders), %TPlaceHolders will be in reverse order
  reverse(TPlaceHolders, PlaceHolders).

%get_placeholders_list(+TermArgs, +SubTerm, +ActionMode, +Stack, +Index, -Placeholders, -FPlaceHolders)
get_placeholders_list([], _Term, _ActionMode, _Stack, _Index, PlaceHolders, PlaceHolders).
get_placeholders_list([H|T], Term, ActionMode, Stack, Index, CurPlaceHolders, FPlaceHolders):-
  (ActionMode=unify-> H=Term ; H==Term,!),
  Index1 is Index+1,
  get_placeholders_list(T, Term, ActionMode, Stack, Index1, [Stack/Index|CurPlaceHolders], FPlaceHolders).
get_placeholders_list([H|T], Term, ActionMode, Stack, Index, CurPlaceHolders, FPlaceHolders):-
  get_placeholders_term(H, Term, ActionMode, Stack/Index, CurPlaceHolders, TPlaceHolders),
  Index1 is Index+1,
  get_placeholders_list(T, Term, ActionMode, Stack, Index1, TPlaceHolders, FPlaceHolders).

%get_placeholders_term(+Term, +SubTerm, +ActionMode, +Stack, -PlaceHolders, -FinalPlaceHolders)
% Pre: Term\==SubTerm
get_placeholders_term(Term, SubTerm, ActionMode, Stack, PlaceHolders, FPlaceHolders):-
  (compound(Term) ->
     Term=..[FunctionSymbol|Args],
     length(Args, Arity),
     (var(Stack) -> NewStack = FunctionSymbol/Arity ; NewStack = Stack/FunctionSymbol/Arity),
     get_placeholders_list(Args, SubTerm, ActionMode, NewStack, 1, PlaceHolders, FPlaceHolders)
   ;
     FPlaceHolders=PlaceHolders
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% skolemize(+Term, -SkolemTerm)
%
% Given:
%  Term: an arbitrary prolog term
%  (optional) StartID: the start id for the first variable to be skolemized (if not provided, 0)
%
% Returns:
%  SkolemTerm: Term skolemized
%
% Example:
%   skolemize(f(C,D,a,b), S), S=f('$VAR'(0),'$VAR'(1),a,b)
%
% Notes:
%   When a term is skolemized all their variables are replaced by '$VAR'(ID) constants, where each variable has a unique ID.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

skolemize(Term, SkolemTerm):-
  skolemize(Term, 0, SkolemTerm).

skolemize(Term, StartVarIndex, SkolemTerm):-
  copy_term(Term, SkolemTerm),
  numbervars(SkolemTerm, StartVarIndex, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% skolemize_ignoring(+Term, +Variables, -SkolemTerm)
%
% Given:
%  Term: an arbitrary prolog term
%  Variables: list of variables to ignore when skolemizing Term (no matter if is ordered or not)
%
% Returns:
%  SkolemTerm: Term skolemized (with occurrences of variable Variable kept as in Term)
%
% Example:
%   skolemize_ignoring(f(C,D,a,b), [C], S), S=f(C,'$VAR'(0),a,b)
%
% Notes:
%  This is in fact a specialized numbervars/3
%  The idea is to copy the term to an auxiliar term, extract the new terms variables
%  and assign to its new variables either an ID (an increasing integer) or the corresponding
%  variable from the original variables to ignore
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

skolemize_ignoring(Term, Variables, Term1):-
  copy_term((Term, Variables), (Term1, Variables1)),
  term_variables(Term1, Term1Variables),
  %it would be more efficient to sort Term1Variables and subtract Variables from it, however, we would have to keep track of the original positions 
  skolemize_ignoring_aux(Term1Variables, 0, Variables1, Variables).

%skolemize_ignoring_aux(+TermVariables, +CurVarID, +TermVarsToIgnore, +OriginalVarsToIgnore).
skolemize_ignoring_aux([], _VarID, _VariablesCopy, _VariablesOriginal).
skolemize_ignoring_aux([H|T], VarID, VariablesC, VariablesO):-
  (check_and_assign(H, VariablesC, VariablesO) ->
    NVarID = VarID
  ; 
    H = '$VAR'(VarID),
    NVarID is VarID+1
  ),
  skolemize_ignoring_aux(T, NVarID, VariablesC, VariablesO).

%check_and_assign(+Var, +VariablesC, +VariablesO)
check_and_assign(VarA, [VarB|_], [VarC|_]):-
  VarA==VarB,!,
  VarA=VarC.
check_and_assign(VarA, [_|T1], [_|T2]):-
  check_and_assign(VarA, T1, T2).
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% undo_skolemize(+Term, -VarTerm)
%
% Given:
%  Term: a skolemized term (i.e. a term with variables ground by skolemize/2 or numbervars/3)
%
% Returns:
%  VarTerm: a term with variables '$VAR'(N) replaced by new variables (not the original ones!)
%
%  Note:
%    The variables in VarTerm are NOT the same as before the skolemization!. I.e.
%   skolemize(A, S), undo_skolemize(S, V). V is not the same variable as A!!
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

undo_skolemize(SkolemTerm, Term):-
  varnumbers(SkolemTerm, Term). % note that varnumbers/2 is an undocumented Yap6 feature

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% remove_redundant(+Literals, -FLiterals)
%
% Given:
%   Literals: a clause as a list of literals
%
% Returns:
%   FLiterals: Literals with redundant ones removed.
%
% Notes:
%   This predicate removes body literals from Literals which are redundant using theta subsumption.
%   Let C be a clause and L a literal in it. Let C'=C-L. A literal L is redundant in a clause C if
%   C subsumes C'. (that is, there is a substitution theta such that all literals in C are a subset
%    of the literals in C'. Note that C has one extra literal)
%   This function has complexity O(N^3.log2(N)), N=number of literals.
%   (described in Vitor Santos Costa paper: Query Transformations for Improving the Efficiency of ILP systems)
%
% E.g.:
%
%  remove_redundant([a(A),b(A,B),b(A,5),c(C,10),c(D,10)], R).
%          R = [a(A),b(A,5),c(D,10)] ?
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove_redundant([Head|RedLits], [Head|Lits]):-
  remove_redundantAux(RedLits, Lits).

remove_redundantAux(Lits, FLits):-
  select(Lit, Lits, RemainLits),
  \+(\+(redundant(Lit, Lits, RemainLits))), !,
  remove_redundantAux(RemainLits, FLits).
remove_redundantAux(Lits, Lits).

redundant(Lit, Lits, NLits):-
  copy_term(NLits, TempLits),
  member(Lit, NLits),
  simplified_subsumption(Lits, TempLits).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% simplified_subsumption(+Clause1, +Clause2)
%
% Given:
%   Clause1: a clause as a list of literals
%   Clause2: another clause as a list of literals
%
% Succeeds iff Clause1 subsumes Clause2
%   (that is, if there exists a substitution that makes the literals
%   in Clause1 a subset of the literals in Clause2)
%
% Notes:
%   The subsumes/2 in library(terms) is not equivalent to this one.
%   (subsumes/2 is term subsumption requiring both terms to have the same functor and arity).
%   Here we don't require the lists to have the same size. The first one may be a
%   subset of the second (as in true subsumption)
%   Notice however that this is not true subsumption as we are skolemizing the clause.
%   E.g. It's true that f(x,A) subsumes f(x,y) but this predicate would fail on that example
%
%   simplified_subsumption/2 has complexity O(N.Log2(N)), where N is max(len clause1, len clause2)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplified_subsumption(Lits1, Lits2):-
  sort(Lits1, SLits1),
  sort(Lits2, SLits2),
  numbervars(SLits1, 0, _),
  numbervars(SLits2, 0, _),
  ord_subset(SLits1, SLits2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% true_subsumption(+Clause1, +Clause2)
%
% This is true subsumption. The problem is that it's very inneficient
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

true_subsumption([Head|Body1], [Head|Body2]):-
  true_subsumption_aux(Body1, Body2).

true_subsumption_aux([], _):-!.
true_subsumption_aux([H|T], Lits):-
  select(H, Lits, RLits), % since we know that nor Clause1 nor Clause2 have repeated literals
                          % we can use select/3 rather than member/2, which will be more efficient 
  true_subsumption_aux(T, RLits).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% in_lattice(+Clause1, +Clause2)
%
% Succeeds iff Clause1 is in the lattice defined by Clause2 (a bottom clause)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

in_lattice([Head|Body1], [Head|Body2]):-
  in_lattice_aux(Body1, Body2).

in_lattice_aux([], _):-!.
in_lattice_aux([H|T], Lits):-
  select(Lit, Lits, RLits),
  subsumes(Lit, H), %notice that it's Lit, H, Lit must be more general
  in_lattice_aux(T, RLits).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% cut_transformation(+Literals, -FLiterals)
%
% Given:
%   Literals: a clause as a list of literals
%
% Returns:
%   FLiterals: Literals with non-interacting groups isolated (in once/1 groups)
%
% Notes:
%   This predicate reorders the literals in the body into non interacting groups (i.e. the solution of one
%   group does not interfere with the others). The groups are isolated in once/1 groups (we just need one
%   solution per group).
%   This function has complexity O(N^2), N=number of literals.
%   (described in Vitor Santos Costa paper: Query Transformations for Improving the Efficiency of ILP systems)
%
% E.g.:
%
%  cut_transformation([a(A),b(A,1),c(A,2)], R).
%          R = [a(A),once(b(A,1)),once(c(A,2))] ?
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cut_transformation([Head|Body], [Head|NBody]):-
  term_variables(Head, HIV),
  create_groups(Body, HIV, [], Groups), % groups have their order reversed
  make_clause_body(Groups, NBody).

%make_clause(+Groups, -Clause), Groups are reversed and inside the literals are reversed too
make_clause_body([], []).
make_clause_body([g(Lits, _)|Groups], Body):-
  reverse(Lits, Lits1),
  make_clause_body(Groups, RemainBody),
  list2Body(Lits1, BLits), append(RemainBody, [once(BLits)], Body).
  %append(RemainBody, [!|Lits1], Body). %in case we prefer '!' rather than onces

%createGroups(+Literals, +HeadInputVariables, +CurGroups, -Groups)
create_groups([], _, Groups, Groups).
create_groups([Lit|Lits], HIV, CurGroups, Groups):-
  sharing_groups(Lit, HIV, CurGroups, ShareGroups, RemainGroups),
  merge_groups(ShareGroups, NewGroup),
  add_to_group(Lit, NewGroup, NewGroup1),
  create_groups(Lits, HIV, [NewGroup1|RemainGroups], Groups).

%sharing_groups(+Literal, +HeadInputVariables, +Groups, -ShareGroups, -RemainGroups)
sharing_groups(Literal, HIV, Groups, ShareGroups, RemainGroups):-
  term_variables(Literal, LitVars),
  sort(LitVars, LV), % not to remove repetition, but to be ordered
  ord_subtract(LV, HIV, LV1),
  groups_with_vars(Groups, LV1, ShareGroups, RemainGroups).

%groups_with_vars(+Groups, +LitVars, -ShareGroups, -RemainGroups).
groups_with_vars([], _, [], []).
groups_with_vars([g(Lits, Vars)|Groups], LitVars, ShareGroups, [g(Lits, Vars)|RemainGroups]):-
  ord_disjoint(Vars, LitVars),!,
  groups_with_vars(Groups, LitVars, ShareGroups, RemainGroups).
groups_with_vars([g(Lits, Vars)|Groups], LitVars, [g(Lits, Vars)|ShareGroups], RemainGroups):-
  groups_with_vars(Groups, LitVars, ShareGroups, RemainGroups).

%add_to_group(+Literal, +Group, -Group)
add_to_group(Literal, g(Literals, Vars), g([Literal|Literals], NVars)):-
% we have to reverse the group literals later
  term_variables(Literal, LitVars),
  ord_union(Vars, LitVars, NVars).

%merge_groups(+Groups, -Group)
merge_groups([], g([], [])).% empty group
merge_groups([g(Lits, Vars)|Groups], g(NLits, NVars)):-
  merge_groups(Groups, g(GLits, GVars)),
  append(GLits, Lits, NLits), % GLits appears before Lits
  ord_union(Vars, GVars, NVars).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% once_transformation(+Literals, -FLiterals)
%
% Given:
%   Literals: a clause as a list of literals
%
% Returns:
%   FLiterals: Literals with non-interacting groups isolated (in once/1 groups)
%              (recursively applied)
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

once_transformation(C1, C2):-
  list2Body(C1, Body),
  stat_once(Body, BodyOnce),
  list2Body(C2, BodyOnce).

stat_once(C1, C2):-
  copy_term(C1, CopyC1),
  transform(CopyC1, NewCopyC1),
  transform_parallel(C1, NewCopyC1, C2).

independent_prefix(Conj, Prefix, Rest):-
  app_conj(Prefix, Rest, Conj),
  independent(Prefix, Rest).

app_conj(G, Conj, (G, Conj)).
app_conj((G,C1), C2, (G, C)):-
  app_conj(C1, C2, C).

independent(A, B):-
  term_variables(A, LA),
  term_variables(B, LB),
  diff(LA, LB).

diff(L1, L2):-
  numbervars(L1, 0, _),
  notallfree(L2),!,
  fail.
diff(_, _).

notallfree([X|R]):-
  (var(X)->
    notallfree(R)
  ;
    true
  ).

transform(C1, C2):-
  independent_prefix(C1, Prefix, Rest), !,
  C2 = (once(NewPrefix), NewRest),
  transform(Prefix, NewPrefix),
  transform(Rest, NewRest).

transform((Goal,Conj), NewConjunction):-
  !,
  NewConjunction = (Goal,NewConj),
  apply_groundness_information(Goal),
  transform(Conj, NewConj).

transform(G, G):-
  apply_groundness_information(G).

apply_groundness_information(G):-
  numbervars(G, 0, _).

transform_parallel(Conj, NewCopiedConj, NewConj):-
  transform_parallel1(Conj, _RestConj, NewCopiedConj, NewConj).

transform_parallel1(Conj, RestConj, (CA, CB), NewConj):-
  !,
  transform_parallel1(Conj, RConj, CA, NewA),
  transform_parallel1(RConj, RestConj, CB, NewB),
  NewConj = (NewA, NewB).

transform_parallel1(Conj, RestConj, CA, NewA):-
  (CA = once(OA) ->
    transform_parallel1(Conj, RestConj, OA, NA),
    NewA = once(NA)
  ;
   Conj = (NewA, RestConj) ->
     true
  ;
   Conj = NewA % end of conjuction
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% clauseLength(+Clause, -NumLiterals)
%
%  Given:
%    Clause: a proper Prolog clause (e.g. Head:-Body, or just Head)
%
%  Returns:
%    NumLiterals: the number of literals in Clause
%
%  Example:
%    clauseLength((a(X):-b(X,5)), 2).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clauseLength((_H:-Body), N):-
  !, list2Body(BodyLiterals, Body),
  length(BodyLiterals, N1),
  N is N1+1. % +1 to account for the head literal
clauseLength(_, 1). % bodyless clause

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% singletons(+Literals, -Singletons)
%
%  Given:
%    Literals: a clause represent by a list of literals
%
%  Returns:
%    Singletons: a list of the singletons variables in clause
%                (a singleton is a variable that appears only once)
%
%  Example:
%    singletons((a(X):-b(X,Y),c(Y,Z,D)), [Z,D]).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

singletons(Literals, Singletons):-
  variables(Literals, Variables),
  singleOccurrences(Variables, Singletons).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% variables(+Terms, -Variables)
%
%  Given:
%    Terms: a list of terms
%
%  Returns:
%    Variables: a list of all variables occuring in terms (possibly with duplicates)
%
%  Example:
%    variables([a(X),b(X,Y),c(Y,Z,D)], [X,Y,Z,D])
%
%  Notes:
%   Library terms (use_module(library(terms)) defines term_variables(+Term, -Vars) which returns all
%   the unique variables of a term
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

variables([], []).
variables([Term|Terms], [Term|Variables]):-
  var(Term),!,% Term is a variable
  variables(Terms, Variables).
variables([Term|Terms], Variables):-
  ground(Term),!, % Term is fully ground (i.e. contains no variables)
  variables(Terms, Variables).
variables([ComplexTerm|Terms], Variables):-
  ComplexTerm=..[_|Args],
  append(Args, Terms, NTerms),
  variables(NTerms, Variables).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% singleOccurrences(+InList, -OutList)
%
%  Given:
%   InList: an unsorted list of possibly repeated values or variables
%
%  Returns:
%   OutList: a list with all the elements in InList that occur only once in it
%
%  Notes:
%   We cannot sort InList nor unify its members as it may contain variables we don't want to bind
%   There this predicate has complexity O(N^2) in the number of elements of InList
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

singleOccurrences([], []).
singleOccurrences([H|T], R):-
  occurs(H, T),!,
  delete(T, H, NT), % delete all occurrences of H in T
  singleOccurrences(NT, R).
singleOccurrences([H|T], [H|R]):-
  singleOccurrences(T, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% occurs(+Element, +List)
%
%  Given:
%    Element: a value or a variable
%    List: a list of values and/or variables
%
%  Succeeds if Element occurs in List
%
% Notes:
%   This function is identical to member/2, except that we do not bind any variable, just check for equality
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

occurs(E, [H|_]):- E==H,!.
occurs(E, [_|T]):-
  occurs(E, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% prettyPrintLiterals(+Clause)
%
% Given:
%   Clause: list of literals
%
% Pretty prints it to stdout
%
% Notes:
%   This pretty print code is adapted from Aleph. Default number of literals per column is 4
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prettyPrintLiterals(ClauseAsLiterals):-
  setting(print, N),
  prettyPrintLiterals(ClauseAsLiterals, N).

prettyPrintLiterals(Clause, N):-
  copy_term(Clause, [Head1|Body1]),
  numbervars([Head1|Body1], 0, _),
  write_literal(Head1),
  (Body1 = [] -> write('.'); write(':-')), nl,
  print_litlist(Body1, 1, N).

write_literal(Lit):-
  write_term(Lit, [numbervars(true), quoted(true)]).

print_litlist([], _, _).
print_litlist([Lit], LitNum, _):-
  !,
  print_lit(Lit, LitNum, LitNum, '.', _).
print_litlist([Lit|Lits], LitNum, LastLit):-
  print_lit(Lit, LitNum, LastLit, ', ', NextLit),
  print_litlist(Lits, NextLit, LastLit).
print_lits((Lit,Lits), LitNum, LastLit):-
  !,
  print_lit(Lit, LitNum, LastLit, ', ', NextLit),
  print_lits(Lits, NextLit, LastLit).
print_lits(Lit, LitNum,_):-
  print_lit(Lit, LitNum, LitNum, '.', _).

print_lit(Lit, LitNum, LastLit, Sep, NextLit):-
  (LitNum = 1 -> tab(3); true),
  write_literal(Lit),
  format("~w", [Sep]),
  (LitNum=LastLit-> nl, NextLit=1; NextLit is LitNum + 1).
