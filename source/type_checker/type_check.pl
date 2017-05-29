%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Hindley-Milner Type Checker for Prolog
%
% All authors agree to the licences of SWI-Prolog and YAP 
%
% AUTHORS OF CODE: 
%	Tom Schrijvers
%       Bart Demoen
%	Markus Triska
%	YOUR NAME HERE
%
% ACKNOWLEDGEMENTS:
%	Ulrich Neumerkel for providing feedback	
%	Vitor Santos Costa
%	Jose Santos
%	YOUR NAME HERE
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DOCUMENTATION
%
% Type Definitions
% ----------------
%
% Define polymorphic algebraic data types like:
%
%	:- type pair(A,B)    	---> A - B.
%	:- type list(T) 	---> [] ; [T|list(T)].
%	:- type boolean    	---> true ;  false.
%
% (NOTE: the above types are predefined, as well as integer and float.)
%
% Type definitions can also be empty, e.g.
%
%	:- type an_empty_type.
%
% This means that the type is not inhabited by instantiated values. Only
% logical variables are possible.
%
% Predicate Signatures
% --------------------
%
% Predicates are given a signature like:
%
%	:- pred append(list(E), list(E), list(E)).
%	:- pred not(boolean, boolean).
%	:- pred lookup(list(pair(Key,Value)), Key, Value).
%
% Interfacing Untyped Code
% ------------------------
%
% 1) Calling typed code from untyped code (and the Prolog top-level)
%    results in runtime type checks.
%
% 2) One may annotate calls to untyped predicates from within typed predicates:
%
%       :- pred concat(list(list(integer)),list(integer)).
%
%	concat(LL,L) :- flatten(LL,L) :: flatten(list(list(integer)),list(integer)).
%
%    which results in runtime type checking. The annotation is also used for static
%    type checking of the code surrounding the annotated call.
%
%    A variant of the annotation is only used for static type checking, and does
%    not result in runtime checks:
%	
%	concat(LL,L) :- flatten(LL,L) :< flatten(list(list(integer)),list(integer)).
%
% 3) A second way is to provide a signature for untypable code with: 
%	
%	:- trust_pred sort(list(integer),list(integer)).
%
%    This signature is only into account when checking calls from
%    typed code.
%
% Coping with Untypable Code
% --------------------------
%
% Untypable code, e.g. using Prolog built-ins, may be encapsulated 
% in a trusted predicate. E.g.
%
%	:- trust_pred new_array(list(T),array(T)).
%
%	new_array(List,Array) :- Array =.. [array|List].
%
% No additional runtime checks are performed for trusted predicates.
%
% Similarly, untyped imported predicates may be given a type signature
% with the trust_pred declaration.
%
%
% Type Checker Options
% --------------------
%
% Options can be passed to the type checker with the declaration
%
%	:- type_check_options(Options).
%
% where Options is a list containing zero or more of the following elements:
%
%	check(Flag) where Flag is on or off, 
%		to enable or disable the type checker
%		enabled by default
%
%	runtime(Flag) where Flag is on or off,
%		to enable or disable runtime type checking
%		disabled by default
%
%	verbose(Flag) where Flag is on or off,
%		to enable or disable printed summary at end of type checking
%		enabled by default
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% CURRENT LIMITATIONS 
%
%	* global namespace for types
%	* runtime type checks are not exhaustive for (non-ground) polymorphic types
%
% TODO:
%	* check uniqueness of defined types, e.g. list(T) not defined twice
%	* check syntactic well-formedness of type definitions and declarations
%	* add module awareness for predicates
%	* add module awareness for types 
%	* take care with variables used in :: (also used for values / other annotations)
%	* improve error messages with tc_stats(Errors,Total)
%		- source location information
%	  	- what the inconsistency is
%	* support for more built-ins 
%	* higher-order types for meta-predicates
%	* exported vs. hidden types
%	* abstract types (hidden definition)
%	* automatic inference of signatures
%	* type classes
%
% CHANGES:
%	* added cmp/0 type
%	* added compare/3 built-in
%	* added statistics printing at end of type checking
%	* fixed detection of less general types than signature
%	* added error message for less polymorphic signature
%	* added error message for duplicate predicate signature
%	* added :< annotation, which is a variant of  the :: annotation,
%	        where the semantics is not to include runtime assertions, 
%               but to simply trust the programmer.
%	* added type pred/0 for goals
%	* added call/1 built-in
%	* added type pred/1 and pred/2
%	* addded call/1 and call/2 built-ins
%	* improved error message for less polymorphic inferred types
%	* support for built-in type `float'
%	* added string/0 type
%	* added get_char/1 built-in
%	* added atom_concat/3 built-in
%	* added atom_length/2 built-in
%	* added atom_chars/2 built-in
%	* added concat_atom/2 built-in
%	* added any/0 type
%	* added coercion predicate any_to_type/3
%	* added coercion predicate type_to_any/2
%	* normalize all types, also built-in ones
%	* option to enable/disable type-checking
%	* option to enable/disable runtime type checks
%	* added empty type definitions
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

:- module(type_check,
	  [ op(1150, fx, type)
	  , op(1130, xfx, --->)
	  , op(1150, fx, pred)
	  , op(1150, fx, trust_pred)
	  , op(500,yfx,::)
	  , op(500,yfx,:<)
	  ]).

:- use_module(library(lists)).
:- use_module(library(apply_macros)).
:- use_module(library(terms), [variant/2]).
:- use_module(functor_constraint).

:- op(1150, fx, type).
:- op(1130, xfx, ---> ).
:- op(1150, fx, pred).
:- op(500,yfx,::).
:- op(500,yfx,:<).

:- multifile
	user:term_expansion/2,
	user:goal_expansion/2,
	prolog:message/3,
	constructor/4,
	constructor_info/4,
	signature/4,
	trusted_predicate/1,
	basic_normalize/2.

:- dynamic
	user:term_expansion/2,
	user:goal_expansion/2,
	signature/4,
	constructor_info/4,
	trusted_predicate/1,
	basic_normalize/2.

tc_version('$Id: type_check.pl,v 1.45 2009-11-17 toms Exp $').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%% Type checker options {{{

:- nb_setval(type_check_runtime,off).
:- nb_setval(type_check,on).
:- nb_setval(type_check_verbose,on).

handle_options(List) :- maplist(handle_option,List).

handle_option(verbose(Flag)) :- !, nb_setval(type_check_verbose,Flag).
handle_option(runtime(Flag)) :- !, nb_setval(type_check_runtime,Flag).
handle_option(check(Flag))   :- !, nb_setval(type_check,Flag).
handle_option(Other)	     :- format('Unsupported type checker option `~w\'.\n',[Other]).


type_checking_runtime :- nb_getval(type_check_runtime,on).
type_checking_verbose :- nb_getval(type_check_verbose,on).
type_checking         :- nb_getval(type_check,on).

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 




type_check_term(Term,ExpectedType,EnvIn,EnvOut) :-
	normalize_type(ExpectedType,NormalExpectedType),
	type_check_term_(Term,NormalExpectedType,EnvIn,EnvOut).

type_check_term_(Term,ExpectedType,EnvIn,EnvOut) :-
	var(Term), !,
	( lookup_eq(EnvIn,Term,EnvType) ->
		( equate_types(ExpectedType,EnvType) ->
			true
		;
			term_type_error(Term,ExpectedType,EnvType)
		),
		EnvIn = EnvOut
	;	
		EnvOut = [Term-ExpectedType|EnvIn]
	).
type_check_term_(Term,Type,EnvIn,EnvOut) :-
	integer(Term), !,
	( equate_types(Type,integer) ->
		EnvIn = EnvOut
	;
		term_type_error(Term,integer,Type)
	).
type_check_term_(Term,Type,EnvIn,EnvOut) :-
	float(Term), !,
	( equate_types(Type,float) ->
		EnvIn = EnvOut
	;
		term_type_error(Term,float,Type)
	).

type_check_term_(Term,Type,EnvIn,EnvOut) :-
	Type == (pred), !,
	type_check_control(Term,top,EnvIn,EnvOut).

type_check_term_(Term,Type,EnvIn,EnvOut) :-
	nonvar(Type),
	Type = pred(ArgType), !,
	Term =.. [Functor|Args],
	append(Args,[DummyArg],FullArgs),
	Goal =.. [Functor|FullArgs],
	type_check_control(Goal,top,[DummyArg-ArgType|EnvIn],EnvOut).

type_check_term_(Term,Type,EnvIn,EnvOut) :-
	nonvar(Type),
	Type = pred(ArgType1,ArgType2), !,
	Term =.. [Functor|Args],
	append(Args,[DummyArg1,DummyArg2],FullArgs),
	Goal =.. [Functor|FullArgs],
	type_check_control(Goal,top,[DummyArg1-ArgType1,DummyArg2-ArgType2|EnvIn],EnvOut).

type_check_term_(Term,Type,EnvIn,EnvOut) :-
	Type == string, !,
	( atom(Term) -> EnvIn = EnvOut
	; term_type_error(Term,unknown_type,Type)
	).

type_check_term_(_Term,Type,EnvIn,EnvOut) :-
	Type == any, !,
	EnvIn = EnvOut.

type_check_term_(Term,Type,EnvIn,EnvOut) :-
	% constructor(Term,Type,EnvIn,EnvOut), !.
	functor_constraint(Term,Type,Args,Types), !,
	type_check_terms(Args,Types,EnvIn,EnvOut).

type_check_term_(Term,Type,_EnvIn,_EnvOut) :-
	term_type_error(Term,unknown_type,Type).

type_check_terms([],[],Env,Env).
type_check_terms([Term|Terms],[Type|Types],Env1,Env3) :-
	type_check_term(Term,Type,Env1,Env2),
	type_check_terms(Terms,Types,Env2,Env3).

term_type_error(Term,ExpectedType,EnvType) :-
	throw(error(type_error(Term,ExpectedType,EnvType))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

constructor_clauses((A;B),Type) --> !,
	constructor_clauses(A,Type),
	constructor_clauses(B,Type).
constructor_clauses(Constructor,Type) -->
	{ functor(Constructor, Name, Arity),
	  functor(Term, Name, Arity),
	  Term        =.. [_|Args],
	  Constructor =.. [_|Types],
	  args_body(Args,Types,Body,EnvIn,EnvOut)
	},
	[ ( type_check:constructor(Term, ExpectedType, EnvIn, EnvOut) :-
		( type_check:equate_types(ExpectedType,Type) ->
			true
		;
			type_check:term_type_error(Term,ExpectedType,Type)
		),
		Body
	  )
	],
	constructor_info_clause(Constructor,Type).

constructor_info_clause(Constructor,Type) -->
	{ functor(Constructor, Name, Arity),
	  functor(Term, Name, Arity),
	  Term        =.. [_|Args],
	  Constructor =.. [_|Types],
	  Clause = type_check:constructor_info(Term, Type, Args, Types)
	},
	[ Clause
	].
				
args_body([],[],true,Env,Env).
args_body([Term|Terms],[Type|Types],(type_check:type_check_term(Term,Type,EnvIn,Env),Body),EnvIn,EnvOut) :-
	args_body(Terms,Types,Body,Env,EnvOut).

signature_clause(Signature, Clause) :-
	( check_signature(Signature) ->
		signature_clause_(Signature, Clause)
	;
		true
	).


signature_clause_(Signature,Clause) :-
	functor(Signature,Name,Arity),
	functor(Call,Name,Arity),
	Call      =.. [_|Args],
	Signature =.. [_|Types],	
	args_body(Args,Types,Body,EnvIn,EnvOut),
	Clause = 
	( type_check:signature(Call,Types,EnvIn,EnvOut) :-
		Body
	).

check_signature(Signature) :-
	nonvar(Signature),
	functor(Signature,Name,Arity),
	functor(Prototype,Name,Arity),
	( signature(Prototype,_,[],_) ->
		duplicate_signature_error(Signature),
		fail
	;
		true
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
type_check_file(NClauses) :-
	findall(Clause,retract(clause_to_check(Clause)),Clauses),
	( type_checking ->
		type_check_clauses(Clauses,Stats),
		( type_checking_runtime ->
			transform_clauses(Clauses,NClauses)
		;
			NClauses = Clauses
		),
		final_message(Stats)
	;
		NClauses = Clauses	
	).

type_check_clauses(Clauses,Stats) :-
	init_stats(Stats0),
	type_check_clauses(Clauses,Stats0,Stats).

type_check_clauses([],Stats,Stats).
type_check_clauses([Clause|Clauses],Stats0,Stats) :-
	catch(
		( type_check_clause(Clause) , 
		  inc_ok_stats(Stats0,Stats1)
		)
	     ,  type_error
	     ,  ( format('TYPE ERROR in clause: \n\n',[]),
	  	  portray_clause(Clause),
		  inc_error_stats(Stats0,Stats1)
		)
	     ),
	type_check_clauses(Clauses,Stats1,Stats).

type_check_clause((:- _)) :- !,
	true. % ignoring
type_check_clause((Head :- Body)) :- !,
	functor(Head,P,N),
	( trusted_predicate(P/N) ->
		true
	;
		type_check_clause_main(Head,Body)
	).
type_check_clause(Head) :- 
	type_check_clause((Head :- true)).

type_check_clause_main(Head,Body) :-
	Env0 = [], 
        /* check the head */ 
        catch(
		signature(Head,ArgTypes,Env0,Env1),
		error(type_error(Term,Exp,Inf)),
		( head_error(Term,Exp,Inf,Head,Body), fail )
	),
	/* check the body */
	catch( 
	  	 type_check_control(Body,top,Env1,_Env2),
		error(type_error(Term,Exp,Inf),Context),
		(control_error(Term,Exp,Inf,Head,Context),fail)
	),
	/* check whether Head is variant of signature */
	functor(Head,Name,Arity),
	functor(Prototype,Name,Arity),
	signature(Prototype,ProtoTypes,Env0,_ProtoEnv),
	( variant(ArgTypes, ProtoTypes) % JCAS: equivalent to  ArgTypes =@= ProtoTypes but does not require SWI.pl
	 ->
	  true
	;
	  InfSig =.. [Name|ArgTypes],
	  DecSig =.. [Name|ProtoTypes],
	  less_polymorphic_error((:- pred InfSig),
	  			 (:- pred DecSig)), 
	  throw(type_error)
	). 

% context ::=
%	  top
%	| lconj parent right
%	| rconj parent left
%	| ldisj parent right
%	| rdisj parent left
%	| cond  parent then
%	| then  parent cond
%	| once  parent
%	| findall parent pattern result

% env == list(pair(var-type))

%% type_check_control(+goal,+context,+env,-env) {{{
type_check_control(G,_Context,Env1,Env2) :- var(G), !,
	type_check_term(G,(pred),Env1,Env2).

type_check_control((G1,G2),Context,Env1,Env3) :- !,
	type_check_control(G1,lconj(Context,G2),Env1,Env2),
	type_check_control(G2,rconj(Context,G1),Env2,Env3).

type_check_control((G1;G2),Context,Env1,Env3) :- !,
	type_check_control(G1,ldisj(Context,G2),Env1,Env2),
	type_check_control(G2,rdisj(Context,G1),Env2,Env3).

type_check_control((G1 -> G2),Context,Env1,Env3) :- !,
	type_check_control(G1,cond(Context,G2),Env1,Env2),
	type_check_control(G2,then(Context,G1),Env2,Env3).

type_check_control(once(G),Context,Env1,Env2) :- !,
	type_check_control(G,once(Context),Env1,Env2).

type_check_control(findall(Pattern,Goal,Result),Context,Env1,Env4) :- !,
	type_check_control(Goal,findall(Context,Pattern,Result),Env1,Env2),
	type_check_term(Pattern,Type,Env2,Env3),
	type_check_term(Result,list(Type),Env3,Env4).

type_check_control(Goal,Context,Env1,Env2) :-
	catch(
		( type_check_goal(Goal,Env1,Env2,Warnings,[]) ->
			maplist(control_warning(context(Goal,Context)),Warnings)	
		;
			term_type_error(?,?,?)
		),
		error(type_error(Term,ExpType,InfType)),
		control_type_error(type_error(Term,ExpType,InfType),Goal,Context)
	).

control_type_error(Error,Goal,Context) :-
	throw(error(Error,context(Goal,Context))).
% }}}

numeric_type(Type) :-
	when(nonvar(Type),check_numeric_type(Type)).

check_numeric_type(integer) :- !.
check_numeric_type(float) :- !.
check_numeric_type(Other) :- 
	term_type_error(some_arithmetic_expression,a_numeric_type,Other).

% type_check_goal(+goal,+env,-env,-warnings,+warnings_tail) {{{
type_check_goal((X = Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal((X \= Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal((X == Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal((X \== Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal((X @< Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal((X @> Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal((X @>= Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal((X @=< Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal(copy_term(X,Y),Env1,Env3,W,W) :- !,
	type_check_term(X,Type,Env1,Env2),
	type_check_term(Y,Type,Env2,Env3).
type_check_goal(compare(R,X,Y),Env1,Env4,W,W) :- !,
	type_check_term(R,cmp,Env1,Env2),
	type_check_term(X,Type,Env2,Env3),
	type_check_term(Y,Type,Env3,Env4).
type_check_goal((X is Y),Env1,Env3,W,W) :- !,
	numeric_type(Type),
	type_check_term(X,Type,Env1,Env2),
	type_check_expression(Y,Type,Env2,Env3).
type_check_goal((X > Y),Env1,Env3,W,W) :- !,
	numeric_type(Type),
	type_check_expression(X,Type,Env1,Env2),
	type_check_expression(Y,Type,Env2,Env3).
type_check_goal((X < Y),Env1,Env3,W,W) :- !,
	numeric_type(Type),
	type_check_expression(X,Type,Env1,Env2),
	type_check_expression(Y,Type,Env2,Env3).
type_check_goal((X =< Y),Env1,Env3,W,W) :- !,
	numeric_type(Type),
	type_check_expression(X,Type,Env1,Env2),
	type_check_expression(Y,Type,Env2,Env3).
type_check_goal((X >= Y),Env1,Env3,W,W) :- !,
	numeric_type(Type),
	type_check_expression(X,Type,Env1,Env2),
	type_check_expression(Y,Type,Env2,Env3).
type_check_goal((X =:= Y),Env1,Env3,W,W) :- !,
	numeric_type(Type),
	type_check_expression(X,Type,Env1,Env2),
	type_check_expression(Y,Type,Env2,Env3).
type_check_goal((X =\= Y),Env1,Env3,W,W) :- !,
	numeric_type(Type),
	type_check_expression(X,Type,Env1,Env2),
	type_check_expression(Y,Type,Env2,Env3).

type_check_goal(arg(I,_,_),Env1,Env2,W,W) :- !,
	type_check_term(I,integer,Env1,Env2).
type_check_goal(functor(Term,Functor,I),Env1,Env3,W,W) :- !,
	type_check_term(I,integer,Env1,Env2),
	( nonvar(I) -> I >= 0 ; true ),
	type_check_term(Term,Type,Env2,Env3),
	( nonvar(Functor) ->
		atomic(Functor),
		( nonvar(I), nonvar(Type) ->
			functor(Dummy,Functor,I),
			constructor(Dummy,Type,[],_Env)	
		;
			true
		)	
	;
		true % ignore functor
	).
type_check_goal(integer(I),Env1,Env2,W,W) :- !,
	type_check_term(I,integer,Env1,Env2).
type_check_goal(float(I),Env1,Env2,W,W) :- !,
	type_check_term(I,float,Env1,Env2).

type_check_goal(true,Env1,Env2,W,W) :- !, Env1 = Env2.
type_check_goal(fail,Env1,Env2,W,W) :- !, Env1 = Env2.
type_check_goal(!,Env1,Env2,W,W) :- !, Env1 = Env2.
type_check_goal(abort,Env1,Env2,W,W) :- !, Env1 = Env2.

type_check_goal(writeln(Term),Env1,Env2,W,W) :- !, type_check_term(Term,_Type,Env1,Env2).
type_check_goal(format(_,_),Env1,Env2,W,W) :- !, Env1 = Env2.

type_check_goal(var(Term),Env1,Env2,W,W) :- !, type_check_term(Term,_Type,Env1,Env2).
type_check_goal(nonvar(Term),Env1,Env2,W,W) :- !, type_check_term(Term,_Type,Env1,Env2).
type_check_goal(ground(Term),Env1,Env2,W,W) :- !, type_check_term(Term,_Type,Env1,Env2).

type_check_goal(atom_chars(A1,A2),Env1,Env3,W,W) :- !,
	type_check_term(A1,string,Env1,Env2),
	type_check_term(A2,list(string),Env2,Env3).
type_check_goal(atom_concat(A1,A2,A3),Env1,Env4,W,W) :- !,
	type_check_term(A1,string,Env1,Env2),
	type_check_term(A2,string,Env2,Env3),
	type_check_term(A3,string,Env3,Env4).
type_check_goal(atom_length(A1,A2),Env1,Env3,W,W) :- !,
	type_check_term(A1,string,Env1,Env2),
	type_check_term(A2,integer,Env2,Env3).
type_check_goal(concat_atom(A1,A2),Env1,Env3,W,W) :- !,
	type_check_term(A1,list(string),Env1,Env2),
	type_check_term(A2,string,Env2,Env3).
type_check_goal(get_char(A1),Env1,Env2,W,W) :- !,
	type_check_term(A1,string,Env1,Env2).

type_check_goal(throw(_),Env1,Env2,W,W) :- !, Env1 = Env2.
type_check_goal(catch(Goal,_,Handler),Env1,Env3,W1,W3) :- !, 
	type_check_goal(Goal,Env1,Env2,W1,W2),
	type_check_goal(Handler,Env2,Env3,W2,W3).


type_check_goal(call(Goal),Env1,Env2,W,W) :- !,
	type_check_term(Goal,(pred),Env1,Env2).

type_check_goal(call(Goal,Arg),Env1,Env3,W,W) :- !,
	type_check_term(Goal,pred(Type),Env1,Env2),
	type_check_term(Arg, Type,      Env2,Env3).

type_check_goal(call(Goal,Arg1,Arg2),Env1,Env4,W,W) :- !,
	type_check_term(Goal,pred(Type1,Type2),Env1,Env2),
	type_check_term(Arg1,Type1,            Env2,Env3),
	type_check_term(Arg2,Type2,            Env3,Env4).

type_check_goal(Goal :: Signature, Env1, Env3,W,W) :- !,
	/* first take into account the predicate signatures
	   if one exists 				    */
	( participating_predicate(Goal) ->
		signature(Goal,_,Env1,Env2)
	;
		Env2 = Env1
	),
	functor(Goal,F,A),
	functor(Signature,F,A),
	Goal      =.. [_|Args],
	Signature =.. [_|Types],
	type_check_terms(Args,Types,Env2,Env3).	
type_check_goal(Goal :< Signature, Env1, Env3,W,W) :- !,
	/* first take into account the predicate signatures
	   if one exists 				    */
	( participating_predicate(Goal) ->
		signature(Goal,_,Env1,Env2)
	;
		Env2 = Env1
	),
	functor(Goal,F,A),
	functor(Signature,F,A),
	Goal      =.. [_|Args],
	Signature =.. [_|Types],
	type_check_terms(Args,Types,Env2,Env3).	

type_check_goal(type_to_any(A1,A2),Env1,Env3,W,W) :- !,
	type_check_term(A1,_Type,Env1,Env2),
	type_check_term(A2,any,Env2,Env3).

type_check_goal(any_to_type(A1,A2,Type),Env1,Env3,W,W) :- !,
	type_check_term(A1,any,Env1,Env2),
	type_check_term(A2,Type,Env2,Env3).

type_check_goal(Goal,Env1,Env2,W,W) :- 
	participating_predicate(Goal), !,
	signature(Goal,_,Env1,Env2).

type_check_goal(Goal,Env1,Env2,W,RW) :-
	/* all other predicates are simply ignored */
	Warning = unknown_predicate_call(Goal),
 	W = [Warning|RW],		
	Env1 = Env2.
% }}}

% type_check_expression(+expression,+type,+env,-env) {{{
type_check_expression(Exp,Type,Env1,Env2) :-
	var(Exp), !,
	type_check_term(Exp,Type,Env1,Env2).
type_check_expression(random,Type,Env1,Env1) :- !,  % NOTE: only supported by Yap
	equate_types(Type,float).
type_check_expression((-Exp),Type,Env1,Env2) :- !,
	type_check_expression(Exp,Type,Env1,Env2).	
type_check_expression((\Exp),Type,Env1,Env2) :- !,
	equate_types(Type,integer),
	type_check_expression(Exp,Type,Env1,Env2).	
type_check_expression(abs(Exp),Type,Env1,Env2) :- !,
	type_check_expression(Exp,Type,Env1,Env2).	
type_check_expression(log(Exp),Type,Env1,Env2) :- !,
	equate_types(Type,float),
	type_check_expression(Exp,Type,Env1,Env2).	
type_check_expression(integer(Exp),Type,Env1,Env2) :- !,
	equate_types(Type,float), % explicit conversion from integer to float
	type_check_expression(Exp,integer,Env1,Env2).	
type_check_expression(sign(Exp),Type,Env1,Env2) :- !,
	type_check_expression(Exp,Type,Env1,Env2).	
type_check_expression((Exp1+Exp2),Type,Env1,Env3) :- !,
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1-Exp2),Type,Env1,Env3) :- !, 
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1*Exp2),Type,Env1,Env3) :- !,
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1/Exp2),Type,Env1,Env3) :- !,
	equate_types(Type,float),
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1//Exp2),Type,Env1,Env3) :- !,
	equate_types(Type,integer),
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1**Exp2),Type,Env1,Env3) :- !,
	equate_types(Type,float),
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1 mod Exp2),Type,Env1,Env3) :- !, 
	equate_types(Type,integer),
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression(min(Exp1,Exp2),Type,Env1,Env3) :- !, 
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression(max(Exp1,Exp2),Type,Env1,Env3) :- !, 
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1 >> Exp2),Type,Env1,Env3) :- !, 
	equate_types(Type,integer),
	type_check_expression(Exp1,Env1,Env2),	
	type_check_expression(Exp2,Env2,Env3).	
type_check_expression((Exp1 << Exp2),Type,Env1,Env3) :- !, 
	equate_types(Type,integer),
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1 /\ Exp2),Type,Env1,Env3) :- !, 
	equate_types(Type,integer),
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression((Exp1 \/ Exp2),Type,Env1,Env3) :- !, 
	equate_types(Type,integer),
	type_check_expression(Exp1,Type,Env1,Env2),	
	type_check_expression(Exp2,Type,Env2,Env3).	
type_check_expression(Exp,Type,Env1,Env2) :-
	/* catch all */
	type_check_term(Exp,Type,Env1,Env2).
% }}}

unify_args([],[],Env,Env).
unify_args([X|Xs],[Y|Ys],Env1,Env3) :-
	type_check_goal((X = Y), Env1, Env2,_,[]),
	unify_args(Xs,Ys,Env2,Env3).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% ERROR MESSAGES

head_error(Term,ExpType,InfType,Head,Body) :-
	format('TYPE ERROR: expected type `~w\' for term `~w\'\n',[ExpType,Term]),
	format('            inferred type `~w\'\n',[InfType]),
	format('\tin head `~w\' of clause:\n',[Head]),
	portray_clause((Head :- Body)).

less_polymorphic_error(InfSig,DecSig) :-
	numbervars(InfSig,0,_),
	numbervars(DecSig,0,_),
	format('TYPE ERROR: Inferred signature is less polymorphic than declared signature.\n',[]), 
	format('            inferred signature `~p\'\n',[InfSig]),
	format('            declared signature `~p\'\n',[DecSig]).

duplicate_signature_error(Signature) :-
	format('TYPE ERROR: Predicate already has a signature.\n',[]), 
	format('            duplicate signature `~w\'\n',[Signature]),
	format('            Ignoring duplicate signature.\n',[]). 

% control_error(+term,+type,+type,+head,+context) {{{ 
control_error(Term,ExpType,InfType,Head,context(Source,Context)) :-
	format('TYPE ERROR: expected type `~w\' for term `~w\'\n',[ExpType,Term]),
	format('            inferred type `~w\'\n',[InfType]),
	format('\tin goal:\n\t\t ~w\n\tin clause:\n',[Source]),
	assemble_marked_body(Context,'HERE'(Source),MarkedBody),
	portray_clause((Head :- MarkedBody)).

control_warning(Context,Warning) :-
	control_warning_(Warning,Context).

control_warning_(unknown_predicate_call(Call),context(Source,Context)) :-
	format('TYPE WARNING: call to unknown predicate `~w\'\n',[Call]),
	format('    Possible Fixes: - add type annotation `::\' to call\n',[]),
	format('                    - replace with call to other predicate\n',[]),
	assemble_marked_body(Context,'HERE'(Source),MarkedBody),
	portray_clause(('...' :- MarkedBody)).

prolog:message(error(type_error(Term,ExpectedType,InferredType))) -->
	[ '\n\tTYPE ERROR: expected type `~w\' for term `~w\'\n' - [ExpectedType, Term],
	  '\t            inferred type `~w\'\n' - [InferredType]
	].
% }}}

% assemble_marked_body(+context,+goal,-goal) {{{
assemble_marked_body(top,Acc,Body) :- Body = Acc.
assemble_marked_body(lconj(Context,Right),Acc,Body) :-
	assemble_marked_body(Context,(Acc,Right),Body).
assemble_marked_body(rconj(Context,Left),Acc,Body) :-
	assemble_marked_body(Context,(Left,Acc),Body).
assemble_marked_body(ldisj(Context,Right),Acc,Body) :-
	assemble_marked_body(Context,(Acc;Right),Body).
assemble_marked_body(rdisj(Context,Left),Acc,Body) :-
	assemble_marked_body(Context,(Left;Acc),Body).
assemble_marked_body(cond(Context,Then),Acc,Body) :-
	assemble_marked_body(Context,(Acc->Then),Body).
assemble_marked_body(then(Context,Cond),Acc,Body) :-
	assemble_marked_body(Context,(Cond->Acc),Body).
assemble_marked_body(once(Context),Acc,Body) :-
	assemble_marked_body(Context,once(Acc),Body).
assemble_marked_body(findall(Context,Pattern,Result),Acc,Body) :-
	assemble_marked_body(Context,findall(Pattern,Acc,Result),Body).
% }}}	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Transform clauses: 	{{{
%
% 	p(T1,...,Tn) :- B.
%
% becomes: 
%
%	p(X1,...,Xn) :- CHECKS, p'(X1,...,Xn).	(* one for each predicate *)
%
%	p'(T1,...,Tn) :- B'.
% 
% where all calls to type safe predicates have been replaced in B to get B'

transform_clauses(Clauses,NClauses) :-
	wrappers(Clauses,NClauses).

wrappers(Clauses,NClauses) :-
	findall(FA,(member(Clause,Clauses), only_check_participating_clauses(Clause,FA)),FAs0),
	sort(FAs0,FAs),
	maplist(wrapper_clause,FAs,WrapperClauses),
	maplist(tc_clause,Clauses,TcClauses),
	append(WrapperClauses,TcClauses,NClauses).

% PORTRAY_CLAUSE bug?
%
% 6 ?- functor(Head,p,2), Clause = (Head :- signature(Head)), portray_clause(Clause).
% p(_, _) :-
%         signature(p(_, _)).

wrapper_clause(F/A,Clause) :-
	functor(Head,F,A),
	tc_head(Head,Call),
	Clause = (Head :- type_check:signature(Head,_,[],_), Call ).

tc_clause((Head :- Body),(TcHead :- TcBody)) :- !,
	tc_head(Head,TcHead),
	tc_body(Body,TcBody).
tc_clause(Head, TcHead) :-
	tc_head(Head,TcHead).

tc_head(Head,TcHead) :-
	Head =.. [F|Args],
	atom_concat('$tc_',F,NF),
	TcHead =.. [NF|Args].

tc_body(Var,TcBody) :- var(Var), !, TcBody = Var.
tc_body((G1,G2),TcBody) :- !,
	TcBody = (TcG1,TcG2),
	tc_body(G1,TcG1),
	tc_body(G2,TcG2).
tc_body((G1;G2),TcBody) :- !,
	TcBody = (TcG1;TcG2),
	tc_body(G1,TcG1),
	tc_body(G2,TcG2).
tc_body((G1->G2),TcBody) :- !,
	TcBody = (TcG1 -> TcG2),
	tc_body(G1,TcG1),
	tc_body(G2,TcG2).
tc_body(Body, TcBody) :-
	participating_predicate(Body), !,
	tc_head(Body,TcBody).
tc_body(Body, TcBody) :-
	TcBody = Body.
% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

only_check_participating_clauses(_) :-
	\+ type_checking, !, fail.

only_check_participating_clauses(Clause) :-
	only_check_participating_clauses(Clause,_).

only_check_participating_clauses((:- _),_) :- !, fail.
only_check_participating_clauses((Head :- _),FA) :- !,
	participating_predicate(Head),
	FA = F / A,
	functor(Head,F,A).
only_check_participating_clauses(Head,FA) :-
	participating_predicate(Head),
	FA = F / A,
	functor(Head,F,A).

participating_predicate(Head) :-
	functor(Head,Name,Arity),
	functor(Test,Name,Arity),
 	signature(Test,_,[],_).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
basic_normalize_clause(Alias,Type,Clause) :-
	Clause = type_check:basic_normalize(Alias,Type).
	
normalize_type(Type0,Type2) :-
	( nonvar(Type0), basic_normalize(Type0,Type1) ->
		normalize_type(Type1,Type2)
	;
		Type2 = Type0
	).

equate_types(Type1,Type2) :-
	( nonvar(Type1), nonvar(Type2) ->
		normalize_type(Type1,NType1),
		normalize_type(Type2,NType2),
		functor(NType1,Functor,Arity),
		functor(NType2,Functor,Arity),
		NType1 =.. [_|Args1],
		NType2 =.. [_|Args2],
		maplist(equate_types,Args1,Args2)
	;
		unify_with_occurs_check(Type1,Type2)
	).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Utility {{{

lookup_eq([K - V | KVs],Key,Value) :-
        ( K == Key ->
                V = Value
        ;
                lookup_eq(KVs,Key,Value)
        ).
snd_of_pairs([],[]).
snd_of_pairs([_-Y|XYs],[Y|Ys]) :-
        snd_of_pairs(XYs,Ys).
% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Goal expansion {{{
user:goal_expansion(UnsafeCall :: Signature, SafeCall) :- !,
	( type_checking_runtime ->
		% Already at end_of_file when this code get executed.
		% prolog_load_context(file,File),
		% prolog_load_context(term_position,'$stream_position'(_, LineNumber, _, _, _)),
		% format('Expanding annotation in ~w at line ~w\n',[File,LineNumber]),
		functor(UnsafeCall,F,A),
		functor(Signature,F,A),	
		UnsafeCall =.. [_|Args],
		Signature  =.. [_|Types],
		args_body(Args,Types,Guard,[],_),	
		SafeCall = ( UnsafeCall, ( Guard -> true ; throw(runtime_type_error(UnsafeCall))  ) )
	;
		SafeCall = UnsafeCall
	).

user:goal_expansion(UnsafeCall :< _Signature, Call) :- !,
	Call = UnsafeCall.

user:goal_expansion(type_to_any(X,Y),(X = Y)).
user:goal_expansion(any_to_type(X,Y,Type),Goal) :- !,
	( type_checking_runtime ->
		Goal = (type_check:type_check_term(X,Type,[],_), X=Y)
	;
		Goal = (X = Y)
	).
% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Term expansion {{{
%	goes last
%	otherwise we end up type checking the type checker...

user:term_expansion((:- type_check_options(Options)),[]) :-
	handle_options(Options).
user:term_expansion((:- runtime_type_check(Flag)),[]) :-
	%writeln(type_checking_runtime(Flag)),
 	handle_option(runtime(Flag)).	
user:term_expansion((:- type Name ---> Constructors),
		     Clauses
		    ) :-
	( \+ \+ ( numbervars(Name, 0, _), ground(Constructors) ) ->
		phrase(constructor_clauses(Constructors,Name), Clauses)
	;   
		format("ERROR: invalid TYPE definition~w\n\tType definitions must be range-restricted!\n", [(:- type Name ---> Constructors)]),
		Clauses = []
	).
user:term_expansion((:- type Alias == Type),
		    [ Clause
		    ]) :-
	basic_normalize_clause(Alias,Type,Clause).
user:term_expansion((:- type _Name),[]).		% empty type
user:term_expansion((:- pred Signature),
		    [ Clause
		    ]) :-
	signature_clause(Signature,Clause).
user:term_expansion((:- trust_pred Signature),
		    [ SignatureClause
		    , TrustedPredicateClause
		    ]) :-
	signature_clause(Signature,SignatureClause),
	functor(Signature,P,N),
	TrustedPredicateClause = type_check:trusted_predicate(P/N).
user:term_expansion(end_of_file,Clauses) :-
	type_check_file(Clauses).

user:term_expansion(Clause, NClause) :-
	only_check_participating_clauses(Clause),
	assert(clause_to_check(Clause)),
	NClause = [].

% }}}

% {{{
final_message(tc_stats(E,T)) :-
	( T > 0, type_checking_verbose -> 
		prolog_load_context(module,Mod),
		write('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'), nl,
		format('% Type checking for module `~w\' done:\n%\tfound type errors in ~w out of ~w clauses.\n',[Mod,E,T]),
		( E == 0 ->
			write('%\tWell-typed code can\'t go wrong!'), nl
		;
			true
		),
		write('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'), nl
	;
		true
	).

init_stats(tc_stats(0,0)).

inc_error_stats(tc_stats(E,T),tc_stats(NE,NT)) :-
	NE is E + 1,
	NT is T + 1.

inc_ok_stats(tc_stats(E,T),tc_stats(E,NT)) :-
	NT is T + 1.
% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Predefined types:	{{{
%
%  The types list(T), pair(A,B), boolean, integer and float are predefined by the type
%  checker.

:- type list(T) 	---> [] ; [T|list(T)].

:- type pair(A,B) 	---> A - B.

:- type boolean		---> true ; false.

:- type cmp		---> (=) ; (>) ; (<).
% }}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Predefined signatures:	{{{
%

% :- pred write(_).
% :- pred writeln(_).

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% BUGS FOUND {{{
% ==========
%
% In rbtrees.pl (Vitor Santos Costa)
%	
%	:- pred rb_lookupall(K,V,rbtree(K,V)).
%	:- pred lookupall(K,V,tree(K,V)).
%	:- pred lookupall(cmp,K,V,tree(K,V)).
%	
%	rb_lookupall(Key, Val, t(_,Tree)) :-
%		lookupall(Key, Val, Tree).
%	
%	lookupall(_, _, black(nil,_,_,nil)) :- !, fail.
%	lookupall(Key, Val, Tree) :-
%		getkey(Tree,KA),		% arg(2,Tree,KA),
%		compare(Cmp,KA,Key),
%		lookupall(Cmp,Key,Val,Tree).
%	
%	lookupall(>, K, V, Tree) :-
%		getright(Tree,NTree),		% arg(4,Tree,NTree),
%		rb_lookupall(K, V, NTree).	% BUG !!!
%	lookupall(=, _, V, Tree) :-
%		getvalue(Tree,V),		% arg(3,Tree,V).
%	lookupall(=, K, V, Tree) :-
%		getleft(Tree,NTree),		% arg(1,Tree,NTree),
%		lookupall(K, V, NTree).
%	lookupall(<, K, V, Tree) :-
%		getleft(Tree,NTree),		% arg(1,Tree,NTree),
%		lookupall(K, V, NTree).
%
% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%  NOTES {{{ 
%  =====
%
% In rbtrees.pl (Vitor Santos Costa)
%  * cannot share Nil in old and new tree:
% 
%	:- pred rb_clone(rbtree(K,_V1),rbtree(K,V2),list(pair(K,V2))).
%	rb_clone(t(_Nil1,T),t(Nil2,NT),Ns) :-
%		new(Nil2),
%		clone(T,NT,Ns,[]).	
%
% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

