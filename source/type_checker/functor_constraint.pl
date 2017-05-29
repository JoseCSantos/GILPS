:- module(functor_constraint,[functor_constraint/4]).
:- use_module(library(apply_macros), [maplist/2]). % for maplist/*

%%%%%%%%%%%%%%%%

:- use_module(library(atts)). % JCAS: add support for put_attr without having to include SWI

t_put_attr(Var, Mod, Att) :-
 functor(AttTerm, Mod, 2),
 arg(2, AttTerm, Att),
 put_module_atts(Var, AttTerm).

%%%%%%%%%%%%%%%%


functor_constraint(Term,Type,Args,ArgTypes) :-
	check_propagator(Term,Type,Args,ArgTypes,Results),
	Results \== [], % no solution
	( Results = [Result] -> % one solution
		Result = constructor_info(Term,Type,Args,ArgTypes)
	; % multiple solutions
		term_variables([Type|ArgTypes],SuspensionVars),
		Closure = functor_constraint_reactivation(Term,Type,Args,ArgTypes,_KillFlag),
		suspend_functor_constraint(SuspensionVars,Closure)	
	).	

functor_constraint_reactivation(Term,Type,Args,ArgTypes,KillFlag,Var) :-
	( var(KillFlag) ->
		check_propagator(Term,Type,Args,ArgTypes,Results),
		Results \== [], % no solution
		( Results = [Result] -> % one solution
			Result = constructor_info(Term,Type,Args,ArgTypes),
			KillFlag = dead
		; % multiple solutions
			% TODO: narrow possibilities for argument types 
			%	using type domain
			( nonvar(Var) -> 
				term_variables(Var,SuspensionVars),
				Closure = functor_constraint_reactivation(Term,Type,Args,ArgTypes,_KillFlag),
				suspend_functor_constraint(SuspensionVars,Closure)
			;
				true
			)
		)	
	;
		true
	).

suspend_functor_constraint(Vars,Closure) :-
	maplist(var_suspend_functor_constraint(Closure),Vars).

var_suspend_functor_constraint(Closure,Var) :-
	t_put_attr(Var,functor_constraint,Closure).

attr_unify_hook(Closure,Term) :-
	call(Closure,Term).

check_propagator(Term,Type,Args,ArgTypes,Results) :-
	copy_term_nat(propagator(Term,Type,Args,ArgTypes)
	     ,propagator(TermC,TypeC,ArgsC,ArgTypesC)),
	findall(constructor_info(TermC,TypeC,ArgsC,ArgTypesC),type_check:constructor_info(TermC,TypeC,ArgsC,ArgTypesC),Results).
