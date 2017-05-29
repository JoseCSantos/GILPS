%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-08-25
%
%  This module countais two predicates that are a variant of findall
%
%  collect_solutions/4: identical to findall but returns up to N solutions rather than all
%  count_solutions/3: identical to collect_solutions/4 but only counts solutions rather
%                     than storing them
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- module(goal_solutions,
            [
               call_n/2,
               collect_solutions/4,
               count_solutions/3
            ]
         ).

% YAP modules
:- use_module(library(nb), [nb_queue/1, nb_queue_enqueue/2, nb_queue_size/2, nb_queue_close/3]).
%Note: nb_queue/2 does not appear in the import list because it's only supported in YAP 5.1.4 and later

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% call_n(+Goal, +MaxSolutions)
%
% Given:
%   Goal: what is to be executed (i.e. a predicate or conjunction of predicates)
%   MaxSolutions: maximum number of times Goal is allowed to succeed (>0)
%
% On success binds goal with a valid variable substitution
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate call_n(:, ?).

call_n(Goal, MaxSolutions):-
   nb_setval(call_n, 0),
   call(Goal),
   nb_getval(call_n, N),
   N1 is N+1,
   nb_setval(call_n, N1),
   (N1<MaxSolutions -> true ; !).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% collect_solutions(+Template, +Generator, +MaxSolutions, -ResultList):
%
% Given:
%   Tempate: Template to capture (must occur in Generator).
%   Generator: what is executed at each turn  (i.e. a predicate or conjunction of predicates)
%   MaxSolutions: maximum number of solutions allowed (0 for all, which is the same as findall)
%
% Returns:
%   ResultList: list, with at most MaxSolutions elements, all elements of Template format
%               resulting in executing Generator up to MaxSolutions times
%
%   e.g. collect(a(X), member(X, [1,2,3,4,5]), 3, [a(1),a(2), a(3)])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate collect_solutions(?, :, ?, ?). %the second argument must be expanded. It is a goal that needs to be executed in its module

collect_solutions(Template, Generator, MaxSolutions, Answers):-
  nb_queue(Queue), % since Yap 5.1.4 nb_queue/2 exists (e.g. nb_queue(Queue, MaxSolutions)) but apparently is no improvement
  (collect_solutions_aux(Queue, Template, Generator, MaxSolutions) ; nb_queue_close(Queue, Answers, [])). % ; is an or..

:- meta_predicate collect_solutions_aux(?, ?, :, ?).

collect_solutions_aux(Ref, Template, Generator, MaxSolutions):-
  call(Generator),
  nb_queue_enqueue(Ref, Template),
  nb_queue_size(Ref, MaxSolutions),!,
  fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% count_solutions(+Goal, +MaxSolutions, -NumSolutions):
%
% Given:
%   Goal: what is to be executed (i.e. a predicate or conjunction of predicates)
%   MaxSolutions: maximum number of times Goal is allowed to succeed
%
% Returns:
%   NumSolutions: Number of times Goal succeeded (up to MaxSolutions)
%
% Notes:
%   This is identical to collect/4 but just counts the solutions, does not store them
%
%   E.g. count_solutions(member(X, [1,2,3,4,5]), 10, 5)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate count_solutions(:, ?, ?).

count_solutions(Goal, MaxSolutions, CountSolutions):-
   nb_setval(count_sols, 0),
   copy_term(Goal, GoalC), % copy goal temporarly
                           % If we didn't do this we could run into trouble in case there is a timeout
   (count_solutions_aux(GoalC, MaxSolutions) ; nb_getval(count_sols, CountSolutions)),
   nb_delete(count_sols).

:- meta_predicate count_solutions(:, ?).

count_solutions_aux(Goal, MaxSolutions):-
   call(Goal),               % if there is a timeout after this is executed, but before the fail, goal would become bound and we do not want that!
   nb_getval(count_sols, Value),
   Value1 is Value+1,
   nb_setval(count_sols, Value1),
   Value1=MaxSolutions,!, %keeps failing until number solutions equals max solutions
   fail.
