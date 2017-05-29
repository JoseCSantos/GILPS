/*
:- modeh(1, qsort(+list,-list)).
:- modeb(1, +list=[-elem|-list]).
:- modeb(1, -list=[+elem|+list]).
:- modeb(1, part(+elem,+list,-list,-list)).
:- modeb(1, append(+list,+list,-list)).
:- modeb(1, qsort(+list,-list)).
*/
% target definition:
/*
qsort(A, B):-
  A=[C|D],          %i=1
  part(C, D, E, F), %i=2
  qsort(E, G),      %i=3
  qsort(F, H),
  I=[C|H],          %i=4
  append(G, I, B).  %i=5

*/

 % Make GILPS work with the below mode definitions
:- modeh(1,qsort([+int|+ilist],-ilist)).
:- modeb(1,part(+int,+ilist,-ilist,-ilist)).
:- modeb(1,append(+ilist,[+int|+ilist],-ilist)).
:- modeb(1,qsort(+ilist,-ilist)).

% target definition:
/*
qsort([A|B], C):-
  part(A, B, D, E), %i=1
  qsort(D, F),      %i=2
  qsort(E, G),
  append(F, [A|G], C).  %i=3

*/

:- set(i,3).
:- set(clause_length,7).

:- dynamic qsort/2.

part(_, [], [], []):-!.
part(E, [H|T], [H|SE], GE):-
  H@<E,!,
  part(E, T, SE, GE).
part(E, [H|T], SE, [H|GE]):-
  part(E, T, SE, GE).

append([], L, L).
append([H|T], L, [H|R]):-
  append(T, L, R).

qsort([], []).
example(qsort([2,1], [1,2]), 10).
example(qsort([5,4], [4,5]), 10).
example(qsort([3,2,1,5,4],[1,2,3,4,5]), 10).
/*
example(qsort([0,1,2],[0,1,2]), 1).
example(qsort([0,2,1],[0,1,2]), 1).
example(qsort([1,0,2],[0,1,2]), 1).
example(qsort([1,2,0],[0,1,2]), 1).
example(qsort([2,0,1],[0,1,2]), 1).
example(qsort([2,1,0],[0,1,2]), 1).
*/
