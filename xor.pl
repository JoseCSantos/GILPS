:- modeh(1, f(+bit, +bit, -bit)).
:- modeb(1, xor(+bit, +bit, -bit)).

xor(0,0,0).
xor(0,1,1).
xor(1,0,1).
xor(1,1,0).

:- set(verbose,2).
:- set(clause_length, 3).
:- set(nodes, 50000).

/*
f(A,B,C):-
  xor(A,B,C).
*/

%example(+f(a,b,c), Weight)
example(f(0,0,0), 10).
example(f(0,1,1), 10).
example(f(1,0,1), 10).
example(f(1,1,0), 10).
