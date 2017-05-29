:-modeh(1, fib(+int,-int)).
:-modeb(1, pred(+int,-int)).
:-modeb(1, fib(+int,-int)).
:-modeb(1, plus2(+int,+int,-int), commutative).

:- dynamic fib/2.

:- set(clause_length,6).

pred(N, M):-
  M is N-1.

%defining plus to be self contained (plus2/3 as plus/3 may already exist in the Prolog system)
plus2(A, B, C):-
  C is A+B.

fib(0, 0):-!.
fib(1, 1):-!.

:- set(i,4).

% we just need two examples to learn the fibonnaci series concept

%example(fib(2,1), 1).
%example(fib(3,2), 1).
%example(fib(4,3), 1).
example(fib(7,13), 10).
example(fib(8,21), 10).
example(fib(9,34), 10).
%example(fib(8,21), 1).

