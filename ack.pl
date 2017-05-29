/*
  Ackermann function
*/
:-modeh(1, ack(+int,+int,-int)).
:-modeb(1, pred(+int,-int)).
:-modeb(1, ack(+int,+int,-int)).

:- dynamic ack/3.

:- set(clause_length, 5).

pred(N, M):-
  M is N-1.
plus(A, B, C):-
  C is A+B.

ack(0, N ,R):-
  !,
  R is N+1.
ack(M, 0 ,R):-
  !,
  M1 is M-1,
  ack(M1, 1, R).

ack(M, N, R):-
  N1 is N-1,
  ack(M, N1, R1),
  M1 is M-1,
  ack(M1, R1, R).

:- set(i,4).

%example(fib(2,1), 1).
%example(fib(3,2), 1).
%example(fib(4,3), 1).
example(fib(7,13), 10).
example(fib(8,21), 10).
example(fib(9,34), 10).
%example(fib(8,21), 1).

