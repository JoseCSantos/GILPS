% Mode declarations for Pascal triangle n-choose-m: C(N,M) = C(N-1,M-1) + C(N-1,M)

:- modeh(1, div(+int,+int,-int,-int)).
:- modeb(1, int_div(+int,+int,-int)).
:- modeb(1, mult(+int,+int,-int), commutative).
:- modeb(1, minus(+int,+int,-int)).

:- set(i,3).
%:- set(bottom_early_stop, true).

%target concept:
%  div(A,B,C, D):-
%    int_div(A, B, C), %i=1
%    mult(C, B, E),    %i=2
%    minus(A, E, D).   %i=3

:- set(verbose, 2).
:- set(maximum_singletons_in_clause, 0).
:- set(clause_length, 4).
:- set(nodes, 5000).

%:- set(verbose,4).
:- set(depth, 10).
:- set(resolutions, 1000).


minus(A,B,C):-
  A>=B,
  C is A-B.
mult(A,B,C):-
  C is A*B.
int_div(A,B,C):-
  A>=B, B\=0,
  C is A//B.

%example(div(7,3,2,1), 10).
%example(div(14,4,3,2), 10).
example(div(22,5,4,2), 10).
