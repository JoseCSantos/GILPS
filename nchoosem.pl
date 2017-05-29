%Mode declarations for closed form n-choose-m: C(N,M) = N!/(M!(N-M)!)
/*
:-modeh(1,choose(+int,+int,-int)).
:-modeb(1,factorial(+int,-int)).
:-modeb(1,int_div(+int,+int,-int)).
:-modeb(1,mult(+int,+int,-int), commutative).
:-modeb(1,minus(+int,+int,-int)).

:- set(i,4).
:- set(clause_length, 5).
*/
%:- set(bottom_early_stop, true).
%:- set(bottom_early_stop, false).

%target concept:
%  choose(A,B,C):-
%    factorial(A, D), %i=1
%    factorial(B, E), %i=1
%    minus(A,B,F),    %i=1
%    factorial(F, G), %i=2
%    mult(E,G,H),     %i=3
%    int_div(D,H,C).  %i=4


%Mode declarations for linear time recursive n-choose-m: C(N,M) = C(N-1,M-1).N/M
/*
:- modeh(1,choose(+int,+int,+int)).
:- modeb(1,dec(+int,-int)).
:- modeb(1,choose(+int,+int,+int)).
:- modeb(1,mult(+int,+int,-int), commutative).
:- modeb(1,int_div(+int,+int,-int)).
*/
%:- set(examples2BK, true).

%target concept:
%  choose(A,B,C):-
%    dec(A, D), %i=1
%    dec(B, E), %i=1
%    choose(D, E, F), %i=2
%    mult(F, A, G),   %i=3
%    int_div(G, B, C),  %i=4

% Mode declarations for Pascal triangle n-choose-m: C(N,M) = C(N-1,M-1) + C(N-1,M)

:- modeh(1, choose(+int,+int,-int)).
:- modeb(1, pred(+int,-int)).
:- modeb(1, choose(+int,+int,-int)).
:- modeb(1, plus(+int,+int,-int), commutative).

:- set(i,3).
%:- set(bottom_early_stop, true).

%target concept:
%  choose(A,B,C):-
%    dec(A, D), %i=1
%    dec(B, E), %i=1
%    choose(D, E, F),  %i=2
%    choose(D, B, G),  %i=2
%    plus(F, G, C).    %i=3

:- set(verbose, 2).
:- set(maximum_singletons_in_clause, 0).
:- set(clause_length, 6).
:- set(nodes, 5000).

:- dynamic choose/3.
%:- set(verbose,4).
:- set(depth, 10).
:- set(min_resolutions, 1000).


choose(_, 0, 1):-!.
choose(N, N, 1):-!.
/*
choose(A,B, C):-
  choose(A, A, D),
  choose(B, B, D),
  plus(B, A, E),
  plus(E,E,F),
  dec(F,C).
choose(_, 0, 1):-!.
choose(N, N, 1):-!.

in this commented program why does: depth_bound_call(choose(6,2,15),8) takes so long to succeed??
I know... the double recursion causes lots of backtracking. Count how many!
The other thing is why does bk_call_atom(choose(6,2,15),8,100) taking ages to succeed? isn't the
counting working well?
*/


plus(A,B,C):-
  C is A+B.
minus(A,B,C):-
  A>=B,
  C is A-B.
mult(A,B,C):-
  C is A*B.
int_div(A,B,C):-
  A>=B, B\=0,
  A mod B=:=0,
  C is A//B.
pred(A,B):-
  B is A-1.

factorial(0,1):-!.
factorial(1,1):-!.
factorial(2,2):-!.
factorial(3,6):-!.
factorial(4,24):-!.
factorial(5,120):-!.
factorial(6,720):-!.
factorial(7,5040):-!.
factorial(8,40320):-!.
/*
factorial(N, F):-
  N1 is N-1,
  factorial(N1, F1),
  F is N*F1.
*/

example(choose(6,2,15), 10).
example(choose(6,3,20), 10).
example(choose(7,3,35), 10).

/*
example(choose(0,0,1), 10).
example(choose(1,0,1), 10).
example(choose(1,1,1), 10).
example(choose(2,0,1), 10).
example(choose(2,1,2), 10).
example(choose(2,2,1), 10).
example(choose(3,0,1), 10).
example(choose(3,1,3), 10).
example(choose(3,2,3), 10).
example(choose(3,3,1), 10).
example(choose(4,0,1), 10).
example(choose(4,1,4), 10).
example(choose(4,2,6), 10).
example(choose(4,3,4), 10).
example(choose(4,4,1), 10).
example(choose(5,0,1), 10).
example(choose(5,1,5), 10).
example(choose(5,2,10), 10).
example(choose(5,3,10), 10).
example(choose(5,4,5), 10).
example(choose(5,5,1), 10).
example(choose(6,0,1), 10).
example(choose(6,1,6), 10).
example(choose(6,2,15), 10).
example(choose(6,3,20), 10).
example(choose(6,4,15), 10).
example(choose(6,5,6), 10).
example(choose(6,6,1), 10).
%example(choose(11,7,330), 10).
*/

%C(N,M) = C(N-1,M-1) + C(N-1,M)

choose_res(A,B,C):-
   factorial(A, D), %i=1
   factorial(B, E), %i=1
   minus(A,B,F),    %i=1
   factorial(F, G), %i=2
   mult(E,G,H),     %i=3
   int_div(D,H,C).  %i=4

show_examples:-
  lists:member(N, [0,1,2,3,4,5,6]),
  lists:member(M, [0,1,2,3,4,5,6]),
  N>=M,
  choose_res(N,M, Res),
  format("example(choose(~w,~w,~w), 10).~n", [N, M, Res]),
  fail.
show_examples.
 