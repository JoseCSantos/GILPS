:- modeh(f(+int, -int)).

:- modeb(1, f1(+int, -int)).
:- modeb(1, f2(+int, -int)).
:- modeb(1, f3(+int, -int)).
:- modeb(1, f4(+int, -int)).
:- modeb(1, f5(+int, -int)).
:- modeb(1, f6(+int, -int)).
%:- modeb(1, f7(+int, -int)).

%:- modeb(1, mult(+int, +int, -int)).
%:- modeb(1, add(+int, +int, -int)).


%f(X, Y):-
%  f1(X, Y1),
%  f2(Y1, Y2),
%  f3(Y2, Y3),
%  f4(Y3, Y4),
%  f5(Y4, Y),
%  f6(Y5, Y).

f1(X, Y) :- Y is 4*X-2*X+8.     % f1
f2(X, Y) :- Y is 7*X+2.       % f2
f3(X, Y) :- Y is 2*X-1.   % f3
f4(X, Y) :- Y is 5*X*X.   % f4
f5(X, Y) :- Y is X-10.   % f5
f6(X, Y) :- Y is 3*X+1.   % f6
f7(X, Y) :- Y is X*X-3.

:- set(clause_length, 7).

%:- set(example_inflation, 10).
:- set(i, 2).
:- set(evalfn, coverage).

example(f(6,1201306), 1).
