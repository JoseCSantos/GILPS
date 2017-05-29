%gravitational_constant(6.673e-11).
gravitational_constant(1).

minus(A, B, C):- C is A-B.
mult(A, B, C):- C is A*B.
add(A, B, C):- C is A+B.
divide(A, B, C):- C is A/B.

func1(A, B, C, D, R):-
  mult(A, B, R1),
  add(B, C, R2),
  mult(C, D, R3),
  add(R1, R2, R11),
  add(R11, R3, R).

func2(A, B, C, D, R):-
  minus(A, B, R1),
  minus(R1, C, R2),
  minus(R2, D, R).

member(H, [H|_]).
member(H, [_|T]):-
  member(H, T).


f(X, Y):-
  f1(X, Y1),
  f2(Y1, Y2),
  f3(Y2, Y3),
  f4(Y3, Y4),
  f5(Y4, Y).
 % f6(Y5, Y).

f1(X, Y) :- Y is 4*X-2*X+8.     % f1
f2(X, Y) :- Y is 7*X+2.       % f2
f3(X, Y) :- Y is 2*X-1.   % f3
f4(X, Y) :- Y is 5*X*X.   % f4
f5(X, Y) :- Y is X-10.   % f5
%f6(X, Y) :- Y is 3*X+1.   % f6


genExamples:-
  member(X1, [0,1,2,3,4,5,6,7,8,9]),
  f(X1, Y1),
  format("example(f(~w,~w), 1).~n", [X1, Y1]),
  fail.
genExamples.

:-genExamples.
