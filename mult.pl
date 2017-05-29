% Problem to highlight the advantages of supporting commutative definitions

:-modeh(1, mult(+int,+int,-int)).
:-modeb(1, dec(+int,-int)).
:-modeb(1, plus(+int,+int,-int), commutative).
:-modeb(1, mult(+int,+int,-int), commutative).

:- dynamic(mult/3).

:- set(i,3).

dec(A, B):-
  A>0,
  B is A-1.
plus(A,B,C):-
  C is A+B.

mult(0, _, 0):-!.
mult(_, 0, 0):-!.

example(mult(3,7,21), 1).
example(mult(4,7,28), 1).

%example(mult(0,0,0),1).
%example(mult(0,1,0),1).
%example(mult(0,2,0),1).
%example(mult(0,3,0),1).
%example(mult(0,4,0),1).
%example(mult(0,5,0),1).
%example(mult(0,6,0),1).
%example(mult(0,7,0),1).
%example(mult(0,8,0),1).
%example(mult(0,9,0),1).
%example(mult(0,10,0),1).
/*
example(mult(1,1,1),1).
example(mult(1,2,2),1).
example(mult(1,3,3),1).
example(mult(1,4,4),1).
example(mult(1,5,5),1).
example(mult(1,6,6),1).
example(mult(1,7,7),1).
example(mult(1,8,8),1).
example(mult(1,9,9),1).
example(mult(1,10,10),1).
example(mult(2,2,4),1).
example(mult(2,3,6),1).
example(mult(2,4,8),1).
example(mult(2,5,10),1).
example(mult(2,6,12),1).
example(mult(2,7,14),1).
example(mult(2,8,16),1).
example(mult(2,9,18),1).
example(mult(2,10,20),1).
example(mult(3,3,9),1).
example(mult(3,4,12),1).
example(mult(3,5,15),1).
example(mult(3,6,18),1).

%example(mult(0,0,0),1).
%example(mult(1,0,0),1).
%example(mult(2,0,0),1).
%example(mult(3,0,0),1).
%example(mult(4,0,0),1).
%example(mult(5,0,0),1).
%example(mult(6,0,0),1).
%example(mult(7,0,0),1).
%example(mult(8,0,0),1).
%example(mult(9,0,0),1).
%example(mult(10,0,0),1).
*/
example(mult(1,1,1),1).
example(mult(2,1,2),1).
example(mult(3,1,3),1).
example(mult(4,1,4),1).
example(mult(5,1,5),1).
example(mult(6,1,6),1).
example(mult(7,1,7),1).
example(mult(8,1,8),1).
example(mult(9,1,9),1).
example(mult(10,1,10),1).
example(mult(2,2,4),1).
example(mult(3,2,6),1).
example(mult(4,2,8),1).
example(mult(5,2,10),1).
example(mult(6,2,12),1).
example(mult(7,2,14),1).
example(mult(8,2,16),1).
example(mult(9,2,18),1).
example(mult(10,2,20),1).
example(mult(3,3,9),1).
example(mult(4,3,12),1).
example(mult(5,3,15),1).
example(mult(6,3,18),1).


:- set(nodes, 10000).

/*
target concept:

 mult(A,B,C):-
  dec(A,D),   %i=1
  mult(D,B,E),%i=2
  plus(B,E,C).%i=3
*/

/*
Aleph:

i=2
mult(A,B,C) :-
   plus(B,B,D), plus(B,A,E), plus(A,A,F), plus(D,B,C).
i=3
mult(A,B,C) :-
   plus(B,B,D), plus(B,A,E), plus(A,B,E), plus(A,A,F),
   plus(F,F,G), plus(F,E,H), plus(F,D,I), plus(F,B,J),
   plus(F,A,K), plus(E,F,H), plus(E,E,I), plus(E,D,L),
   plus(E,B,M), plus(E,A,J), plus(D,F,I), plus(D,E,L),
   plus(D,D,N), plus(D,B,C), plus(D,A,M), plus(B,F,J),
   plus(A,F,K), plus(B,E,M), plus(A,E,J), plus(B,D,C),
   plus(A,D,M).
[literals] [26]

i=3, commutative(plus/3)
mult(A,B,C) :-
   plus(B,B,D), plus(A,B,E), plus(A,A,F), plus(F,F,G),
   plus(F,E,H), plus(F,D,I), plus(F,B,J), plus(F,A,K),
   plus(E,E,I), plus(E,D,L), plus(E,B,M), plus(E,A,J),
   plus(D,D,N), plus(D,B,C), plus(D,A,M).
[literals] [16]

Gilps:

i=1
mult(A,B,C) :-
   plus(B,B,D), plus(B,A,E), plus(A,B,E), plus(A,A,F).

i=2
mult(A,B,C) :-
   plus(B,B,D), plus(B,A,E), plus(A,B,E), plus(A,A,F),
   plus(D,D,G), plus(D,E,H), plus(D,F,I), plus(D,B,C),
   plus(D,A,J), plus(E,D,H), plus(E,E,I), plus(E,F,K),
   plus(E,B,J), plus(E,A,L), plus(F,D,I), plus(F,E,K),
   plus(F,F,M), plus(F,B,L), plus(F,A,N), plus(B,D,C),
   plus(B,E,J), plus(B,F,L), plus(A,D,J), plus(A,E,L),
   plus(A,F,N).

[Num literals=26]

*/