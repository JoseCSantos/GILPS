:- set(nodes,16000).

:- modeh(1, example(+int, +int, +int, +int)).
:- modeb(1, add(+int, +int, -int)).
:- modeb(1, odd(+int)).

add(X, Y, Z) :- Z is X + Y.
odd(X) :- 1 is X mod 2.


example(example(8,6,3,2),1).
example(example(2,2,2,1),1).
example(example(2,4,2,1),1).
example(example(2,4,6,1),1).
example(example(2,2,1,2),1).
example(example(2,1,2,2),1).
example(example(1,2,2,2),1).
example(example(1,1,2,1),1).
example(example(1,2,3,5),1).
example(example(2,3,4,6),1).
example(example(1,2,3,1),1).


example(example(3,2,2,1),-1).
example(example(2,5,2,1),-1).
example(example(2,4,7,1),-1).
example(example(2,2,1,3),-1).
example(example(1,1,2,2),-1).
example(example(1,1,2,2),-1).
example(example(1,1,1,1),-1).
example(example(1,2,3,4),-1).
example(example(5,3,4,6),-1).
example(example(8,9,3,2),-1).
example(example(1,2,6,1),-1).
