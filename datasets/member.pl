:- modeh(1, mem(-elem, +list)).
:- modeb(1, +list=[-elem|-list]).
:- modeb(1, mem(-elem, +list)).

%:- set(minpos, 2).
:- set(noise, 0).
:- set(i, 3).

% target definition:
% member(A, B):- B=[A|_]
% member(A, B):- B=[_|C], member(A, C).

:- dynamic mem/2.

mem(A, [A|_]). % base case

example(mem(5,[5]),10).
example(mem(5,[1,5]),10).
example(mem(5,[1,2,3,5]),10).
example(mem(5,[1,2]),-10).

