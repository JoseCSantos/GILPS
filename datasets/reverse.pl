:- modeh(1,rev(+list,-list)).
:- modeb(1,+list=[-elem|-list]).
%:- modeb(1,-list=[+elem]).
:- modeb(1,app(+list,+elem,-list)).
:- modeb(1,rev(+list,-list)).

:- dynamic(rev/2).

:- set(clause_length, 5).

/*
reverse(A, B):-
  A=[H|T], % i=1
  reverse(T, RT), C=[H], %i=2
  append(RT, C, B). %i=3
*/
 
rev([], []).

%example(rev([],[]), 1).
example(rev([1],[1]), 1).
example(rev([2],[2]), 1).
example(rev([3],[3]), 1).
example(rev([4],[4]), 1).
example(rev([1,2],[2,1]), 1).
example(rev([1,3],[3,1]), 1).
example(rev([1,4],[4,1]), 1).
example(rev([2,2],[2,2]), 1).
example(rev([2,3],[3,2]), 1).
example(rev([2,4],[4,2]), 1).
example(rev([3,4],[4,3]), 1).
example(rev([0,1,2],[2,1,0]), 1).
example(rev([1,2,3],[3,2,1]), 1).
example(rev([2,3,4],[4,3,2]), 1).
example(rev([1,2,3,4],[4,3,2,1]), 1).


% common_clause:commonClauseForExamples([rev([1,2,3,4],[4,3,2,1]), rev([2,3,4], [4,3,2])], A, B).

/*
app([], L, L).
app([H|T], L, [H|R]):-
  app(T, L, R).
*/

app([],[],[]).
app([1],[],[1]).
app([2],[],[2]).
app([3],[],[3]).
app([4],[],[4]).
app([],[1],[1]).
app([],[2],[2]).
app([],[3],[3]).
app([],[4],[4]).
app([1],[0],[1,0]).
app([2],[1],[2,1]).
app([2],[1],[2,1]).
app([3],[1],[3,1]).
app([4],[1],[4,1]).
app([2],[2],[2,2]).
app([3],[2],[3,2]).
app([4],[2],[4,2]).
app([4],[3],[4,3]).
app([2,1],[0],[2,1,0]).
app([3,2],[1],[3,2,1]).
app([4,3],[2],[4,3,2]).
app([4,3,2],[1],[4,3,2,1]).
