%background knowledge
atom(m1, 'o').
atom(m1, 'c').

atom(m2, 'o').
atom(m2, 'c').

atom(m3, 'o').

example(good(m1), 1).
example(good(m2), 1).
example(good(m3), -1).


%concept to learn: good(M):-atom(M, 'c').

:- modeh(1, good(+molecule)).
:- modeb(2, atom(+molecule,#atom)).
:- modeb(2, not(a(+atom,-int))).
% modeb(2, not(a(graph(+molecule,#atom),-int))).
:- modeb(2, atom(+molecule,-atom)).
%:- modeb(1, ((+int)>(+int))).


%%%% problem 2
small(a).

example(test([a,b,c])).


sep([H|T], H, T).

%modeh(1, test(+list)).
%modeb(1, +list=[-elem|-list]).
%modeb(1, sep(+list, -elem, -list)).
%modeb(1, small(+elem)).

%top_theory:theory(A,B,C),A>=100.