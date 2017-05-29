
:- modeh(10,odd(+number)).
:- modeb(10,even(+number)).

%%%%% Background Knowledge

even(0).
even(s(X)):- odd(X).


%%%%% Positive Example
example( odd(s(s(s(0)))), 1).

