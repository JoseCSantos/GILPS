%background knowledge

a(m1, a1).
a(m1, a2).
a(m1, a3).
b(m1, b1).
b(m1, b2).
b(m1, b3).
c(b2, a1).
c(b3, a2).



%try: hyp(g(m1), H)

:- modeh(1, g(+m)).
:- modeb(2, a(+m,#p)).
:- modeb(2, b(+m,#p)).
:- modeb(2, a(+m,-p)).
:- modeb(2, b(+m,-p)).
:- modeb(2, c(+p,+p)).

