%%%%%%%%%%%%%%%%%%%%
% Grammar learning problem. -- Abduction

:- modeh(1,noun(+wlist,-wlist)).

%%%%%%%%%%%%%%%%%%%%
% Types

wlist([]).
wlist([W|Ws]) :- word(W), wlist(Ws).

wlist1([]).

word(a).  word(at).  word(ball). word(big).  word(dog). word(every).
word(happy).  word(hits).  word(house).  word(in).  word(man). word(nice).
word(on). word(small).  word(takes).  word(the).  word(to).  word(walks).

:- [wpair]?



%??????????????????????????????
:-set(maximum_literals_in_hypothesis, 4).



%%%%%%%%%%%%%%%%%%%%%%
% Positive Example
example(s([the, dog, bites, the, dog],[]), 1).

%%%%%%%%%%%%%%%%%%%%%%%
% Background knowledge
s(A,B):- np(A,C),vp(C,D),np(D,B).

np(S1,S2) :- det(S1,S3), noun(S3,S2).

det([a|S],S).
det([the|S],S).
det([every|S],S).

vp(S1,S2) :- tverb(S1,S2).

noun([man|S],S).
%noun([dog|S],S).
noun([house|S],S).
noun([ball|S],S).

tverb([hits|S],S).
tverb([takes|S],S).
tverb([walks|S],S).
tverb([bites|S],S).




