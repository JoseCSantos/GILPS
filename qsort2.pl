/*
 Qsort identical to the one used by Golem
*/
:- modeh(1, qsort(+list,-list)).
:- modeb(1, app(+list,+list,-list)).
:- modeb(1, part(+elem,+list,-list,-list)).


nat(0).
nat(1).
nat(2).
part(0,[],[],[]).
part(1,[],[],[]).
part(2,[],[],[]).
part(0,[1],[],[1]).
part(1,[0],[0],[]).
part(0,[2],[],[2]).
part(2,[0],[0],[]).
part(1,[2],[],[2]).
part(2,[1],[1],[]).
part(0,[2,1],[],[2,1]).
part(0,[1,2],[],[1,2]).
part(1,[0,2],[0],[2]).
part(1,[2,0],[0],[2]).
part(2,[0,1],[0,1],[]).
part(2,[1,0],[1,0],[]).
% 15 cases of part f1=12
app([],[],[]).
app([],[0],[0]).
app([],[1],[1]).
app([],[2],[2]).
app([0],[],[0]).
app([1],[],[1]).
app([2],[],[2]).
app([],[0,1],[0,1]).
app([],[1,0],[1,0]).
app([],[0,2],[0,2]).
app([],[2,0],[2,0]).
app([],[1,2],[1,2]).
app([],[2,1],[2,1]).
app([0],[1],[0,1]).
app([1],[0],[1,0]).
app([0],[2],[0,2]).
app([2],[0],[2,0]).
app([1],[2],[1,2]).
app([2],[1],[2,1]).
app([0,1],[],[0,1]).
app([1,0],[],[1,0]).
app([0,2],[],[0,2]).
app([2,0],[],[2,0]).
app([1,2],[],[1,2]).
app([2,1],[],[2,1]).
app([],[0,1,2],[0,1,2]).
app([],[0,2,1],[0,2,1]).
app([],[1,0,2],[1,0,2]).
app([],[1,2,0],[1,2,0]).
app([],[2,0,1],[2,0,1]).
app([],[2,1,0],[2,1,0]).
app([0],[1,2],[0,1,2]).
app([0],[2,1],[0,2,1]).
app([1],[0,2],[1,0,2]).
app([1],[2,0],[1,2,0]).
app([2],[0,1],[2,0,1]).
app([2],[1,0],[2,1,0]).
app([0,1],[2],[0,1,2]).
app([0,2],[1],[0,2,1]).
app([1,0],[2],[1,0,2]).
app([1,2],[0],[1,2,0]).
app([2,0],[1],[2,0,1]).
app([2,1],[0],[2,1,0]).
app([0,1,2],[],[0,1,2]).
app([0,2,1],[],[0,2,1]).
app([1,0,2],[],[1,0,2]).
app([1,2,0],[],[1,2,0]).
app([2,0,1],[],[2,0,1]).
app([2,1,0],[],[2,1,0]).

qsort([],[]).
qsort([0],[0]).
qsort([1],[1]).
qsort([2],[2]).
qsort([0,1],[0,1]).
qsort([1,0],[0,1]).
qsort([0,2],[0,2]).
qsort([2,0],[0,2]).
qsort([1,2],[1,2]).
qsort([2,1],[1,2]).
qsort([0,1,2],[0,1,2]).
qsort([0,2,1],[0,1,2]).
qsort([1,0,2],[0,1,2]).
qsort([1,2,0],[0,1,2]).
qsort([2,0,1],[0,1,2]).
qsort([2,1,0],[0,1,2]).
