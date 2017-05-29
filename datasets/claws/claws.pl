:- set(i,3).
%:- set(search, heuristic).
:- set(evalfn, coverage).
:- set(clause_length, 20).
:- set(nodes, 10000).
%:- set(verbosity, 0).
:- set(minpos, 2).
:- set(noise, 0).
:- modeh(1,eriphia(+example)).
:- modeb(*,hasNode(+example, -node)).
:- modeb(*,hasEdge(+example, -edge, -node, -node)).
:- modeb(*,distance(+node, +node, -float),commutative).
:- modeb(*,(+float)<(+float)).

:- [clawdata, examples].
