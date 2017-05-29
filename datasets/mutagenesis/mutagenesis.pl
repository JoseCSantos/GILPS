%:-set(maximum_singletons_in_clause, 1).
:-set(clause_length, 4).
:-set(cross_validation_folds, 10).
%:-set(evalfn, laplace).

:- modeh(active(+drug)).

% active(A):-ind1>0 
%:- modeb(ind1(+drug,-float)).
%:- modeb(inda(+drug,-float)).

:- modeb(*,lumo(+drug,-energy)).
:- modeb(*,logp(+drug,-hydrophob)).

:- modeb(*,atm(+drug,-atomid,#element,#int,-charge)).
:- modeb(*,bond(+drug,-atomid,-atomid,#int)).
:- modeb(*,bond(+drug,+atomid,-atomid,#int)).

:- modeb(*,gteq(+charge,#float)).
:- modeb(*,gteq(+energy,#float)).
:- modeb(*,gteq(+hydrophob,#float)).
:- modeb(*,gteq(+float,#float)).
:- modeb(*,lteq(+charge,#float)).
:- modeb(*,lteq(+energy,#float)).
:- modeb(*,lteq(+hydrophob,#float)).
:- modeb(*,lteq(+float,#float)).

:- modeb(1,(+charge)=(#charge)).
:- modeb(1,(+energy)=(#energy)).
:- modeb(1,(+hydrophob)=(#hydrophob)).

:- modeb(1,benzene(+drug,-ring)).
:- modeb(1,carbon_5_aromatic_ring(+drug,-ring)).
:- modeb(1,carbon_6_ring(+drug,-ring)).
:- modeb(1,hetero_aromatic_6_ring(+drug,-ring)).
:- modeb(*,hetero_aromatic_5_ring(+drug,-ring)).
:- modeb(*,ring_size_6(+drug,-ring)).
:- modeb(*,ring_size_5(+drug,-ring)).
:- modeb(*,nitro(+drug,-ring)).
:- modeb(*,methyl(+drug,-ring)).
:- modeb(*,anthracene(+drug,-ringlist)).
:- modeb(*,phenanthrene(+drug,-ringlist)).
:- modeb(*,ball3(+drug,-ringlist)).

:- [atom_bond,logp,lumo,ring_struct,examples].
%:- [atom_bond,examples].

% trivial background knowledge for greater/smaller or equal than

gteq(X,Y):- \+(var(X)), \+(var(Y)),float(X), float(Y), X >= Y. % not does not exist in sicstus!!
gteq(X,X):- \+(var(X)), float(X).

lteq(X,Y):- \+(var(X)), \+(var(Y)),float(X), float(Y), X =< Y.
lteq(X,X):- \+(var(X)), float(X).
