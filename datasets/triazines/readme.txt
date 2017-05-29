Dataset for Inductive Logic Programming (ILP)
Learning Quantitative Structure Activity Relationships (QSARs)
The Inhibition of Dihydrofolate Reductase by Triazines

The data is organised for 6 fold cross-validation series of 186 compounds
test[123456]*
train[123456]*

The methodology is described in:
King, Ross .D., Muggleton, Steven., Lewis, Richard. and Sternberg, Michael.J.E.
Drug design by machine learning: the use of inductive logic programming 
to model the structure-activity relationships of trimethoprim analogues 
binding to dihydrofolate reductase. 
Proc. Natl. Acad. Sci. USA. 1992, 89, 11322-11326.

King, Ross .D., Muggleton, Steven., Lewis, Richard., Srinivasan, Ashwin., 
Feng, Cao. and Sternberg, Michael.J.E.
Drug design using inductive logic programming
Proceeding of the 26th Annual Hawaii International Conference on System 
Sciences, 1 pp. 646-655, Los Alamitos, CA: IEEE Computer Society Press.

The details are described in:
King, Ross .D., Hurst, Jonathan. D.,  and Sternberg, Michael.J.E.
A comparison of artificial intelligence methods for modelling QSARs
Applied Artificial Intelligence, 1994 (in press).

Hurst, Jonathan. D., King, Ross .D. and Sternberg, Michael.J.E.
Quantitative Structure-Activity Relationships by neural networks and 
inductive logic programming: 2. The inhibition of dihydrofolate reductase by 
triazines. Journal of Computer Aided Molecular Design, 1994 (in press).

The positive facts are given in the files *.f

QSAR problems are in general regression problems, 
i.e. a real number must be predicted, not a class.
To get around this problem for ILP we used the hack of learning the 
greater activity relationship between pairs of compounds, i.e. 
The predicate 
great(Drug_no1, Drug_no2).
States that drug no. 1 has higher activity than drug no. 2.  
From  rules learnt for this relationship it is  possible 
to rank the drugs by activity 
(we used the David method, David, H.A.
Ranking from unbalanced paired-comparison data, Biometrika, 74, 432-436).


The negative facts are given in the files *.n.
These are the inverse of the facts in the *.f files.


The background facts are given in three files: struc.b, props.b and back.b.

struc.b
This contains the structural information about the compounds.  
These structures can be quite complicated, with ring structures 
substituted onto other ring structures.
Three predicates are used struc3/3, struc4/3 and subst/3.
The representation is best explained by an example.

struc3(d217, 'Cl', absent).
struc4(d217,'(CH2)4',subst14).
subst(subst14,'SO2F','Cl').

This represents the compound -3-Cl, 4-(CH2)C6H3-4'-Cl, 3'-SO2F.
The first clause represents substitution at position 3 on the 
N-phenyl moiety: a Cl is present and there is the absence of a 
further phenyl ring.  The second clause represents substitution 4 on the 
N-phenyl moiety: there is a (CH2)4 bridge to a second phenyl ring (implicit 
in this representation).  The second phenyl ring has a SO2F group 
substituted at position 3 and a Cl group substituted at position 4.  
This is represented using the linker constant subst14 to a third clause.


back.b
Contains the predicates for chemical properties of the chemical groups.  
The different chemical type are typed to 
avoid spurious comparison.

polar(Group, Property).
size(Group, Property).
flex(Group, Property).
h_doner(Group, Property). (I can't spell)
h_acceptor(Group, Property).
pi_doner(Group, Property).
pi_acceptor(Group, Property).
polarisable(Group, Property).
sigma(Group, Property).
branch(Group, Property).


gt.b
Contains the arithmetical information.
gt(Property, Property).


Ross D. King
Biomolecular Modelling Laboratory
Imperial Cancer Research Fund
P.O. Box 123
44 Lincoln's Inn Fields
London WC2A 3PX
U.K.
+44-71-242-0200 x3023
rd_king@icrf.ac.uk
