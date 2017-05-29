% Aunt Agatha Problem 
% Feb 15 2009 Ramin


% Learning the killer 

%:- set(posonly)?
:- set(example_inflation, 10).

% mode declarations

:- modeh(1,killer(+person,+person)).
:- modeb(1,hates(+person,+person)).
			%:- modeb(1,\+richer(+person,+person))?
:- modeb(1,not_richer(+person,+person)).
%- modeb(1,is(+person,+person))?

% types

% case 1 - no11 is Killer, no 12 is victim
person(no11).
person(no12).
person(no13).

% case 2 - no21 is Killer, no 23 is victim
person(no21).
person(no22).
person(no23).

% case 3 - no33 is Killer, no 31 is victim
person(no31).
person(no32).
person(no33).

% case 4 - no43 is Killer, no 42 is victim
person(no41).
person(no42).
person(no43).

% case 5 - no51 is killer, no 51 is victim
person(no51).
person(no52).
person(no53).


% background knowledge

%%%%%%%%% CASE 1 - no11 is Killer, no12 is victim

hates(no11,no12).
not_richer(no11,no12).

%:-hates(no12,no11).
%:-hates(no12,no12).

%:-hates(no11,no13).

hates(no13,Y):-
	not_richer(Y,no11).
hates(no13,Y):-
	hates(no11,Y).

example(killer(no11,no12),1).

%%%%%%%%% CASE 2 - no21 is Killer, no 23 is victim

hates(no21,no23).
not_richer(no21,no23).


%:-hates(no21,no22).
%:-hates(no23,no23).

%:-hates(no21,no22).

hates(no22,Y):-
	not_richer(Y,no21).
hates(no22,Y):-
	hates(no21,Y).

example(killer(no21,no23), 1).

%%%%%%%%%% CASE 3 - no33 is Killer, no 31 is victim

hates(no33,no31).
not_richer(no33,no31).


%:-hates(no31,no33).
%:-hates(no31,31).

%:-hates(no33,no32). 


hates(no32,Y):-
	not_richer(Y,no33).
hates(no32,Y):-
	hates(no33,Y).

%%%%%%%%%%%%% case 4 - no43 is Killer, no 42 is victim		

hates(no43,no42).
not_richer(no43,no42).
not_richer(no42,no41).

%:-hates(no42,no43).
%:-hates(no42,no42).

%:-hates(no43,no41).

hates(no41,Y):-
	not_richer(Y,no43).
hates(no41,Y):-	
	hates(no43,Y).

example(killer(no43,no42), 1).
example(killer(no42,no41), -1).


%%%%%%%%%%%%% case 5 - no51 is Killer, no 51is victim		

hates(no51,no51).
not_richer(no51,no51).

%:-hates(no51,no53).


hates(no53,Y):-
	not_richer(Y,no53).
hates(no53,Y):-	
	hates(no51,Y).

%example(killer(no51,no51), 1).

%%%%%%%%%%%%% Postitive Examples

example(killer(no33,no31), 1).


example(killer(no12,no13), -1).
example(killer(no23,no22), -1).
example(killer(no32,no31), -1).

%person(agatha).
%hates(agatha,agatha).
%not_richer(agatha,agath).
