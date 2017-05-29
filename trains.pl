%%%%%%%%%%%%%%%%%%%%%%%
% Michalski's train problem. This involves 5 eastbound trains and
%	5 westbound trains. Learns simple rule which distinguishes
%	between eastbound and westbound trains.

%%%%%%%%%%%%%%%%%%%%%%%
% Declarations

:- modeh(1,eastbound(+train)).
:- modeb(*,has_car(+train,-car)).
%:- modeb(1,not open(+car)).
%:- modeb(1,not long(+car)).
:- modeb(1,closed(+car)).%added
:- modeb(1,short(+car)).%added

:- modeb(1,long(+car)).
:- modeb(1,open(+car)).
%:- modeb(1,double(+car)).
%:- modeb(1,jagged(+car)).
% :- modeb(1,shape(+car,#shape))?
% :- modeb(1,load(+car,#shape,#int))?
% :- modeb(1,wheels(+car,#int))?
:- modeb(1,shape(+car,-shape)).
:- modeb(1,load(+car,-shape,-int)).
:- modeb(1,wheels(+car,#int)). % was wheels(+car,-int)).
:- modeb(1,infront(+train,-car)).%added
:- modeb(1,infront(+car,-car)).

%%%%%%%%%%%%%%%%%%%%%%%
% Positive examples

example(eastbound(east1),10).
example(eastbound(east2),10).
example(eastbound(east3),10).
example(eastbound(east4),10).
example(eastbound(east5),10).

%%%%%%%%%%%%%%%%%%%%%%%
% Negative examples

example(eastbound(west6),-10).
example(eastbound(west7),-10).
example(eastbound(west8),-10).
example(eastbound(west9),-10).
example(eastbound(west10),-10).

%%%%%%%%%%%%%%%%%%%%%%%
% Background knowledge

car(car_11).  car(car_12).  car(car_13).  car(car_14).
car(car_21).  car(car_22).  car(car_23).
car(car_31).  car(car_32).  car(car_33).
car(car_41).  car(car_42).  car(car_43).  car(car_44).
car(car_51).  car(car_52).  car(car_53).
car(car_61).  car(car_62).
car(car_71).  car(car_72).  car(car_73).
car(car_81).  car(car_82).
car(car_91).  car(car_92).  car(car_93).  car(car_94).
car(car_101).  car(car_102).

shape(elipse).  shape(hexagon).  shape(rectangle).  shape(u_shaped).

train(east1).  train(east2).  train(east3).  train(east4).  train(east5).
train(west6).  train(west7).  train(west8).  train(west9).  train(west10).

%%%%%%%%%%%%%%%%%%%%%%%
% Eastbound train 1

short(car_12).
closed(car_12).
long(car_11).
long(car_13).
short(car_14).
open(car_11).
infront(east1,car_11).
infront(car_11,car_12).
infront(car_12,car_13).
infront(car_13,car_14).
open(car_13).
open(car_14).
shape(car_11,rectangle).
shape(car_12,rectangle).
shape(car_13,rectangle).
shape(car_14,rectangle).
load(car_11,rectangle,3).
load(car_12,triangle,1).
load(car_13,hexagon,1).
load(car_14,circle,1).
wheels(car_11,2).
wheels(car_12,2).
wheels(car_13,3).
wheels(car_14,2).
has_car(east1,car_11).
has_car(east1,car_12).
has_car(east1,car_13).
has_car(east1,car_14).

%%%%%%%%%%%%%%%%%%%%%%%
% Eastbound train 2

has_car(east2,car_21).
has_car(east2,car_22).
has_car(east2,car_23).
infront(east2,car_21).
infront(car_21,car_22).
infront(car_22,car_23).
short(car_21).
short(car_22).
short(car_23).
shape(car_21,u_shaped).
shape(car_22,u_shaped).
shape(car_23,rectangle).
open(car_21).
open(car_22).
closed(car_23).
load(car_21,triangle,1).
load(car_22,rectangle,1).
load(car_23,circle,2).
wheels(car_21,2).
wheels(car_22,2).
wheels(car_23,2).

%%%%%%%%%%%%%%%%%%%%%%%
% Eastbound train 3

has_car(east3,car_31).
has_car(east3,car_32).
has_car(east3,car_33).
infront(east3,car_31).
infront(car_31,car_32).
infront(car_32,car_33).
short(car_31).
short(car_32).
long(car_33).
shape(car_31,rectangle).
shape(car_32,hexagon).
shape(car_33,rectangle).
open(car_31).
closed(car_32).
closed(car_33).
load(car_31,circle,1).
load(car_32,triangle,1).
load(car_33,triangle,1).
wheels(car_31,2).
wheels(car_32,2).
wheels(car_33,3).

%%%%%%%%%%%%%%%%%%%%%%%
% Eastbound train 4

has_car(east4,car_41).
has_car(east4,car_42).
has_car(east4,car_43).
has_car(east4,car_44).
infront(east4,car_41).
infront(car_41,car_42).
infront(car_42,car_43).
infront(car_43,car_44).
short(car_41).
short(car_42).
short(car_43).
short(car_44).
shape(car_41,u_shaped).
shape(car_42,rectangle).
shape(car_43,elipse).
shape(car_44,rectangle).
double(car_42).
open(car_41).
open(car_42).
closed(car_43).
open(car_44).
load(car_41,triangle,1).
load(car_42,triangle,1).
load(car_43,rectangle,1).
load(car_44,rectangle,1).
wheels(car_41,2).
wheels(car_42,2).
wheels(car_43,2).
wheels(car_44,2).

%%%%%%%%%%%%%%%%%%%%%%%
% Eastbound train 5

has_car(east5,car_51).
has_car(east5,car_52).
has_car(east5,car_53).
infront(east5,car_51).
infront(car_51,car_52).
infront(car_52,car_53).
short(car_51).
long(car_52).
short(car_53).
shape(car_51,rectangle).
shape(car_52,rectangle).
shape(car_53,rectangle).
double(car_51).
open(car_51).
closed(car_52).
closed(car_53).
load(car_51,triangle,1).
load(car_52,rectangle,1).
load(car_53,circle,1).
wheels(car_51,2).
wheels(car_52,3).
wheels(car_53,2).

%%%%%%%%%%%%%%%%%%%%%%%
% Westbound train 6

has_car(west6,car_61).
has_car(west6,car_62).
infront(west6,car_61).
infront(car_61,car_62).
long(car_61).
short(car_62).
shape(car_61,rectangle).
shape(car_62,rectangle).
closed(car_61).
open(car_62).
load(car_61,circle,3).
load(car_62,triangle,1).
wheels(car_61,2).
wheels(car_62,2).

%%%%%%%%%%%%%%%%%%%%%%%
% Westbound train 7

has_car(west7,car_71).
has_car(west7,car_72).
has_car(west7,car_73).
infront(west7,car_71).
infront(car_71,car_72).
infront(car_72,car_73).
short(car_71).
short(car_72).
long(car_73).
shape(car_71,rectangle).
shape(car_72,u_shaped).
shape(car_73,rectangle).
double(car_71).
open(car_71).
open(car_72).
jagged(car_73).
load(car_71,circle,1).
load(car_72,triangle,1).
load(car_73,nil,0).
wheels(car_71,2).
wheels(car_72,2).
wheels(car_73,2).

%%%%%%%%%%%%%%%%%%%%%%%
% Westbound train 8

has_car(west8,car_81).
has_car(west8,car_82).
infront(west8,car_81).
infront(car_81,car_82).
long(car_81).
short(car_82).
shape(car_81,rectangle).
shape(car_82,u_shaped).
closed(car_81).
open(car_82).
load(car_81,rectangle,1).
load(car_82,circle,1).
wheels(car_81,3).
wheels(car_82,2).

%%%%%%%%%%%%%%%%%%%%%%%
% Westbound train 9

has_car(west9,car_91).
has_car(west9,car_92).
has_car(west9,car_93).
has_car(west9,car_94).
infront(west9,car_91).
infront(car_91,car_92).
infront(car_92,car_93).
infront(car_93,car_94).
short(car_91).
long(car_92).
short(car_93).
short(car_94).
shape(car_91,u_shaped).
shape(car_92,rectangle).
shape(car_93,rectangle).
shape(car_94,u_shaped).
open(car_91).
jagged(car_92).
open(car_93).
open(car_94).
load(car_91,circle,1).
load(car_92,rectangle,1).
load(car_93,rectangle,1).
load(car_93,circle,1).
wheels(car_91,2).
wheels(car_92,2).
wheels(car_93,2).
wheels(car_94,2).

%%%%%%%%%%%%%%%%%%%%%%%
% Westbound train 10

has_car(west10,car_101).
has_car(west10,car_102).
infront(west10,car_101).
infront(car_101,car_102).
short(car_101).
long(car_102).
shape(car_101,u_shaped).
shape(car_102,rectangle).
open(car_101).
open(car_102).
load(car_101,rectangle,1).
load(car_102,rectangle,2).
wheels(car_101,2).
wheels(car_102,2).
