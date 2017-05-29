%%%%%%%%%%%%%%%%%%%%%%%
% Declarations


%[rule1] [Pos cover = 2, Neg cover = 0]
%couple(A, B) :- w_occupation(A, doctor), w_occupation(B, doctor).
%[rule2] [Pos cover = 2, Neg cover = 0]
%couple(A, B) :- w_pos_in_brothers(A, youngest), w_pos_in_brothers(B,youngest). 

:- modeh(1, couple(+person, +person)).
:- modeb(*, w_occupation(+person, #job)).
:- modeb(*, w_pos_in_brothers(+person, #pos_brothers)).
:- modeb(*, w_personality(+person, #personality)).
%:- modeb(*, property(+person, -int)).


person(male1).
property(10).
occupation(doctor).
pos_in_brothers(youngest).
personality(very_good).

person(male2).
property(100).
occupation(doctor).
pos_in_brothers(eldest).
personality(good).

person(male3).
property(0).
occupation(doctor).
pos_in_brothers(youngest).
personality(very_bad).

person(male4).
property(0).
occupation(doctor).
pos_in_brothers(eldest).
personality(very_good).

person(female1).
property(5).
occupation(doctor).
pos_in_brothers(youngest).
personality(very_good).

person(female2).
property(1).
occupation(doctor).
pos_in_brothers(middle).
personality(very_good).

person(female3).
property(10).
occupation(doctor).
pos_in_brothers(youngest).
personality(very_bad).

person(female4).
property(0).
occupation(doctor).
pos_in_brothers(middle).
personality(very_good).

w_property(male1,10).
w_property(male2,100).
w_property(male3,0).
w_property(male4,0).
w_property(female1,5).
w_property(female2,1).
w_property(female3,10).
w_property(female4,0).

w_occupation(male1,doctor).
w_occupation(male2,business).
w_occupation(male3,doctor).
w_occupation(male4,nothing).
w_occupation(female1,doctor).
w_occupation(female2,student).
w_occupation(female3,doctor).
w_occupation(female4,nothing).

w_pos_in_brothers(male1,youngest).
w_pos_in_brothers(male2,eldest).
w_pos_in_brothers(male3,youngest).
w_pos_in_brothers(male4,eldest).
w_pos_in_brothers(female1,youngest).
w_pos_in_brothers(female2,middle).
w_pos_in_brothers(female3,youngest).
w_pos_in_brothers(female4,middle).

w_personality(male1,very_good).
w_personality(male2,good).
w_personality(male3,very_bad).
w_personality(male4,very_good).
w_personality(female1,very_good).
w_personality(female2,very_good).
w_personality(female3,very_bad).
w_personality(female4,very_good).

%Positive Examples
example(couple(male1,female1), 10).
example(couple(male2,female2), 10).
example(couple(male3,female3), 10).
example(couple(male4,female4), 10).

% Negative Examples
example(couple(male1,female4), -10).
example(couple(male2,female3), -10).
example(couple(male3,female2), -10).
example(couple(male4,female1), -10).

