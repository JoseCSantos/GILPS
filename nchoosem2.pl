:- modeh(1,choose(+int,+int,+int)).
:- modeb(1,dec(+int,-int)).
:- modeb(1,choose(+int,+int,+int)).
:- modeb(1,mult(+int,+int,-int)).
:- modeb(1,div(+int,+int,-int)).

%:- set(examples2BK, true).


dec(1,0).
dec(2,1).
dec(3,2).
dec(4,3).
dec(5,4).
dec(6,5).
dec(7,6).
dec(8,7).
dec(9,8).
dec(10,9).
dec(11,10).

mult(0,0,0).
mult(0,1,0).
mult(0,2,0).
mult(0,3,0).
mult(0,4,0).
mult(0,5,0).
mult(0,6,0).
mult(0,7,0).
mult(0,8,0).
mult(0,9,0).
mult(0,10,0).
mult(1,0,0).
mult(1,1,1).
mult(1,2,2).
mult(1,3,3).
mult(1,4,4).
mult(1,5,5).
mult(1,6,6).
mult(1,7,7).
mult(1,8,8).
mult(1,9,9).
mult(1,10,10).
mult(2,0,0).
mult(2,1,2).
mult(2,2,4).
mult(2,3,6).
mult(2,4,8).
mult(2,5,10).
mult(2,6,12).
mult(2,7,14).
mult(2,8,16).
mult(2,9,18).
mult(2,10,20).
mult(3,0,0).
mult(3,1,3).
mult(3,2,6).
mult(3,3,9).
mult(3,4,12).
mult(3,5,15).
mult(3,6,18).
mult(3,7,21).
mult(3,8,24).
mult(3,9,27).
mult(3,10,30).
mult(4,0,0).
mult(4,1,4).
mult(4,2,8).
mult(4,3,12).
mult(4,4,16).
mult(4,5,20).
mult(4,6,24).
mult(4,7,28).
mult(4,8,32).
mult(4,9,36).
mult(4,10,40).
mult(5,0,0).
mult(5,1,5).
mult(5,2,10).
mult(5,3,15).
mult(5,4,20).
mult(5,5,25).
mult(5,6,30).
mult(5,7,35).
mult(5,8,40).
mult(5,9,45).
mult(5,10,50).
mult(6,0,0).
mult(6,1,6).
mult(6,2,12).
mult(6,3,18).
mult(6,4,24).
mult(6,5,30).
mult(6,6,36).
mult(6,7,42).
mult(6,8,48).
mult(6,9,54).
mult(6,10,60).
mult(7,0,0).
mult(7,1,7).
mult(7,2,14).
mult(7,3,21).
mult(7,4,28).
mult(7,5,35).
mult(7,6,42).
mult(7,7,49).
mult(7,8,56).
mult(7,9,63).
mult(7,10,70).
mult(8,0,0).
mult(8,1,8).
mult(8,2,16).
mult(8,3,24).
mult(8,4,32).
mult(8,5,40).
mult(8,6,48).
mult(8,7,56).
mult(8,8,64).
mult(8,9,72).
mult(8,10,80).
mult(9,0,0).
mult(9,1,9).
mult(9,2,18).
mult(9,3,27).
mult(9,4,36).
mult(9,5,45).
mult(9,6,54).
mult(9,7,63).
mult(9,8,72).
mult(9,9,81).
mult(9,10,90).
mult(10,0,0).
mult(10,1,10).
mult(10,2,20).
mult(10,3,30).
mult(10,4,40).
mult(10,5,50).
mult(10,6,60).
mult(10,7,70).
mult(10,8,80).
mult(10,9,90).
mult(10,10,100).
div(1,1,1).
div(2,1,2).
div(3,1,3).
div(4,1,4).
div(5,1,5).
div(6,1,6).
div(7,1,7).
div(8,1,8).
div(9,1,9).
div(10,1,10).
div(0,2,0).
div(2,2,1).
div(4,2,2).
div(6,2,3).
div(8,2,4).
div(10,2,5).
div(12,2,6).
div(14,2,7).
div(16,2,8).
div(18,2,9).
div(20,2,10).
div(24,2,12).
div(0,3,0).
div(3,3,1).
div(6,3,2).
div(9,3,3).
div(12,3,4).
div(15,3,5).
div(18,3,6).
div(21,3,7).
div(24,3,8).
div(27,3,9).
div(30,3,10).
div(0,4,0).
div(4,4,1).
div(8,4,2).
div(12,4,3).
div(16,4,4).
div(20,4,5).
div(24,4,6).
div(28,4,7).
div(32,4,8).
div(36,4,9).
div(40,4,10).
div(0,5,0).
div(5,5,1).
div(10,5,2).
div(15,5,3).
div(20,5,4).
div(25,5,5).
div(30,5,6).
div(35,5,7).
div(40,5,8).
div(45,5,9).
div(50,5,10).
div(0,6,0).
div(6,6,1).
div(12,6,2).
div(18,6,3).
div(24,6,4).
div(30,6,5).
div(36,6,6).
div(42,6,7).
div(48,6,8).
div(54,6,9).
div(60,6,10).
div(0,7,0).
div(7,7,1).
div(14,7,2).
div(21,7,3).
div(28,7,4).
div(35,7,5).
div(42,7,6).
div(49,7,7).
div(56,7,8).
div(63,7,9).
div(70,7,10).
div(0,8,0).
div(8,8,1).
div(16,8,2).
div(24,8,3).
div(32,8,4).
div(40,8,5).
div(48,8,6).
div(56,8,7).
div(64,8,8).
div(72,8,9).
div(80,8,10).
div(0,9,0).
div(9,9,1).
div(18,9,2).
div(27,9,3).
div(36,9,4).
div(45,9,5).
div(54,9,6).
div(63,9,7).
div(72,9,8).
div(81,9,9).
div(90,9,10).
div(0,10,0).
div(10,10,1).
div(20,10,2).
div(30,10,3).
div(40,10,4).
div(50,10,5).
div(60,10,6).
div(70,10,7).
div(80,10,8).
div(90,10,9).
div(100,10,10).

example(choose(0,0,1), 1).
example(choose(1,0,1), 1).
example(choose(1,1,1), 1).
example(choose(2,0,1), 1).
example(choose(2,1,2), 1).
example(choose(2,2,1), 1).
example(choose(3,0,1), 1).
example(choose(3,1,3), 1).
example(choose(3,2,3), 1).
example(choose(3,3,1), 1).
example(choose(4,0,1), 1).
example(choose(4,1,4), 1).
example(choose(4,2,6), 1).
example(choose(4,3,4), 1).
example(choose(4,4,1), 1).
example(choose(5,0,1), 1).
example(choose(5,1,5), 1).
example(choose(5,2,10), 1).
example(choose(5,3,10), 1).
example(choose(5,4,5), 1).
example(choose(5,5,1), 1).
example(choose(6,0,1), 1).
example(choose(6,1,6), 1).
