:- modeh(1,class(+animal,#class)).
:- modeb(1,has_milk(+animal)).
:- modeb(1,has_gills(+animal)).
:- modeb(1,has_covering(+animal,#covering)).
:- modeb(1,has_legs(+animal,#nat)).
:- modeb(1,homeothermic(+animal)).
:- modeb(1,has_eggs(+animal)).
:- modeb(1,habitat(+animal,#habitat)).

:- set(example_inflation, 10).

has_covering(dog,hair).
has_covering(dolphin,none).
has_covering(platypus,hair).
has_covering(bat,hair).
has_covering(trout,scales).
has_covering(herring,scales).
has_covering(shark,none).
has_covering(eel,none).
has_covering(lizard,scales).
has_covering(crocodile,scales).
has_covering(t_rex,scales).
has_covering(snake,scales).
has_covering(turtle,scales).
has_covering(eagle,feathers).
has_covering(ostrich,feathers).
has_covering(penguin,feathers).

has_legs(dog,4).
has_legs(dolphin,0).
has_legs(platypus,2).
has_legs(bat,2).
has_legs(trout,0).
has_legs(herring,0).
has_legs(shark,0).
has_legs(eel,0).
has_legs(lizard,4).
has_legs(crocodile,4).
has_legs(t_rex,4).
has_legs(snake,0).
has_legs(turtle,4).
has_legs(eagle,2).
has_legs(ostrich,2).
has_legs(penguin,2).

has_milk(dog).
has_milk(dolphin).
has_milk(bat).
has_milk(platypus).


homeothermic(dog).
homeothermic(dolphin).
homeothermic(platypus).
homeothermic(bat).
homeothermic(eagle).
homeothermic(ostrich).
homeothermic(penguin).


habitat(dog,land).
habitat(dolphin,water).
habitat(platypus,water).
habitat(bat,air).
habitat(bat,caves).
habitat(trout,water).
habitat(herring,water).
habitat(shark,water).
habitat(eel,water).
habitat(lizard,land).
habitat(crocodile,water).
habitat(crocodile,land).
habitat(t_rex,land).
habitat(snake,land).
habitat(turtle,water).
habitat(eagle,air).
habitat(eagle,land).
habitat(ostrich,land).
habitat(penguin,water).

has_eggs(platypus).
has_eggs(trout).
has_eggs(herring).
has_eggs(shark).
has_eggs(eel).
has_eggs(lizard).
has_eggs(crocodile).
has_eggs(t_rex).
has_eggs(snake).
has_eggs(turtle).
has_eggs(eagle).
has_eggs(ostrich).
has_eggs(penguin).

has_gills(trout).
has_gills(herring).
has_gills(shark).
has_gills(eel).


%example/2, example(target, weight) 
example(class(dog,mammal), 1).
example(class(dolphin,mammal), 1).

example(class(platypus,mammal), 1).
example(class(bat,mammal), 1).

example(class(trout,fish), 1).
example(class(herring,fish), 1).
example(class(shark,fish), 1).
example(class(eel,fish), 1).

example(class(lizard,reptile), 1).
example(class(crocodile,reptile), 1).
example(class(t_rex,reptile), 1).
example(class(snake,reptile), 1).
example(class(turtle,reptile), 1).

example(class(eagle,bird), 1).
example(class(ostrich,bird), 1).
example(class(penguin,bird), 1).

example(class(trout,mammal), -1).
example(class(herring,mammal), -1).
example(class(shark,mammal), -1).
example(class(lizard,mammal), -1).
example(class(crocodile,mammal), -1).
example(class(t_rex,mammal), -1).
example(class(turtle,mammal), -1).
example(class(eagle,mammal), -1).
example(class(ostrich,mammal), -1).
example(class(penguin,mammal), -1).
example(class(dog,fish), -1).
example(class(dolphin,fish), -1).
example(class(platypus,fish), -1).
example(class(bat,fish), -1).
example(class(lizard,fish), -1).
example(class(crocodile,fish), -1).
example(class(t_rex,fish), -1).
example(class(turtle,fish), -1).
example(class(eagle,fish), -1).
example(class(ostrich,fish), -1).
example(class(penguin,fish), -1).
example(class(dog,reptile), -1).
example(class(dolphin,reptile), -1).
example(class(platypus,reptile), -1).
example(class(bat,reptile), -1).
example(class(trout,reptile), -1).
example(class(herring,reptile), -1).
example(class(shark,reptile), -1).
example(class(eagle,reptile), -1).
example(class(ostrich,reptile), -1).
example(class(penguin,reptile), -1).
example(class(dog,bird), -1).
example(class(dolphin,bird), -1).
example(class(platypus,bird), -1).
example(class(bat,bird), -1).
example(class(trout,bird), -1).
example(class(herring,bird), -1).
example(class(shark,bird), -1).
example(class(lizard,bird), -1).
example(class(crocodile,bird), -1).
example(class(t_rex,bird), -1).
example(class(turtle,bird), -1).
