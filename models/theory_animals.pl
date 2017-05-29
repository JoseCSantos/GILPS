theory_clause([class(A,fish),has_gills(A)],[class(+animal,#class),has_gills(+animal)]).
theory_clause([class(A,mammal),has_milk(A)],[class(+animal,#class),has_milk(+animal)]).
theory_clause([class(A,reptile),has_legs(A,4),has_eggs(A)],[class(+animal,#class),has_legs(+animal,#nat),has_eggs(+animal)]).
theory_clause([class(A,bird),has_covering(A,feathers)],[class(+animal,#class),has_covering(+animal,#covering)]).
theory_clause([class(A,reptile),habitat(A,land),has_covering(A,scales)],[class(+animal,#class),habitat(+animal,#habitat),has_covering(+animal,#covering)]).
