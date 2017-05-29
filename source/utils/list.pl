%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-01-28
%
%     This file contains misc. list utility predicates not present in library(lists)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(utils_list,
            [
              afterFirstNElemsOf/3,
              member_identical/2,
              member_identical_chk/2,
              member_identical_pos/3,
              length_up_to/3,
              createList/3,
              numbersList/3,
              firstNElemsOf/3,
              find_minimum/3,
              replaceAt/4,
              splitAtPos/4,
              split/4,
              elemsAtPos/3,
              order_list/2,
              custom_qsort/3,
              relative_position/2,
              random_elem/2,
              random_elem/3,
              random_elem/4,
              randomMember/2,
              randomMember/3,
              randomPairs/3,
              randomPermutation/2,
              remove_after/3,
              remove_positions/3,
              n_randomElems/3,
              tuples_to_lists/2,
              lists_to_tuples/3,
              merge_keys/2,
              merge_sorted_keys/2,
              append_keys/2,            % these are similar to merge_keys but do not sort the values, just append them
              append_sorted_keys/2
            ]
         ).

% YAP modules
:- use_module(library(lists), [member/2, append/3, nth/4, nth/3]).
:- use_module(library(ordsets), [ord_subset/2]).
:- use_module(library(apply_macros), [maplist/3]).
:- use_module(library(random), [random/3]).

% type checker
:- use_module('../type_checker/type_check'). % enabling the type checker has a 1-2% runtime cost
:- type_check_options([check(off), verbose(off)]).
%:- use_module('../type_checker/type_check_disabler').

%:- srandom(7). % set random seed to an arbitrary constant, % this is now in settings

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% member_identical(+Elem, +List)
% member_identical_chk(+Elem, +List)
% member_identical_pos(+Elem, +List, -Pos)
%
% Given:
%   Elem: the element to check for identicality in List (likely a variable)
%   List: a list of of elements (likely a list of variables)
%
% member_identical/2: Succeeds once for each element in List identical to Elem
% member_identica_chk/2: Succeeds at the first occurrences of Elem in List, as efficiently as possible
%
% Returns:
%    Pos: the 1-based position for Elem in List
%
% Notes:
%   This predicate is similar to member/2 with the important difference that we don't bind variables.
%   This is important when either Elem is a variable or List is a list of variables.
%
% E.g.
%   member_identical(D,[1,2,A,D,X]), % succeeds
%   member_identical(D,[1,2,A,D,X], 4)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

member_identical(Elem, List):-
  member_identical_pos(Elem, List, _).

member_identical_pos(E1, [E2|_], N, N):-
  E1==E2. % we use == rather than = because we don't want to bind variables
member_identical_pos(E1, [_|T], CurN, N):-
  CurN1 is CurN+1,
  member_identical_pos(E1, T, CurN1, N).

member_identical_pos(Elem, List, N):-
  member_identical_pos(Elem, List, 1, N).

member_identical_chk(E1, [E2|_]):-
  E1==E2, !.
member_identical_chk(E1, [_|T]):-
  member_identical_chk(E1, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% length_up_to(+List, +MaxLength, -Length)
%
% Given:
%   List: a list
%   MaxLength: maximum length to consider in list (>=0)
%              (MaxLength<0 is equivalent to length/2)
%
% Returns:
%   Length: list List length (up to MaxLength)
%
% E.g.
%   length_up_to([a,b,c,d,e], 3, R), R=3.
%   length_up_to([a,b,c,d,e], 9, R), R=5.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

length_up_to(L, MaxLength, Length):-
  length_up_to(L, MaxLength, 0, Length).

length_up_to([], _, Length, Length):-!.
length_up_to(_, MaxLength, MaxLength, MaxLength):-!.
length_up_to([_|T], MaxLength, CurLength, FLength):-
  CurLength1 is CurLength+1,
  length_up_to(T, MaxLength, CurLength1, FLength).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% createList(+NumElements, +Elem, -List)
%
% Given:
%   NumElements: number of elements in the result list
%   Elem: the element to appear NumElements times
%
% Returns:
%   List: a list with NumElements elements, each with Elem as value
%
% E.g.
%   createList(4, 0, [0,0,0,0])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred createList(integer, T, list(T)).

createList(0, _, []):-!.
createList(N, E, [E|T]):-
  N1 is N-1,
  createList(N1, E, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% list_to_array(+Elements, -TermArray)
%
% Given:
%   Elements: a prolog list
%
% Returns:
%   TermArray: a term where each argument is an element of the array
%
% Notes:
%   Using arg/3 we can access elements in constant time now
%
% E.g.
%   list_to_array([a,b,c,d,e],f(a,b,c,d,e)]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_to_array(Elements, Array):-
  Array=..[f|Elements].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% numbersList(+StartNum, +EndNum, -List)
%
% Given:
%   StartNum: an integer
%   EndNum: an integer >=StartNum
%
% Returns
%   List: a list with the integers from [StartNum ..EndNum]
%
% E.g.
%  numbersList(1, 5, [1,2,3,4,5]).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred numbersList(integer, integer, list(integer)).

numbersList(N, N, [N]):-!.
numbersList(CurN, N, [CurN|R]):-
  CurN1 is CurN+1,
  numbersList(CurN1, N, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% splitAtPos(+List, ?N, -Before, -After)
%
% Given:
%   List: a normal Prolog list
%      N: position to split (1 based) (or free variable to return all splits)
%
% Returns:
%   Before: a list with all elements of List up until N (inclusive)
%   After: a list with all elements of List starting after N until the end of list
%
% E.g.
%  splitAtPos([a,b,c,d,e,f], 2, Before, After)
%    Before=[a,b], After=[c,d,e,f]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred splitAtPos(list(T), integer, integer, list(T), list(T)).

splitAtPos(L, N, N, [], L).
splitAtPos([E|T], CurN, MaxN, [E|R], Remain):-
  (ground(MaxN)-> CurN<MaxN ; true),
  CurN1 is CurN+1,
  splitAtPos(T, CurN1, MaxN, R, Remain).

:- pred splitAtPos(list(T), integer, list(T), list(T)).

splitAtPos(L, MaxN, Before, Remain):-
  splitAtPos(L, 0, MaxN, Before, Remain).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% firstNElemsOf(+List, +N, -Elems)
%
% Given:
%   List: a normal Prolog list
%      N: an integer (>=0)
%
% Returns:
%   Elems: a list with all elements of List up until N (inclusive), or less if List has less than N elements
%
% Notes:
%   This is equivalent to splitAtPos(List, N, Elems, _),!.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred firstNElemsOf(list(T), integer, integer, list(T)).

firstNElemsOf([], _, _, []):-!.
firstNElemsOf([E|_], N, N, [E]):-!.
firstNElemsOf([E|T], CurN, N, [E|R]):-
  CurN1 is CurN+1,
  firstNElemsOf(T, CurN1, N, R).

:- pred firstNElemsOf(list(T), integer, list(T)).

firstNElemsOf(_, 0, []):-!.
firstNElemsOf(List, N, Elems):-
  firstNElemsOf(List, 1, N, Elems).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% afterFirstNElemsOf(+List, +N, -Result)
%
% Given:
%   List: an arbitrary Prolog list
%      N: an integer
%
% Returns:
%   Result: a list with all elements of List after the first N elements (or empty, if List has <= N elements)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred afterFirstNElemsOf(list(T), integer, list(T)).

afterFirstNElemsOf(List, N, Result):-
  afterFirstNElemsOf(List, 1, N, Result).

:- pred afterFirstNElemsOf(list(T), integer, integer, list(T)).

afterFirstNElemsOf([], _, _, []):-!.
afterFirstNElemsOf(List, N, N, List):-!.
afterFirstNElemsOf([_|T], CurN, N, R):-
  CurN1 is CurN+1,
  afterFirstNElemsOf(T, CurN1, N, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% replaceAt(+List, +Position, +Elem, -NList)
%
% Given:
%   List: an arbitrary Prolog list
%      N: an integer, a position in the list (1 based)
%   Elem: the element to replace at position N
%
% Returns:
%  NList: List with element at position N replaced by Elem
%
% Example:
%  replaceAt([a,b,c,d],3,x,NList). NList=[a,b,x,d]
%
% Notes:
%   If Position is not valid, nothing is replaced
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred replaceAt(list(T), integer, T, list(T)).

replaceAt(L, Pos, Elem, R):-
  replaceAt(L, 1, Pos, Elem, R).

:- pred replaceAt(list(T), integer, integer, T, list(T)).

%replaceAt(+List, +CurPos, +Pos, +Elem, -NList).
replaceAt([], _, _, _, []):-!.
replaceAt([_|T], Pos, Pos, Elem, [Elem|T]):-!.
replaceAt([H|T], CurPos, Pos, Elem, [H|R]):-
  CurPos1 is CurPos+1,
  replaceAt(T, CurPos1, Pos, Elem, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% split(+List, +Elem, -Before, -After)
%
% Given:
%   List: a normal Prolog list
%   Elem: an element of the list
%
% Returns:
%   Before: a list with all elements of List before Elem
%   After: a list with all elements of List after Elem
%
%   This fails if Elem does not occur in List
%
% Notes:
%   This is logically equivalent to: append(Before, [Elem|After], List)
%   However procedurally it's slightly different as with split/4 we return the elements from the start
%   of the list where as in append/3, it starts from the end of the list.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred split(list(T), T, list(T), list(T)).

split([Elem|T], Elem, [], T).
split([H|T], Elem, [H|Before], After):-
  split(T, Elem, Before, After).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% elemsAtPos(+ValuesList, +PositionsList, -ValuesAtPositionsList)
%
% Given:
%    ValuesList: a list of arbitrary Prolog terms
%    PositionsList: an ascending sorted list of positions (integers), 1 based
% Returns:
%    In ValuesAtPositionsList, the elements of ValuesList in PositionsList
%
% E.g.
%   elemsAtPos([A,1,2,g,h], [1,3,4], L). L=[A,2,g]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% elemsAtPos(+ValuesList, +PositionsList, +CurPos, -ValuesAtPositionsList)

:- pred elemsAtPos(list(T), list(integer), integer, list(T)).

elemsAtPos(_, [], _, []):-!.
elemsAtPos([V|Values], [CurPos|Positions], CurPos, [V|Result]):-
  !,CurPos1 is CurPos+1,
  elemsAtPos(Values, Positions, CurPos1, Result).
elemsAtPos([_|Values], Positions, CurPos, Result):-%Head of Positions > CurPos
  CurPos1 is CurPos+1,
  elemsAtPos(Values, Positions, CurPos1, Result).

:- pred elemsAtPos(list(T), list(integer), list(T)).

elemsAtPos(Values, Positions, Result):-
  elemsAtPos(Values, Positions, 1, Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% relative_position(+InList, -OutList)
%
% Given:
%   InList: an arbitrary list
%
% Returns:
%   OutList: the input list with each element of OutList being a tuple: element-original position
%                                                                                  (1 based)
%
% E.g.
%   relative_position([b,y,x,a], [b-1,y-2,x-3,a-4])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred relative_position(list(T), list(pair(T,integer))).

relative_position(InList, OutList):-
  relative_position(InList, 1, OutList).

:- pred relative_position(list(T), integer, list(pair(T,integer))).

relative_position([], _, []):-!.
relative_position([H|T], Pos, [H-Pos|R]):-
  Pos1 is Pos+1,
  relative_position(T, Pos1, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% order_list(+InList, -OutList)
%
% Given:
%   InList: an arbitrary list
%
% Returns:
%   OutList: the input list sorted with each element of OutList being a tuple: element-original position
%
% E.g.
%   order_list([b,y,x,a], [a-4,b-1,x-3,y-2])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred order_list(list(T), list(pair(T,integer))).

order_list(InList, OutList):-
  relative_position(InList, TList),
  keysort(TList, OutList).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% find_minimum(+List, +MinKey, -MinList)
%
% Given:
%  List: a non empty list of pairs Key-Value 
%  MinKey: threshold on the minimum key
%
% Returns
%  MinList: a list where the head is the first element of list that has a key =< MinKey,
%           if no such element exists then the element with smallest key is the head.
%           The remaining elements of MinList are in the original order
%
% Example:
%   find_minimum([3-a,4-b,2-c,1-x], 2, R). R= [2-c,4-b,3-a,1-x,0-p]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred find_minimum(list(pair(Key,Value)), Key, list(pair(Key,Value))).

find_minimum([K-V|L], MinKey, [BP|R]):-
  find_minimum(L, MinKey, K-V, BP, R). %BP stands for BestPair

:- pred find_minimum(list(pair(Key,Value)), Key, pair(Key,Value), pair(Key,Value), list(pair(Key,Value))).

%find_minimum(+List, +MinimumKey, +CurBestPair, -FinalBestPair, -MinList)
find_minimum(L, MK, K-V, K-V, L):-
  K=<MK, !.
find_minimum([], _, BP, BP, []):-!.
find_minimum([K1-V1|L], MK, K0-V0, BP, [KH-VH|R]):-
  (K1<K0 ->
    KH=K0, VH=V0,
    NK0=K1, NV0=V1
   ;
    KH=K1, VH=V1,
    NK0=K0, NV0=V0
  ),
  find_minimum(L, MK, NK0-NV0, BP, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% tuples_to_lists(+Tuples, +Lists)
%
% Given:
%   Tuples: a list where each element is a tuple of the same arity. The tuple name is ignored
%
% Returns:
%   Lists: a list with tuple arity lists. List 'i' has all the values of argument 'i' of Tuples
%
% E.g.
%   tuples_to_lists([f(a,b),f(c,d),f(e,f)], R).
%                  R=[[a,c,e],[b,d,f]])
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

tuples_to_lists([], List):-
  close_list(List), !. % cut to avoid infinite recursion if initial Tuples is the empty list
tuples_to_lists([Tuple|Tuples], List):-
  Tuple=..[_|Args],
  add_to_list(Args, List, ListTails),
  tuples_to_lists(Tuples, ListTails).

close_list([]).
close_list([[]|T]):-
  close_list(T).

:- pred add_to_list(list(T), list(list(T)), list(list(T))).

%add_to_list(+Values, +List, -Tails)
add_to_list([], [], []).
add_to_list([Arg|Args], [[Arg|T]|L], [T|R]):-
  add_to_list(Args, L, R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% lists_to_tuples(+Lists, +FunctorName, -Tuples)
%
% Given:
%   Lists: a list of lists. (all with the same number of elements)
%   FunctorName: a name for the functor
%
% Returns:
%   Tuples: a list of tuples. Each is a term with arity equal to length of Lists.
%           Main functor has FunctorName and each argument is taken from the head of each list in Lists
%
% E.g.
%   lists_to_tuples([[a,c,e],[b,d,f]], f, R).
%                   R=[f(a,b),f(c,d),f(e,f)]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- pred lists_to_tuples(list(list(A)), list(list(list(A))),list(list(list(A)))).

lists_to_tuples([], _, []):-!. % empty list case
lists_to_tuples([[]|_], _, []):-!. % base case of recursion
lists_to_tuples(List, FunctorName, [Tuple|Tuples]):-
  add_to_list(Args, List, ListTails),
  Tuple=..[FunctorName|Args],
  lists_to_tuples(ListTails, FunctorName, Tuples).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% merge_keys(+IList, -OList)
% merge_sorted_keys(+List, OList) % assumes IList has its keys sorted
%
% Given:
%   IList: a list, possible not ordered, where each element is of the form: Key-Value  (Key may be a variable)
%
% Returns:
%   OList: a list where the key appears only once and all the values associated with that
%          key in a sorted list
%
% E.g.
%  merge_keys([A-4,A-2,B-1], [A-[2,4],B-[1]]) 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

merge_keys(IL, OL):-
  keysort(IL, KSIL), % we must sort the initial list for identical keys to appear consecutively
  merge_sorted_keys(KSIL, OL).

merge_sorted_keys([], []):-!.
merge_sorted_keys([K-V|R], OL):-
  merge_sorted_keys_aux([K-[V]|R], OL).

%:- trust_pred sort(list(T), list(T)).
%:- pred merge_sorted_keys_aux(list(pair(K,list(V))), list(pair(K,list(V)))).

merge_sorted_keys_aux([K-V1], [K-V2]):-
  !, sort(V1, V2).
merge_sorted_keys_aux([K1-V1, K2-V2|R], ROL):-
  (K1==K2 ->
     merge_sorted_keys_aux([K1-[V2|V1]|R], ROL)
    ;
     sort(V1, SV1),
     ROL= [K1-SV1|OL],
     merge_sorted_keys_aux([K2-[V2]|R], OL)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% append_keys(+IList, -OList)
% append_sorted_keys(+IList, -OList)
%
% Identical to merge_keys/2 and merge_sorted_keys/2 but values are not sorted, just appended. Since no sort of values needs to take place, it's a bit faster
%
% E.g.
%  append_keys([A-4,A-2,B-1], [A-[4,2],B-[1]]) 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

append_keys(IL, OL):-
  keysort(IL, KSIL), % we must sort the initial list for identical keys to appear consecutively
  append_sorted_keys(KSIL, OL).

append_sorted_keys([], []):-!.
append_sorted_keys([K-V|R], OL):-
  append_sorted_keys_aux([K-[V]|R], OL).

append_sorted_keys_aux([K-V], [K-V]):-!.
append_sorted_keys_aux([K1-V1, K2-V2|R], ROL):-
  (K1==K2 ->
     append_sorted_keys_aux([K1-[V2|V1]|R], ROL)
    ;
     ROL= [K1-V1|OL],
     append_sorted_keys_aux([K2-[V2]|R], OL)
  ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% custom_qsort(+List, +ComparePredicate, -SortedList)
%
% Given:
%   List: a Prolog list
%   ComparePredicate: a predicate that compare two elements and returns how they compare. 
%                     First argument is result (must be '<', '=' or '>'). E.g. cmp(Result, Elem1, Elem2)
%
% Returns:
%   SortedList: List sorted according to ComparePredicate
%
% E.g.
%  custom_qsort([4,1,3], compare, Sorted). Sorted=[1,3,4]
%    (this is equivalent to built-in sort as compare/3 is Prolog's compare predicate)
%
% Notes:
%  This predicate should only be used when a custom sort is needed. It's implemented with difference
%  lists for extra efficiency (regular append would be more costly). The big bottleneck is, ne
% Nevertheless, it's much more
%  inneficient than built-in sort/2. Here are some results comparing custom_qsort/3
%  (using built-in compare/3) with sort/2, on random lists of integers of increasing sizes:
%
%  ?- ListSize: 100000, sort/2: 36 ms, custom_qsort/3: 1152 ms
%  ?- ListSize: 1000000, sort/2: 724 ms, custom_qsort/3: 13645 ms
%  ?- ListSize: 10000000, sort/2: 4804 ms, custom_qsort/3: 162895 ms
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- meta_predicate custom_qsort(?, :, ?).

custom_qsort(L, Compare, SL):-
  custom_qsort_aux(L, Compare, SL-[]).

:- meta_predicate custom_qsort_aux(?, :, ?).

custom_qsort_aux([], _, T-T):-!.
custom_qsort_aux([A], _, [A|T]-T):-!.
custom_qsort_aux([H|T], Compare, S-R):-
  custom_partition(T, Compare, H, SH, LH),
  custom_qsort_aux(SH, Compare, S-[H|T1]),
  custom_qsort_aux(LH, Compare, T1-R).

:- meta_predicate custom_partition(?, :, ?, ?, ?).

custom_partition([], _, _, [], []).
custom_partition([H|T], Compare, E, NSE, NLE):-
  call_with_args(Compare, Result, H, E),
  custom_partition_aux(Result, H, NSE, NLE, SE, LE),
  custom_partition(T, Compare, E, SE, LE).

%custom_partition_aux(+CompareRes, +Elem, -SmallerThanPivot, -LargerThanPivot, -RemainSmallerThanPivot, -RemainLargerThanPivot)
custom_partition_aux(<, Elem, [Elem|SP], LP, SP, LP).
custom_partition_aux(=, _Elem, SP, LP, SP, LP). % ignore element
custom_partition_aux(>, Elem, SP, [Elem|LP], SP, LP).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% randomPairs(+NumPairs, +List, -Pairs)
%
% Given:
%   NumPairs: number of pairs to return from list
%   List: an arbitrary Prolog list
%
% Returns:
%   Pairs: a list of randomly selected pairs from List. Each pair is of the form (E1, E2), where
%          E1 and E2 are elements of List
%
% Notes:
%   The implementation is not efficient. It takes O(N.L), where N is the number of pairs and L is
%   the List length
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

randomPairs(0, _, []):-!.
randomPairs(N, L, [Pair|Pairs]):-
  randomPair(L, Pair),
  N1 is N - 1,
  randomPairs(N1, L, Pairs).

%:- pred elemsAtPos(list(T), list(integer), integer, list(T)).

%randomPair(+List, -Pair)
randomPair(L, (E1, E2)):-
  length(L, N),
  random(1, N, Pos1),
  nth(Pos1, L, E1, RemainL),
  N1 is N-1,
  random(1, N1, Pos2),
  nth(Pos2, RemainL, E2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% random_elem(+List, -Elem)
% random_elem(+List, -Pos, -Elem)
% random_elem(+List, -Pos, -Elem, -RemainList)
%
% Given:
%  List: a list
%
% Returns:
%   Elem: a random element of list List.
%   Optionally returns the position 1-based, and the remaining list
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%random_elem(+List, -Pos, -Elem)
random_elem(List, Elem):-
  random_elem(List, _, Elem).

random_elem(List, Pos, Elem):-
  random_elem(List, Pos, Elem, _).

random_elem(List, Pos, Elem, RList):-
  length(List, N),
  random(1, N, Pos),
  nth(Pos, List, Elem, RList).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% randomMember(-Element, +List)
%
% Given:
%   List: an arbitrary list
% Returns:
%   Element: an element picked at random from List, by backtracking returns all elements, never
%            repeating any one, and always at random
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

randomMember(Elem, List):-
  randomMember(Elem, _, List).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% randomMember(-Element, -Pos, +List)
%
% Given:
%   List: an arbitrary list
%
% Returns:
%   Element: an element picked at random from List, by backtracking returns all elements, never repeating
%            anyone, and always at random
%   Pos: the position of the element in the original list (1 based)
%
% Notes:
%   This function should be called to generate random member through backtracking. If the purpose
%  is to get a one off random element from the list elem_at_random_pos/2(/3) should be used
%  instead.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

randomMember(Elem, RandomPos, List) :-
  add_random_keys(List, 1, KeyList), % the idea is to add random numbers as keys
  keysort(KeyList, OrderedKeyList),  % sort according to the keys (effectively, having the list sorted)
  member(_-(RandomPos, Elem), OrderedKeyList). % return the RandomPos and Element

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% randomPermutation(+InList, -OutList)
%
% Given:
%   InList: an arbitrary list
% Returns:
%   OutList: InList with elements in a random rder
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred randomPermutation(list(T), list(T)).
:- trust_pred keysort(list(pair(Key,Value)), list(pair(Key,Value))).
:- trust_pred maplist(pred(A, B), list(A), list(B)).

randomPermutation(InList, OutList):-
  add_random_keys(InList, 1, KeyList),
  keysort(KeyList, OrderedKeyList),
  maplist(removeKeyPos, OrderedKeyList, OutList).

:- type tuple(A,B) ---> (A,B).
:- pred removeKeyPos(pair(_Key, tuple(_Pos, Elem)), Elem).

removeKeyPos(_Key-(_Position, Elem), Elem).

:- pred add_random_keys(list(T), integer, list(pair(float,tuple(integer,T)))).

% add_random_keys(+List, +Pos, -List(RandomFloat-(Pos,Elem))
add_random_keys([], _, []).
add_random_keys([E| Es], N, [K-(N,E)| Ks]) :- % K-(N,E) is Key-(Position, Element)
  K is random, % K is a float between 0 and 1
  N1 is N+1,
  add_random_keys(Es, N1, Ks).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% n_randomElems(+InList, +N, -OutList)
%
% Given:
%   InList: an arbitrary list
%        N: an integer
%
% Returns:
%   OutList: N randomly choosen elements from InList (or less, if InList has less than N elems)
%
% Notes:
%   This implementation is inefficient. The current implementation has complexity O(L.log(L)) where
%   L is the number of elements in InList. This could be made O(N) (do it later)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred n_randomElems(list(T), integer, list(T)).

n_randomElems(InList, N, OutList):-
  randomPermutation(InList, SInList),
  firstNElemsOf(SInList, N, OutList).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% remove_after(+Ints, +N, -NInts)
%
% Given:
%   Ints: ascendingly ordered list of integers
%   N: last integer to be considered
%
% Returns:
%   NInts: Ints with all elements after elem of value N removed (exclusive)
%
% Examples:
%  remove_after([1,3,5,7], 4, NPos). NPos=[1,3]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove_after([], _, []):-!.
remove_after([H|T], N, [H|R]):-
  H=<N,!,
  remove_after(T, N, R).
remove_after(_, _, []):-!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% remove_positions(+List, +Positions, -NList)
%
% Given:
%   List: an arbitrary prolog list
%   Positions: ascendingly ordered list of positions to remove from List
%
% Returns:
%   NList: List with elements at Positions removed
%
% Examples:
%  remove_positions([a,b,c,d,e], [1,3,5], NList), NList=[b,d]
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove_positions(List, Positions, NList):-
  remove_positions(List, Positions, 1, NList).

%remove_positions(+List, +Positions, +CurPos, -NList)
remove_positions([], _Positions, _CurPos, []):-!.
remove_positions(L, [], _CurPos, L):-!.
remove_positions([H|T], [Pos|RPos], CurPos, NList):-
  CurPos1 is CurPos+1,
  (Pos==CurPos -> 
      NPos = RPos,
      RList = NList
    ; 
      NPos = [Pos|RPos],
      NList=[H|RList]
   ),
  remove_positions(T, NPos, CurPos1, RList).
