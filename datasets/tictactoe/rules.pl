:- set_prolog_flag(single_var_warnings, on).
:- set_prolog_flag(unknown, warning).

:-dynamic posExamples/1.
:-dynamic negExamples/1.

:-[examples].

player(x).
player(o).

oppositePlayer(x, o).
oppositePlayer(o, x).
  
start:-
  findall(PosEx, example(PosEx, 1), PosExs),
  assert(posExamples(PosExs)),
  findall(NegEx, example(NegEx, -1), NegExs),
  assert(negExamples(NegExs)).
  
:-start.

entailsExample(Clause, Example):-
  copy_term(Clause, (Example:-Body)),!, % Clause has body
  \+(\+(call(Body))).
entailsExample(Clause, Example):-
  \+(\+(Clause=Example)). % clause has no body
  
countCoverage([], _, Cov, Cov).
countCoverage([Ex|Exs], Clause, CurCov, FCov):-
  entailsExample(Clause, Ex),!,
  CurCov1 is CurCov+1,
  countCoverage(Exs, Clause, CurCov1, FCov).
countCoverage([_|Exs], Clause, CurCov, FCov):-
  countCoverage(Exs, Clause, CurCov, FCov).

% clauseCoverage(+Clause, -Coverage):-
%   given a clause C, returns in Coverage a term with its positive and negative coverage

clauseCoverage(Clause, cov(Pos, Neg)):-
  posExamples(PosExs),
  negExamples(NegExs),
  countCoverage(PosExs, Clause, 0, Pos),
  countCoverage(NegExs, Clause, 0, Neg).

% background knowledge


% 1|2|3
% -----
% 4|5|6
% -----
% 7|8|9

% playerToMove(+Board, -Player)
% Player is the player symbol, 'x' or 'o'

playerToMove(Board, P):-
  countPieces(Board, '.', N),
  (N mod 2=:=1 -> P=x; P=o). % if the number of empty pieces is odd then is player x turn

countPiecesAux([], _, N, N).
countPiecesAux([H|T], Player, Accum, N):-
  H\==Player,!,
  countPiecesAux(T, Player, Accum, N).
countPiecesAux([Player|T], Player, Accum, N):-
  Accum1 is Accum+1,
  countPiecesAux(T, Player, Accum1, N).

% countPieces(+Board, +Player, -N)

countPieces(Board, Player, N):-
  countPiecesAux(Board, Player, 0, N).

%1
diametrically_opposite(1,3).
diametrically_opposite(1,7).
diametrically_opposite(1,9).

%2
diametrically_opposite(2,8).

%3
diametrically_opposite(3,1).
diametrically_opposite(3,7).
diametrically_opposite(3,9).

%4
diametrically_opposite(4,6).

%5

%6
diametrically_opposite(6,4).

%7
diametrically_opposite(7,1).
diametrically_opposite(7,3).
diametrically_opposite(7,9).

%8
diametrically_opposite(8,2).

%9
diametrically_opposite(9,1).
diametrically_opposite(9,3).
diametrically_opposite(9,7).



%  :-modeb(playerToMove(+board, -player)).
%  :-modeb(oppositePlayerToMove(+player, -player)).
%  :-modeb(contains(+board, +position, +player)).
%  :-modeb(contains(+board, -position, +player)).
%  :-modeb(countPieces(+board, +player, -int)).
%  :-modeb(countPieces(+board, +player, #int)).
%  :-modeb(sameLine(+position, +position, +position)).
%  :-modeb(sameLine(-position, -position, -position)).  % or any intermediate combination

aboutToWin(Board, Player, Position):-
  contains(Board, A, Player),
  contains(Board, B, Player),
  freeAt(Board, Position),
  sameLine(A, B, Position).
  

%clauseCoverage((bestMove(Board, M):-playerToMove(Board, P),oppositePlayer(P, P1),contains(Board, Move, '.'),contains(Board, A, P1),contains(Board, B, P1),sameLine(A,B,Move)), Cov).

% rules that I want to find:
% There are on total 4520 distinct boards, 7123 positive examples, 9044 negative examples.
%  Total number of examples = 16167, default model accuracy = 9044/16167=55.94%
%  To make a perfect player we can't cover a single negative example and we need to cover
% at least one positive entry per unique board (that is, 4520 positives)
%
% one board instance 
%
% bestMove(Board, PosMove):-       % this rules covers 2782 positives (2358 unique) and 0 negatives
%    playerToMove(Board, Player),
%    contains(Board, PosA, Player),
%    contains(Board, PosB, Player),
%    freeAt(Board, PosMove),
%    sameLine(PosA, PosB, PosMove).
%
% clauseCoverage((bestMove(Board, M):-playerToMove(Board, P),oppositePlayer(P, P1),contains(Board, Move, '.'),contains(Board, A, P1),contains(Board, B, P1),sameLine(A,B,Move)), Cov).

% This is equivalent to:
%
% bestMove(Board, PosMove):-      % this rules covers 2782 positives (2358 unique) and 0 negatives
%   playerToMove(Board, Player),
%   aboutToWin(Board, Player, PosMove).
%
% clauseCoverage((bestMove(Board, M):-playerToMove(Board, P), aboutToWin(Board, P, M)), Cov).

%bestMove(Board, PosMove)

% is any example covered by both clauses? no..good

test(N):-
  %C1=(bestMove(Board, M):-playerToMove(Board, P), aboutToWin(Board, P, M)),
  C2=(bestMove(Board, M):-playerToMove(Board, P),oppositePlayer(P, P1),\+aboutToWin(Board,P,_),aboutToWin(Board,P1,M)),
  all(Board, (example(bestMove(Board,Move),1), entailsExample(C2, bestMove(Board,Move))), L),
  length(L,N).
                 
%
%
% bestMove(Board, Move):-        % this rules covers 2056 positives (1484 unique) but 0 negatives
%    playerToMove(Board, P),
%    \+aboutToWin(Board, P, _),
%    oppositePlayer(P, P1),
%    aboutToWin(Board, P1, Move). % block opposite player who is about to win at Move
%
% clauseCoverage((bestMove(Board, M):-playerToMove(Board, P),oppositePlayer(P, P1),\+aboutToWin(Board,P,_),aboutToWin(Board,P1,M)), Cov).
%
% there is no intersection between the 2 clauses, 2358+1484=3842 unique (of 4520)
%
%

numMoves(Board, NumMoves):-
  countPieces(Board, '.', NumEmpties),
  NumMoves is 9-NumEmpties.
  
freeAt(Board, Position):-
  contains(Board, Position, '.').
  
%bestMove(Board, PosMove):-        % covers 9 positives and 0 negatives
%  numMoves(Board,NumMoves),
%  NumMoves<2,
%  center(PosMove),
%  freeAt(Board, PosMove).

%bestMove(Board, PosMove):-        % covers 8 positives and 0 negatives, probably not worth it
%  numMoves(Board,0),
%  position(PosMove).

%clauseCoverage((bestMove(Board, Move):-numMoves(Board,NumMoves),NumMoves<2,center(Move),\+forkAt(Board,PosMove),freeAt(Board, Move)),Cov).

% forkAt(+Board, -Move): returns in Move the board position where, if player to play moves there
%   creates a winning scenario in 2 ways.

forkAt(Board, Move):-
  playerToMove(Board, Player),
  \+aboutToWin(Board, Player, _),
  freeAt(Board, Move),
  contains(Board, Pos1, Player),
  contains(Board, Pos2, Player),
  Pos1\=Pos2, % this literal is not strictly needed
  freeAt(Board, Pos3),
  sameLine(Pos1, Move, Pos3),
  freeAt(Board, Pos4),
  Pos3\=Pos4,
  sameLine(Pos2, Move, Pos4).

%bestMove(Board, Move):-            % fork, covers 112 positives and 0 negatives
%  forkAt(Board, Move).


corner(1).
corner(3).
corner(7).
corner(9).

edge(2).
edge(4).
edge(6).
edge(8).

center(5).

%clauseCoverage((bestMove(B, Move):-forkAt(B, Move)), Cov)

testCoverage(Cov):-
  clauseCoverage(      
   (bestMove(Board, Pos):-
     playerToMove(Board, Player),
     \+aboutToWin(Board,Player,_),
     contains(Board, Pos1, Player),
     freeAt(Board,Pos),
     diametrically_opposite(Pos1, Pos),
     sameLine(Pos1, Pos, Pos2),
     freeAt(Board,Pos2)
   ), Cov).
   
counterExample(E):-
  C=(bestMove(Board, Pos):-
     playerToMove(Board, Player),
     \+aboutToWin(Board,Player,_),
     contains(Board, Pos1, Player),
     freeAt(Board,Pos),
     diametrically_opposite(Pos1, Pos),
     sameLine(Pos1, Pos, Pos2),
     freeAt(Board,Pos2)),
  example(E,-1),
  entailsExample(C, E).
   
   
posExamplesNotEntailed(E):-
  C1=(bestMove(Board, PosMove):-
        playerToMove(Board, Player),
        aboutToWin(Board, Player, PosMove)
     ),
  C2=(bestMove(Board, Move):-
        playerToMove(Board, P),
        \+aboutToWin(Board, P, _),
        oppositePlayer(P, P1),
        aboutToWin(Board, P1, Move)
     ),
  C3=(bestMove(Board, PosMove):-
        numMoves(Board,NumMoves),
        NumMoves<2,
        center(PosMove),
        freeAt(Board, PosMove)
     ),  
  C4=(bestMove(Board, Move):-      
        forkAt(Board,Move)
     ),
  example(E, 1),
  \+entailed([C1,C2,C3,C4],E).
  
entailed([C|_], E):-
  entailsExample(C, E),!.
entailed([_|T], E):-
  entailed(T, E).
  

position(1).
position(2).
position(3).
position(4).
position(5).
position(6).
position(7).
position(8).
position(9).


contains([], _, _, _):-!, fail.
contains([Mark|_], Pos, Pos, Mark).
contains([_|T], CurPos, Pos, Mark):-
  CurPos1 is CurPos+1,
  contains(T, CurPos1, Pos, Mark).

%contains(+Board, +Position, +Mark)
%contains(+Board, -Position, +Mark)
contains(Board, Pos, Mark):-
  contains(Board, 1, Pos, Mark).

% below are the possible lines. Inside each line the numbers are increasing

win_lines([
           [1,2,3],[4,5,6],[7,8,9], % rows
           [1,4,7],[2,5,8],[3,6,9], % cols
           [1,5,9],[3,5,7] % diagonals
          ]).

member(H, [H|_]).
member(H, [_|T]):-
  member(H, T).
  
%sameLine(?A,?B,?C) doesn't require any argument to be instantiated
sameLine(A,B,C):-
  win_lines(Ls),
  member(Line, Ls),
  member(A, Line),
  member(B, Line),
  member(C, Line),
  A\=B, A\=C, B\=C.
