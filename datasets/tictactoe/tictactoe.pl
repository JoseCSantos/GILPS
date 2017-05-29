%
% This is the learning problem for tictactoe. The purpose is to learn a perfect player to play the game
%

% board is a list of positions with their values inside
% position is a number between 1 and 9
% piece is either '.', 'x' or 'o'
% player is either 'x' or 'o' 

:- modeh(bestMove(+board, -position)).
:- modeb(1, playerToMove(+board, -player)).
:- modeb(*, contains(+board, -position, +player)).
%:- modeb(1, freeAt(+board, +position)).
:- modeb(1, sameLine(+position, +position, -position)).
%:- modeb(1, oppositePlayer(+player, -player)).
%:- modeb(*, aboutToWin(+board, +player, -position)).
%:- modeb(*, not(aboutToWin(+board, +player, -position))).




%bestMove(B, Pos):-
%  playerToMove(B, Player),
%  contains(B, P1, Player),
%  contains(B, P2, Player),
%  freeAt(B, Pos),
%  sameLine(P1, P2, Pos).

%
% Induce rule:
%
%bestMove(A,B) :-
%   playerToMove(A,C),
%   contains(A,D,C),
%   sameLine(D,B,E),
%   contains(A,E,C).


:-[examples].

:- set(depth, 20).
:- set(clause_length, 5).

%:- set(maximum_singletons_in_clause, 0).

player(x).
player(o).

oppositePlayer(x, o).
oppositePlayer(o, x).
  

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

position(1).
position(2).
position(3).
position(4).
position(5).
position(6).
position(7).
position(8).
position(9).


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
  A\=B,
  member(C, Line),
  A\=C, B\=C.
