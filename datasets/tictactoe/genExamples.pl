% tic tac toe in Prolog
%
% Jose Santos, January 2009

:- set_prolog_flag(single_var_warnings, on).
:- set_prolog_flag(unknown, warning).

:- dynamic rec_minimax/2.


% the game is represented by a list with 9 positions
% [_,_,_,_,_,_,_,_,_] where:
%  . represents empty
%  x represents a player A piece
%  o represents a player B piece
%
% player A plays first

empty('.').
numPlaces(9).

opposite(x, o).
opposite(o, x).

% playerToMove(+Board, -Player)
% Player is the player symbol, 'x' or 'o'
playerToMove(Board, P):-
  empty(E),
  countPieces(Board, E, N), % t
  (N mod 2=:=1 -> P=x; P=o).

turnID2PlayerToMove(TurnID, P):-
  (TurnID mod 2=:=1 -> P=x; P=o).

% countPieces(+Board, +Player, -N)

countPiecesAux([], _, N, N).
countPiecesAux([H|T], Player, Accum, N):-
  H\==Player,!,
  countPiecesAux(T, Player, Accum, N).
countPiecesAux([Player|T], Player, Accum, N):-
  Accum1 is Accum+1,
  countPiecesAux(T, Player, Accum1, N).
countPieces(Board, Player, N):-
  countPiecesAux(Board, Player, 0, N).

% place(+Board, +Player, +CurPosition, -Position, -NewBoard).
place([H|T], Player, CurPos, CurPos, [Player|T]):-
  empty(H).
place([H|T], Player, CurPos, FPos, [H|R]):-
  CurPos1 is CurPos+1,
  place(T, Player, CurPos1, FPos, R).

% place(+Board, +Player, ?Position, -NewBoard).  
place(Board, Player, Position, NewBoard):-
  place(Board, Player, 1, Position, NewBoard).

% possibleMoves(+Board, -Position, -NBoard)
% 
possibleMoves(Board, Position, NBoard):-
  playerToMove(Board, Player),
  place(Board, Player, Position, NBoard).
  
% row(+Player, +Board): %succeeds if Player has 3 marks in the same row
row(A, [A,A,A,_,_,_,_,_,_]).
row(A, [_,_,_,A,A,A,_,_,_]).
row(A, [_,_,_,_,_,_,A,A,A]).

% col(+Player, +Board): %succeeds if Player has 3 marks in the same col
col(A, [A,_,_,A,_,_,A,_,_]).
col(A, [_,A,_,_,A,_,_,A,_]).
col(A, [_,_,A,_,_,A,_,_,A]).

%diag(+Board,-Diag)
diag(A, [A,_,_,_,A,_,_,_,A]).
diag(A, [_,_,A,_,A,_,A,_,_]).

% win(+Board, +Player): succeeds if Player has won

win(Board, Player):-
  row(Player, Board).
win(Board, Player):-
  col(Player, Board).
win(Board, Player):-
  diag(Player, Board).

% continuePlay(+Board)
continuePlay(Board):-
  \+win(Board, x),
  \+win(Board, o),
  hasEmptySquares(Board).

% gameOver(+Board)
gameOver(Board):- win(Board, x),!.
gameOver(Board):- win(Board, o),!.
gameOver(Board):- \+hasEmptySquares(Board).
  
hasEmptySquares(['.'|_]):-!.
hasEmptySquares([_|T]):-
  hasEmptySquares(T).

%%%% prints all games with respective result

buildBoard([]).
buildBoard([Pos|T]):-
  member(Pos, [.,o,x]),
  buildBoard(T).

% playingBoard(-B) returns in backtracking all
% tictactoe games that are not over (i.e. there are still valid moves to do),
% use with findall to collect all boards
playingBoard(B):-
  B=[_,_,_,_,_,_,_,_,_],
  buildBoard(B),
  validBoard(B),
  continuePlay(B).

validBoard(Board):-
  countPieces(Board, x, NX),
  countPieces(Board, o, NO),
  (NX=:=NO;NX=:=NO+1).

% split(+Elem, +List, -BeforeElem, -AfterElem)

split(E, [E|T], [], T).
split(E, [H|L], [H|B], A):-
  split(E, L, B, A).

append([], L, L).
append([H|T], L, [H|R]):-
  append(T, L, R).

winPlayerToScore('x', +1).
winPlayerToScore('o', -1).

% minOf(+List, +CurMin, -FinalMin)
minOf([], Min, Min).
minOf([H|T], CurMin, FMin):-
  compRes(H, CurMin, NewCurMin, _),
  minOf(T, NewCurMin, FMin).
minOf([H|T], R):-
  minOf(T, H, R).

% maxOf(+List, +CurMax, -FinalMax)
maxOf([], Max, Max).
maxOf([H|T], CurMax, FMax):-
  compRes(H, CurMax, _, NewCurMax),
  maxOf(T, NewCurMax, FMax).
maxOf([H|T], R):-
  maxOf(T, H, R).

%compRes(+Res1,+Res2,-WorseResult,-BestResult)
%
% if Res1 and Res2 are equal, Res1 is considered Best

compRes(res(S1,T1), res(S2,T2), res(S1,T1), res(S2,T2)):- S1<S2,!.
compRes(res(S1,T1), res(S2,T2), res(S2,T2), res(S1,T1)):- S1>S2,!.
compRes(res(-1,T1), res(-1,T2), res(-1,T2), res(-1,T1)):- T1>=T2,!.%in case scores are equal and negative
compRes(res(-1,T1), res(-1,T2), res(-1,T1), res(-1,T2)):- T1<T2,!.%in case scores are equal and negative
compRes(res(S,T1), res(S,T2), res(S,T2), res(S,T1)):- S>=0,T1=<T2,!.%in case scores are equal and non negative
compRes(res(S,T1), res(S,T2), res(S,T1), res(S,T2)):- S>=0,T1>T2,!.%in case scores are equal and non negative


%strategyForPlayer(+Player, +ListOfResults, -BestResult)
%
% each result is of the form res(Score, TurnID)
%
% The best result is returned: (only one)
%
%  The results' score are from player 'x' perspective.
%    A result is better than other if it has higher score, in case of same score
%      then if score is positive then lower TurnID is better  (i.e. win in less moves)
%           if score is negative then higher TurnID is better (i.e. take longer to lose)

strategyForPlayer('x', L, Res):-
  maxOf(L, Res).
strategyForPlayer('o', L, Res):-
  minOf(L, Res).

% mini-max for tic-tac-toe
% minimax(+Board, +TurnID, -Result): Given a Board returns its end result from player x perspective
%
%  the result is a tuple (Score, TurnIDWhenScore is achieved)
%  the Score is either: +1 if player A wins, 0 if draw, -1 if player B wins
%  the TurnID when score is achieved is from the beginning of the game, the smaller the number the better
%  in case of victory. In case of defeat the bigger the number the better. In case of draw the turnid
%  does not matter. It is always 9.
%
%  Move is the move the current player to move should make. It is a number from 1 to 9
%  Returns 0 if there is no move to be done (e.g. game is already over)

minimax(Board, _, Result):-
  rec_minimax(Board, Result),!. % see if result, move was in cache
minimax(Board, TurnID, res(Score, TurnID)):-
  member(Player, [x,o]),%we don't need to check win for both players
  win(Board, Player),!,
  winPlayerToScore(Player, Score),
  asserta(rec_minimax(Board, res(Score, TurnID))).
minimax(Board, 10, res(0,10)):-
  !, 
  asserta(rec_minimax(Board, res(0,10))). %draw
minimax(Board, TurnID, Result):-
  turnID2PlayerToMove(TurnID, Player),
  NextTurnID is TurnID+1,
  findall(TempResult,
             (%this is to do a move, i.e. Player to put its mark on the board at an empty position
              split('.', Board, Before, After),
              append(Before, [Player|After], NBoard),
              minimax(NBoard, NextTurnID, TempResult)),
          AllTempResults),
  strategyForPlayer(Player, AllTempResults, Result),
  asserta(rec_minimax(Board, Result)).

genMoves:-
  playingBoard(Board),
  possibleMoves(Board, MoveSquare, NewBoard),
  countPieces(NewBoard, '.', NumEmpty),
  TurnID is 9-NumEmpty+1,
  minimax(NewBoard, TurnID, Res),
  %Res=res(Score,_),format("example(move(~w,~w,~w)).~N", [Board, MoveSquare, Score]),
  asserta(move(Board,MoveSquare,Res)),
  fail.
genMoves.

member(H, [H|_]).
member(H, [_|T]):-
  member(H, T).

adjustScore(L, x, L):-!.
adjustScore([], o, []).
adjustScore([r(res(Score,Turn),M)|T], o, [r(res(AScore,Turn),M)|RT]):-
  AScore is -Score,
  adjustScore(T, o, RT).


% highestMoveResultsAux(+ListOfMovesAndResults, +CurBestResult, +CurBestResultList, -FinalBestResultList)

highestMoveResultsAux([], _, L, L).
highestMoveResultsAux([r(CB,Move)|T], CB, CBList, FBList):- %CB is equal to the best so far, add it to list
  !, 
  highestMoveResultsAux(T, CB, [Move|CBList], FBList).
highestMoveResultsAux([r(Res,M)|T], CB, _, FBList):-
  compRes(Res, CB, _, Res),!,% Res is better
  highestMoveResultsAux(T, Res, [M], FBList).
highestMoveResultsAux([_|T], CB, CBList, FBList):-
  % Result and move, ignored here, are worse
  highestMoveResultsAux(T, CB, CBList, FBList).
  
% highestMoveResults(+ListOfMovesAndResults, -ListOfMovesWithHighestResult)
% ListOfMovesAndResults is a list where each item is of the form:
%  r(res(Score,Turn), Move)

%bug: highestMoveResults([r(res(-1,8),3),r(res(-1,6),4),r(res(-1,3),7)],R)
% is returning R={7] rather than R=[3]
% highestMoveResults([r(res(-1,8),3),r(res(-1,6),4)],R)
highestMoveResults([r(Res,Move)|T], HS):-
  highestMoveResultsAux(T, Res, [Move], HS).

% bestMove([.,x,.,.,.,.,.,.,.],X).

% bestMove(+Board, -Move)
%  Move is the square that the player to play should move, in order to maintain or increase its final score
%  It is a number from 0..9, where 0 means give up (i.e. the other player has a guaranteed win)
%  There may be several optimal moves for the same board

% bestMove([.,.,.,.,.,x,o,o,x],M).

bestMove(Board, BestMove):-
% move term is of the form:
% output format is move(+Board, +PositionToMove, +GameResultFromPlayerToPlayPerspectiveAfterMove)
% BoardValues are always from player 'X' perspective
% E.g. move([.,.,.,x,.,x,o,.,.],3,res(1,6))
  all(r(BoardResAfterMove, Move), move(Board, Move, BoardResAfterMove), MoveResults),
  playerToMove(Board, Player),
  adjustScore(MoveResults, Player, AdjustedMoveResults),
  highestMoveResults(AdjustedMoveResults, HMR),
  member(BestMove, HMR).

genBestMoves:-
  playingBoard(Board),
  bestMove(Board, Move),
  asserta(precomputed_BestMove(Board, Move)),
  fail.
genBestMoves.

writeExamplesForBoard(Board):-
  forall(precomputed_BestMove(Board, Move), format("example(bestMove(~w,~w),1).~N", [Board, Move])), %write positive examples
  forall( (possibleMoves(Board, Move, _), % this is to discard illegal moves, an illegal move is not a negative example
           (\+precomputed_BestMove(Board, Move))),
           format("example(bestMove(~w,~w),-1).~N", [Board, Move])). %write negative examples

writeExamples:-
  playingBoard(Board),
  writeExamplesForBoard(Board),
  fail.
writeExamples.

:- genMoves, genBestMoves, writeExamples.

