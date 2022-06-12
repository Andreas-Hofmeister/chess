Require Import List.
Require Import Nat.
From CHESS Require Export movement_basics.
From CHESS Require Export pawn_moves.
From CHESS Require Export rook_moves.
From CHESS Require Export bishop_moves.
From CHESS Require Export knight_moves.
From CHESS Require Export queen_moves.
From CHESS Require Export king_moves.

(* Definition of when a piece attacks a square or another piece *)

(* Definitions *)

Inductive APieceCanMakeMove (pos : Position) : Color -> Move -> Prop := 
  | MoveCanBeMadeByPawn : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Pawn ->
    PawnCanMakeMove pos from move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByRook : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Rook ->
    RookCanMakeMove pos from move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByBishop : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Bishop ->
    BishopCanMakeMove pos from move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByKnight : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Knight ->
    KnightCanMakeMove pos from move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByQueen : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Queen ->
    QueenCanMakeMove pos from move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByKing : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color King ->
    KingCanMakeMove pos from move -> APieceCanMakeMove pos color move.

Inductive AttacksEmptySquare (pos : Position) 
  : Color -> SquareLocation -> Prop :=
  | AttacksEmptySquare_iff : forall color loc move,
    loc = toOfMove move -> IsMoveToEmptySquare move ->
    APieceCanMakeMove pos color move -> AttacksEmptySquare pos color loc.

Inductive AttacksOccupiedSquare (pos : Position)
  : Color -> SquareLocation -> Prop :=
  | AttacksOccupiedSquare_iff : forall color loc move,
    loc = toOfMove move -> IsCapturingMove move ->
    APieceCanMakeMove pos color move -> AttacksOccupiedSquare pos color loc.

Definition Attacks (pos : Position) (c : Color) (loc : SquareLocation) : Prop
  := AttacksEmptySquare pos c loc \/ AttacksOccupiedSquare pos c loc.

