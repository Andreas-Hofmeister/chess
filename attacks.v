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

(** Definitions **)

Inductive APieceCanMakeMove (pos : Position) : Color -> Move -> Prop := 
  | MoveCanBeMadeByPawn : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Pawn ->
    PawnCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByRook : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Rook ->
    RookCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByBishop : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Bishop ->
    BishopCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByKnight : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Knight ->
    KnightCanMakeMove pos from color  move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByQueen : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Queen ->
    QueenCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByKing : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color King ->
    KingCanMakeMove pos from color move -> APieceCanMakeMove pos color move.

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

Definition moves_by_player_from_square (pos : Position) (c : Color) 
(loc : SquareLocation) : (list Move) :=
  match pos, loc with
  | Posn pp _ _ , Loc r f 
    => match get_square_by_index pp r f with
      | Empty => []
      | Occupied sc p => 
        if ceq c sc then match p with
        | Pawn => pawn_moves loc c pos
        | Rook => rook_moves loc c pos
        | Bishop => bishop_moves loc c pos
        | Knight => knight_moves loc c pos
        | Queen => queen_moves loc c pos
        | King => king_moves loc c pos
        end else []
      end
  end.

Definition moves_by_player (pos : Position) (c : Color) : (list Move) :=
  append_forall (fun sq => moves_by_player_from_square pos c sq) 
  valid_locations.

(** Proofs **)


