Require Import List.
Require Import Nat.
From CHESS Require Export basics.
From CHESS Require Export attacks.
From CHESS Require Export check.

(** Definitions **)

Definition empty_castling_squares (c : Color) (t: CastlingType) :=
  match c,t with
  | White,QueenSide => [Loc 0 1; Loc 0 2; Loc 0 3]
  | White,KingSide => [Loc 0 5; Loc 0 6]
  | Black,QueenSide => [Loc 7 1; Loc 7 2; Loc 7 3]
  | Black,KingSide => [Loc 7 5; Loc 7 6]
  end.

Definition rook_castling_square (c : Color) (t : CastlingType) :=
  match c,t with
  | White,QueenSide => Loc 0 0
  | White,KingSide => Loc 0 7
  | Black,QueenSide => Loc 7 0
  | Black,KingSide => Loc 7 7
  end.

Definition king_castling_square (c : Color) :=
  match c with
  | White => Loc 0 4
  | Black => Loc 7 4
  end.

Inductive CanMakeCastlingMove (pos : Position) : Color -> Move -> Prop :=
  | CanCastleIff : forall pp pos_c dstep cavl c ctype,
    pos = Posn pp pos_c dstep cavl -> In (Cavl ctype c) cavl ->
    (forall l, In l (empty_castling_squares c ctype)
      -> is_square_empty l pp = true) ->
    IsOccupiedBy pos (rook_castling_square c ctype) c Rook ->
    IsOccupiedBy pos (king_castling_square c) c King ->
    ~(IsInCheck pos c) ->
    (forall l, In l (empty_castling_squares c ctype)
      -> ~(AttacksEmptySquare pos (opponent_of c) l)) ->
    CanMakeCastlingMove pos c (Castle c ctype).


