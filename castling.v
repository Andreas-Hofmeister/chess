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

Fixpoint forall_in {A} (l : list A) (f : A -> bool) : bool :=
  match l with
  | [] => true
  | x::xs => if (negb (f x)) then false else (forall_in xs f)
  end.

Definition can_make_castling_move (pos : Position) (c : Color) 
(ctype : CastlingType) :=
  (andb (exists_in (castling_availabilities pos)
    (fun cavl => (cavleq cavl (Cavl ctype c))))
  (andb (forall_in (empty_castling_squares c ctype)
    (fun loc => is_square_empty loc (get_piece_placements pos)))
  (andb (eqSq (square_at_location pos (rook_castling_square c ctype))
    (Occupied c Rook))
  (andb (eqSq (square_at_location pos (king_castling_square c))
    (Occupied c King))
  (andb (negb (is_in_check pos c))
  (forall_in (empty_castling_squares c ctype)
    (fun loc => (negb (attacks_empty_square pos (opponent_of c) loc))))))))).

(*
Definition castling_moves (pos : Position) (c : Color) :=
  if (andb (exists_in (castling_availabilities pos) 
            (fun cavl => (cavleq cavl (Cavl c 
*)

