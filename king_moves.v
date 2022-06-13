Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.

(* Definitions *)

Inductive KingCanMakeMove (pos : Position) : 
  SquareLocation -> Move -> Prop :=
  | KingCanMove : forall from to pp c dstep,
    location_valid from -> location_valid to ->
    pos = Posn pp c dstep ->
    SquaresAdjacent from to -> is_square_empty to pp = true ->
    KingCanMakeMove pos from (FromTo from to)
  | KingCanCapture : forall from to pp c dstep,
    location_valid from -> location_valid to ->
    pos = Posn pp c dstep ->
    SquaresAdjacent from to -> 
    is_square_occupied_by_enemy_piece to pp c = true ->
    KingCanMakeMove pos from (FromTo from to).

Definition king_moves_to_empty_square (loc : SquareLocation) (pos : Position)
  : (list Move) :=
  