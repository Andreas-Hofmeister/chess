Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.
(*
Inductive KingCanMakeMove (pos : Position) : 
  SquareLocation -> Move -> Prop :=
  | KingCanMove : forall ,
    location_valid from -> location_valid to ->
    are_squares_adjacent from to -> from <> to ->
    *)
