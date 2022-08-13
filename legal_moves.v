Require Import List.
Require Import Nat.
From CHESS Require Export attacks.
From CHESS Require Export make_move.
From CHESS Require Export check.

Definition puts_king_in_check (pos : Position) (move : Move) :=
  (is_in_check (make_move pos move) (get_to_move pos)).

(* Calculates the list of legal moves in a position *)
Definition legal_moves (pos : Position) : list Move :=
  filter (fun move => negb (puts_king_in_check pos move))
  (moves_by_player pos (get_to_move pos)).


