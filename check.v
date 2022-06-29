Require Import List.
Require Import Nat.
From CHESS Require Export attacks.

(** Definitions **)

Inductive IsInCheck (pos : Position) : Color -> Prop :=
  | IsInCheckIff : forall pp c pos_c dstep cavl king_rank king_file,
    pos = Posn pp pos_c dstep cavl ->
    get_square_by_index pp king_rank king_file = Occupied c King ->
    AttacksOccupiedSquare pos (opponent_of c) (Loc king_rank king_file) ->
    IsInCheck pos c.

Definition find_king (pos : Position) (c : Color) := 
  find_piece pos c King valid_locations.

Definition is_in_check (pos : Position) (c : Color) : bool :=
  exists_in (find_king pos c) 
  (fun king_loc => (attacks_occupied_square pos c king_loc)).


