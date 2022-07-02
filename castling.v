Require Import List.
Require Import Nat.
From CHESS Require Export attacks.
From CHESS Require Export check.

(** Definitions **)
(*
Inductive CanMakeCastlingMove (pos : Position) : Color -> Move -> Prop
  | CanCastleQueenSide : forall pp c pos_c dstep cavl castling_type,
    pos = Posn pp pos_c dstep cavl -> In (Cavl castling_type c) cavl ->
*)
