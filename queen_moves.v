Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.
From CHESS Require Export rook_moves.
From CHESS Require Export bishop_moves.

Inductive QueenCanMakeMove (pos : Position)
: SquareLocation -> Color -> Move -> Prop :=
  | QueenCanMoveLikeRook : forall from c move,
    RookCanMakeMove pos from c move -> QueenCanMakeMove pos from c move
  | QueenCanMoveLikeBishop : forall from c move,
    BishopCanMakeMove pos from c move -> QueenCanMakeMove pos from c move.

Definition queen_moves (l : SquareLocation) (c : Color) (pos : Position) 
: (list Move) :=
  (rook_moves l c pos) ++ (bishop_moves l c pos).

(*****Proofs*****)

Lemma queen_moves_from : forall l c pos move,
  In move (queen_moves l c pos) -> fromOfMove move = l.
Proof.
  intros l c pos move Hin. unfold queen_moves in *. repeat in_app_to_or.
  - eapply rook_moves_from; eauto.
  - eapply bishop_moves_from; eauto.
Qed.

Lemma queen_moves_sound : forall move fromL c pos,
  location_valid fromL ->
  In move (queen_moves fromL c pos) -> QueenCanMakeMove pos fromL c move.
Proof.
  intros move fromL c pos Hv Hin.
  unfold queen_moves in *. in_app_to_or. destruct Hin as [Hin | Hin].
  - apply QueenCanMoveLikeRook. apply rook_moves_sound; auto.
  - apply QueenCanMoveLikeBishop. apply bishop_moves_sound; auto.
Qed.

Lemma queen_moves_complete : forall pos fromL c move,
  QueenCanMakeMove pos fromL c move -> In move (queen_moves fromL c pos).
Proof.
  intros pos fromL c move Hcan.
  unfold queen_moves. in_app_to_or. inversion Hcan; subst.
  - left. apply rook_moves_complete. auto.
  - right. apply bishop_moves_complete. auto.
Qed.
