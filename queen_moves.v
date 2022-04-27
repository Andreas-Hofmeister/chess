From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.
From CHESS Require Export rook_moves.
From CHESS Require Export bishop_moves.

Inductive QueenCanMakeMove (pos : Position)
: SquareLocation -> Move -> Prop :=
  | QueenCanMoveLikeRook : forall from move,
    RookCanMakeMove pos from move -> QueenCanMakeMove pos from move
  | QueenCanMoveLikeBishop : forall from move,
    BishopCanMakeMove pos from move -> QueenCanMakeMove pos from move.

Definition queen_moves (l : SquareLocation) (pos : Position) : (list Move) :=
  (rook_moves l pos) ++ (bishop_moves l pos).

(*****Proofs*****)

Lemma queen_moves_sound : forall move fromL pos,
  location_valid fromL ->
  In move (queen_moves fromL pos) -> QueenCanMakeMove pos fromL move.
Proof.
  intros move fromL pos Hv Hin.
  unfold queen_moves in *. in_app_to_or. destruct Hin as [Hin | Hin].
  - apply QueenCanMoveLikeRook. apply rook_moves_sound; auto.
  - apply QueenCanMoveLikeBishop. apply bishop_moves_sound; auto.
Qed.

Lemma queen_moves_complete : forall pos fromL move,
  QueenCanMakeMove pos fromL move -> In move (queen_moves fromL pos).
Proof.
  intros pos fromL move Hcan.
  unfold queen_moves. in_app_to_or. inversion Hcan; subst.
  - left. apply rook_moves_complete. auto.
  - right. apply bishop_moves_complete. auto.
Qed.
