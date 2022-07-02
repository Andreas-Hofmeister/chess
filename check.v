Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
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
  (fun king_loc => (attacks_occupied_square pos (opponent_of c) king_loc)).

(** Proofs **)

Lemma find_king_correct : forall pos c king_rank king_file,
  In (Loc king_rank king_file) (find_king pos c) <-> 
  (location_valid (Loc king_rank king_file)) /\
  (get_square_by_index (get_piece_placements pos) king_rank king_file = 
  Occupied c King).
Proof.
  intros pos c king_rank king_file. split.
  - unfold find_king. intros H. apply find_piece_correct in H. HdAnd. split; 
    auto. apply valid_squares_suf in H. auto.
  - unfold find_king. intros H. HdAnd. apply valid_squares_nec in H. 
    apply find_piece_correct. split; auto.
Qed.

Lemma is_in_check_sound : forall pos c,
  is_in_check pos c = true -> IsInCheck pos c.
Proof.
  intros pos c. unfold is_in_check. intros H. rewrite exists_in_iff in *.
  destruct H as [loc [Hinkp Hattacked]]. destruct loc eqn:?E.
  destruct pos eqn:?E. subst. rewrite find_king_correct in *. HdAnd. 
  simpl in Hinkp0. eapply IsInCheckIff; eauto. 
  apply attacks_occupied_square_correct. auto.
Qed.

Lemma is_in_check_complete : forall pos c,
  IsInCheck pos c -> is_in_check pos c = true.
Proof.
  intros pos c. unfold is_in_check. intros H. rewrite exists_in_iff.
  inversion H. subst. inversion H2. subst. exists (Loc king_rank king_file).
  split.
  - rewrite find_king_correct. split; auto. rewrite H0. 
    eapply a_piece_can_make_move_to_valid; eauto.
  - apply attacks_occupied_square_correct. auto.
Qed.
