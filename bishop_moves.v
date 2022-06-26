Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.

Inductive BishopCanMakeMove (pos : Position)
: SquareLocation -> Color -> Move -> Prop :=
  | BishopCanMove : forall pp c pos_c dstep cavl from to, 
    location_valid from -> location_valid to ->
    pos = Posn pp pos_c dstep cavl ->
    from <> to ->
    are_squares_on_same_diagonal from to = true \/ 
    are_squares_on_same_antidiagonal from to = true ->
    SquaresBetweenEmpty pp from to ->
    is_square_empty to pp = true ->
    BishopCanMakeMove pos from c (FromTo from to)
  | BishopCanCapture : forall pp c pos_c dstep cavl from to,
    location_valid from -> location_valid to -> 
    pos = Posn pp pos_c dstep cavl ->
    from <> to ->
    are_squares_on_same_diagonal from to = true \/ 
    are_squares_on_same_antidiagonal from to = true ->
    SquaresBetweenEmpty pp from to ->
    is_square_occupied_by_enemy_piece to pp c = true ->
    BishopCanMakeMove pos from c (Capture from to).

Definition bishop_moves (l : SquareLocation) (c : Color) (pos : Position) 
: (list Move) :=
  (append_forall (moves_to_square_on_rfd_list pos c l)
    (squares_on_same_diagonal l)) ++
  (append_forall (moves_to_square_on_rfd_list pos c l)
    (squares_on_same_antidiagonal l)).

(******Proofs*****)

Lemma bishop_moves_from : forall l c pos move,
  In move (bishop_moves l c pos) -> fromOfMove move = l.
Proof.
  intros l c pos move Hin. unfold bishop_moves in *. repeat in_app_to_or;
  apply in_append_forall_suf in Hin; destruct Hin as [a [Hd Hin]];
  eapply moves_to_square_on_rfd_list_from; eauto.
Qed.

Lemma bishop_move_to_square_on_same_diagonal_sound : forall pos c fromL toL m,
  location_valid fromL -> location_valid toL ->
  are_squares_on_same_diagonal fromL toL = true \/   
  are_squares_on_same_antidiagonal fromL toL = true ->
  move_to_square_on_rfd pos c fromL toL = Some m ->
  BishopCanMakeMove pos fromL c m.
Proof.
  intros pos c fromL toL m Hfromv Htov Hsamed Hmts.
  destruct pos eqn:Epos. destruct fromL eqn:Efrom. destruct toL eqn:Eto.
  subst. simpl in Hmts.
  destruct ((rank =? rank0) && (file =? file0))%bool eqn:EfromNotTo;
  simpl in Hmts; try discriminate.
  destruct (are_squares_between_empty pp (Loc rank file) (Loc rank0 file0))
    eqn:Eempty; simpl in Hmts; try discriminate.
  destruct (is_square_empty_rank_file rank0 file0 pp) eqn:Htoempty.
  - inversion Hmts. subst. 
    apply (BishopCanMove _ pp c toMove pawnDoubleStep castlingAvailabilities _ _); 
    auto. intros C. inversion C; subst. Hb2p.
    repeat rewrite PeanoNat.Nat.eqb_refl in EfromNotTo.
    destruct EfromNotTo as [C1 | C1]; discriminate.
    apply are_squares_between_empty_correct; auto.
  - destruct (occupied_by_enemy_piece rank0 file0 pp c) eqn:Eoccupied;
    simpl in Hmts; try discriminate.
    inversion Hmts. subst. 
    apply (BishopCanCapture _ pp c toMove pawnDoubleStep castlingAvailabilities _ _); 
    auto. intros C. inversion C; subst. Hb2p. 
    repeat rewrite PeanoNat.Nat.eqb_refl in EfromNotTo.
    destruct EfromNotTo as [C1 | C1]; discriminate.
    apply are_squares_between_empty_correct; auto.
Qed.

Lemma bishop_move_to_square_on_same_diagonal_complete : 
  forall pos fromL c toL m,
  BishopCanMakeMove pos fromL c m ->
  (m = (FromTo fromL toL) \/ m = (Capture fromL toL)) ->
  move_to_square_on_rfd pos c fromL toL = Some m.
Proof.
  intros pos fromL c toL m Hcan Hmove.
  inversion Hcan; subst.
  - assert (Hto: to = toL). 
    { destruct Hmove as [Hmove | Hmove]; inversion Hmove; subst; auto. }
    subst.
    simpl. destruct (eqSL fromL toL) eqn:Enotsame.
    + rewrite eqSL_iff in Enotsame. exfalso. apply H2. auto.
    + simpl. rewrite are_squares_between_empty_correct in H4. rewrite H4.
      rewrite H5; auto. auto. auto.
  - assert (Hto: to = toL). 
    { destruct Hmove as [Hmove | Hmove]; inversion Hmove; subst; auto. }
    subst.
    simpl. destruct (eqSL fromL toL) eqn:Enotsame.
    + rewrite eqSL_iff in Enotsame. exfalso. apply H2. auto.
    + simpl. rewrite are_squares_between_empty_correct in H4. rewrite H4.
      rewrite H5. auto. rewrite (occupied_not_empty toL pp c H5). auto. auto.
      auto.
Qed.

Lemma bishop_moves_to_square_on_same_diagonal_complete : 
  forall pos c fromL toL m,
  BishopCanMakeMove pos fromL c m ->
  (m = (FromTo fromL toL) \/ m = (Capture fromL toL)) ->
  In m (moves_to_square_on_rfd_list pos c fromL toL).
Proof.
  intros pos c fromL toL m Hcan Hmovetype.
  unfold moves_to_square_on_rfd_list.
  destruct (move_to_square_on_rfd pos c fromL toL) eqn:Erm.
  - constructor. 
    apply bishop_move_to_square_on_same_diagonal_complete with (toL:=toL) 
      in Hcan; auto.
    rewrite Hcan in Erm. inversion Erm. auto.
  - apply bishop_move_to_square_on_same_diagonal_complete with (toL:=toL) 
      in Hcan; auto. rewrite Hcan in Erm. inversion Erm.
Qed.

Lemma bishop_moves_to_square_on_same_diagonal_list_sound : 
  forall pos c fromL toL m,
  location_valid fromL -> location_valid toL ->
  are_squares_on_same_diagonal fromL toL = true \/   
  are_squares_on_same_antidiagonal fromL toL = true ->
  In m (moves_to_square_on_rfd_list pos c fromL toL) ->
  BishopCanMakeMove pos fromL c m.
Proof.
  intros. unfold moves_to_square_on_rfd_list in *.
  destruct (move_to_square_on_rfd pos c fromL toL) eqn:Hrm; inversion H2; 
  try inversion H3. subst. 
  eapply bishop_move_to_square_on_same_diagonal_sound; eauto.
Qed.

Lemma bishop_moves_sound : forall move fromL c pos,
  location_valid fromL ->
  In move (bishop_moves fromL c pos) -> BishopCanMakeMove pos fromL c move.
Proof.
  intros move fromL c pos Hvalid Hin.
  unfold bishop_moves in Hin. in_app_to_or. destruct Hin as [Hin | Hin];
  apply in_append_forall_suf in Hin as [a [Hd Hm]];
  apply bishop_moves_to_square_on_same_diagonal_list_sound in Hm; auto.
  - eapply squares_on_same_diagonal_valid; eauto.
  - left. apply squares_on_same_diagonal_sound. auto.
  - eapply squares_on_same_antidiagonal_valid; eauto. 
  - right. apply squares_on_same_antidiagonal_sound. auto.
Qed.

Lemma bishop_moves_complete : forall pos fromL c move,
  BishopCanMakeMove pos fromL c move -> In move (bishop_moves fromL c pos).
Proof.
  intros pos fromL c move Hcan.
  inversion Hcan; subst.
  - unfold bishop_moves. in_app_to_or. destruct H3 as [Hd | Had].
    + left. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_diagonal_complete; auto.
      * apply bishop_moves_to_square_on_same_diagonal_complete; auto.
    + right. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_antidiagonal_complete; auto.
      * apply bishop_moves_to_square_on_same_diagonal_complete; auto.
  - unfold bishop_moves. in_app_to_or. destruct H3 as [Hd | Had].
    + left. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_diagonal_complete; auto.
      * apply bishop_moves_to_square_on_same_diagonal_complete; auto.
    + right. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_antidiagonal_complete; auto.
      * apply bishop_moves_to_square_on_same_diagonal_complete; auto.
Qed.
