Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.

Inductive RookCanMakeMove (pos : Position)
: SquareLocation -> Move -> Prop :=
  | RookCanMove : forall pp c dstep from to, 
    location_valid from -> location_valid to ->
    pos = Posn pp c dstep ->
    from <> to ->
    SquaresOnSameFile from to \/ SquaresOnSameRank from to ->
    SquaresBetweenEmpty pp from to ->
    is_square_empty to pp = true ->
    RookCanMakeMove pos from (FromTo from to)
  | RookCanCapture : forall pp c dstep from to,
    location_valid from -> location_valid to -> 
    pos = Posn pp c dstep ->
    from <> to ->
    SquaresOnSameFile from to \/ SquaresOnSameRank from to ->
    SquaresBetweenEmpty pp from to ->
    is_square_occupied_by_enemy_piece to pp c = true ->
    RookCanMakeMove pos from (Capture from to).

Definition rook_moves (l : SquareLocation) (pos : Position) : (list Move) :=
  (append_forall (moves_to_square_on_rfd_list pos l)
    (squares_on_same_rank l)) ++
  (append_forall (moves_to_square_on_rfd_list pos l)
    (squares_on_same_file l)).

Lemma rook_move_to_square_on_same_rank_or_file_sound : forall pos fromL toL m,
  location_valid fromL -> location_valid toL ->
  SquaresOnSameFile fromL toL \/ SquaresOnSameRank fromL toL ->
  move_to_square_on_rfd pos fromL toL = Some m ->
  RookCanMakeMove pos fromL m.
Proof.
  intros pos fromL toL m Hfromv Htov Hsamerf Hrmts.
  destruct pos eqn:Epos. destruct fromL eqn:Efrom. destruct toL eqn:Eto.
  subst. simpl in Hrmts.
  destruct ((rank =? rank0) && (file =? file0))%bool eqn:EfromNotTo;
  simpl in Hrmts; try discriminate.
  destruct (are_squares_between_empty pp (Loc rank file) (Loc rank0 file0))
    eqn:Eempty; simpl in Hrmts; try discriminate.
  destruct (is_square_empty_rank_file rank0 file0 pp) eqn:Htoempty.
  - inversion Hrmts. subst. apply (RookCanMove _ pp toMove pawnDoubleStep _ _); 
    auto. intros C. inversion C; subst. Hb2p.
    repeat rewrite PeanoNat.Nat.eqb_refl in EfromNotTo.
    destruct EfromNotTo as [C1 | C1]; discriminate.
    apply are_squares_between_empty_correct. auto. auto. auto.
  - destruct (occupied_by_enemy_piece rank0 file0 pp toMove) eqn:Eoccupied;
    simpl in Hrmts; try discriminate.
    inversion Hrmts. subst. 
    apply (RookCanCapture _ pp toMove pawnDoubleStep _ _); auto. intros C. 
    inversion C; subst. Hb2p. 
    repeat rewrite PeanoNat.Nat.eqb_refl in EfromNotTo.
    destruct EfromNotTo as [C1 | C1]; discriminate.
    apply are_squares_between_empty_correct. auto. auto. auto.
Qed.

Lemma rook_move_to_square_on_same_rank_or_file_complete : 
  forall pos fromL toL m,
  RookCanMakeMove pos fromL m ->
  (m = (FromTo fromL toL) \/ m = (Capture fromL toL)) ->
  move_to_square_on_rfd pos fromL toL = Some m.
Proof.
  intros pos fromL toL m Hcan Hmove.
  inversion Hcan; subst.
  - assert (Hto: to = toL). 
    { destruct Hmove as [Hmove | Hmove]; inversion Hmove; subst; auto. }
    subst.
    simpl. destruct (eqSL fromL toL) eqn:Enotsame.
    + rewrite eqSL_iff in Enotsame. exfalso. apply H2. auto.
    + simpl. rewrite are_squares_between_empty_correct in H4. rewrite H4.
      rewrite H5. auto. auto. auto.
  - assert (Hto: to = toL). 
    { destruct Hmove as [Hmove | Hmove]; inversion Hmove; subst; auto. }
    subst.
    simpl. destruct (eqSL fromL toL) eqn:Enotsame.
    + rewrite eqSL_iff in Enotsame. exfalso. apply H2. auto.
    + simpl. rewrite are_squares_between_empty_correct in H4. rewrite H4.
      rewrite H5. auto. rewrite (occupied_not_empty toL pp c H5). auto. auto.
      auto.
Qed.

Lemma rook_moves_to_square_on_same_rank_or_file_list_complete : 
  forall pos fromL toL m,
  RookCanMakeMove pos fromL m ->
  (m = (FromTo fromL toL) \/ m = (Capture fromL toL)) ->
  In m (moves_to_square_on_rfd_list pos fromL toL).
Proof.
  intros pos fromL toL m Hcan Hmovetype.
  unfold moves_to_square_on_rfd_list.
  destruct (move_to_square_on_rfd pos fromL toL) eqn:Erm.
  - constructor. 
    apply rook_move_to_square_on_same_rank_or_file_complete with (toL:=toL) 
      in Hcan; auto.
    rewrite Hcan in Erm. inversion Erm. auto.
  - apply rook_move_to_square_on_same_rank_or_file_complete with (toL:=toL) 
      in Hcan; auto. rewrite Hcan in Erm. inversion Erm.
Qed.

Lemma rook_moves_to_square_on_same_rank_or_file_list_sound : 
  forall pos fromL toL m,
  location_valid fromL -> location_valid toL ->
  SquaresOnSameFile fromL toL \/ SquaresOnSameRank fromL toL -> 
  In m (moves_to_square_on_rfd_list pos fromL toL) ->
  RookCanMakeMove pos fromL m.
Proof.
  intros. unfold moves_to_square_on_rfd_list in *.
  destruct (move_to_square_on_rfd pos fromL toL) eqn:Hrm; inversion H2; 
  try inversion H3. subst. 
  eapply rook_move_to_square_on_same_rank_or_file_sound; eauto.
Qed.

Lemma rook_moves_sound : forall move fromL pos,
  location_valid fromL ->
  In move (rook_moves fromL pos) -> RookCanMakeMove pos fromL move.
Proof.
  intros move fromL pos Hvalid Hin.
  unfold rook_moves in Hin. in_app_to_or. destruct Hin as [Hin | Hin];
  apply in_append_forall_suf in Hin as [a [Hnk Hrm]];
  apply rook_moves_to_square_on_same_rank_or_file_list_sound in Hrm; auto.
  - eapply squares_on_same_rank_valid; eauto. 
  - right. apply squares_on_same_rank_sound. auto.
  - eapply squares_on_same_file_valid; eauto. 
  - left. apply squares_on_same_file_sound. auto.
Qed.

Lemma rook_moves_complete : forall pos fromL move,
  RookCanMakeMove pos fromL move -> In move (rook_moves fromL pos).
Proof.
  intros pos fromL move Hcan.
  inversion Hcan; subst.
  - unfold rook_moves. in_app_to_or. destruct H3 as [Hsamefile | Hsamerank].
    + right. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_file_complete; auto.
      * apply rook_moves_to_square_on_same_rank_or_file_list_complete; auto.
    + left. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_rank_complete; auto.
      * apply rook_moves_to_square_on_same_rank_or_file_list_complete; auto.
  - unfold rook_moves. in_app_to_or. destruct H3 as [Hsamefile | Hsamerank].
    + right. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_file_complete; auto.
      * apply rook_moves_to_square_on_same_rank_or_file_list_complete; auto.
    + left. apply in_append_forall_nec with (a:=to).
      * apply squares_on_same_rank_complete; auto.
      * apply rook_moves_to_square_on_same_rank_or_file_list_complete; auto.
Qed.


