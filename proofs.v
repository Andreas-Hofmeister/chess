Require Import List.
Require Import Nat.
From Coq Require Export Lia.
From CHESS Require Export proof_tactics.
From CHESS Require Export chess.

Lemma eq_Loc : forall rank file rank1 file1, 
  rank = rank1 -> file = file1 -> Loc rank file = Loc rank1 file1.
Proof.
  intros. subst. auto.
Qed.

Definition location_valid (loc : SquareLocation) : Prop :=
  match loc with
  | Loc r f => r <= 7 /\ f <= 7
  end.

Lemma location_valid_iff : forall r f,
  location_valid (Loc r f) <-> indices_valid r f = true.
Proof.
  intros. unfold indices_valid. unfold file_index_valid. 
  unfold rank_index_valid. rewrite Bool.andb_true_iff.
  repeat rewrite PeanoNat.Nat.leb_le.
  split; intros.
  - inversion H. lia.
  - constructor. all: lia.
Qed.

Inductive PawnCanMakeMove (pos : Position)
: SquareLocation -> Move -> Prop :=
  | PawnCanMoveForward : forall pp c dstep loc sf sr tr,
    pos = Posn pp c dstep -> loc = Loc sr sf ->
    tr = advance_pawn c sr ->
    location_valid loc -> location_valid (Loc tr sf) ->
    get_square_by_index pp tr sf = Empty -> 
    PawnCanMakeMove pos loc (FromTo loc (Loc tr sf))
  | PawnCanCaptureDiagonallyForward : forall pp c dstep loc sf sr tf tr tc p,
    pos = Posn pp c dstep -> loc = Loc sr sf ->
    tr = advance_pawn c sr ->
    (tf = sf + 1 \/ tf = sf - 1) ->
    location_valid loc -> location_valid (Loc tr tf) ->
    get_square_by_index pp tr tf = Occupied tc p -> tc <> c -> 
    PawnCanMakeMove pos loc (Capture loc (Loc tr tf))
  | PawnCanDoubleStep : forall pp c dstep loc sf sr step1r tr,
    pos = Posn pp c dstep -> loc = Loc sr sf ->
    location_valid loc ->
    sr = starting_rank_of_pawn c ->
    step1r = advance_pawn c sr ->
    tr = advance_pawn c step1r ->
    get_square_by_index pp step1r sf = Empty ->
    get_square_by_index pp tr sf = Empty ->
    PawnCanMakeMove pos loc (DoubleStep loc (Loc tr sf))
  | PawnCanCaptureEnPassant : forall pp c dstep loc dstf sf sr tr,
    pos = Posn pp c (Some dstep) -> loc = Loc sr sf ->
    location_valid loc ->
    dstep = (DoubleStepRankFile sr dstf) ->
    (sf = dstf + 1 \/ sf = dstf - 1) ->
    tr = advance_pawn c sr ->
    PawnCanMakeMove pos loc (EnPassant loc (Loc tr dstf)).

Lemma is_square_empty_rank_file_correct : forall r f pp,
  is_square_empty_rank_file r f pp = true <-> (get_square_by_index pp r f) = Empty.
Proof.
  intros. 
  split.
  - intros. unfold is_square_empty_rank_file in *. 
    destruct (get_square_by_index pp r f) eqn:Egs; auto. discriminate.
  - intros. unfold is_square_empty_rank_file in *. 
    destruct (get_square_by_index pp r f) eqn:Egs; auto. discriminate.
Qed.

Lemma pawn_forward_moves_sound : forall move loc pos,
  In move (pawn_forward_moves loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. 
  simpl in H. unfold pawn_forward_moves in H.
  destruct pos eqn:Epos. destruct loc eqn:Eloc.
  destruct (indices_valid (advance_pawn toMove rank) file) eqn:Eiv; 
    try rewrite Bool.andb_false_r in H; simpl in H; try contradiction.
  destruct (indices_valid rank file) eqn:Eiv2; try simpl in H; 
    try contradiction.
  destruct (is_square_empty_rank_file (advance_pawn toMove rank) file pp) eqn:Eempty;
    try simpl in H; try contradiction.
  destruct H as [H | W]; try contradiction.
  subst. rewrite <- location_valid_iff in *. 
  rewrite is_square_empty_rank_file_correct in *.
  eapply PawnCanMoveForward; auto.
Qed.

Lemma ceq_eq : forall c1 c2, ceq c1 c2 = true <-> (c1 = c2).
Proof.
  intros. split.
  - intros. destruct c1; destruct c2; auto; try simpl in H; try discriminate.
  - intros. rewrite H. destruct c2; simpl; auto.
Qed.

Lemma occupied_by_enemy_piece_correct : forall f r pp c,
  occupied_by_enemy_piece r f pp c = true <-> exists c2 piece,
  (indices_valid r f = true) /\ 
  (get_square_by_index pp r f) = Occupied c2 piece /\ c2 <> c.
Proof.
  intros. split.
  - intros. 
    unfold occupied_by_enemy_piece in H.
    destruct (indices_valid r f); simpl in H; try discriminate.
    destruct (get_square_by_index pp r f); try discriminate.
    destruct (ceq c0 c) eqn:Eceq; try discriminate. auto.
    exists c0. exists p.
    repeat split; auto. intros C. rewrite <- ceq_eq in C. rewrite C in Eceq.
    discriminate.
  - intros. destruct H as [c2 [piece [Hiv [Hoc Henemy]]]].
    unfold occupied_by_enemy_piece. rewrite Hiv. rewrite Hoc.
    destruct (ceq c2 c) eqn:Eceq; auto; try rewrite ceq_eq in Eceq; 
    try contradiction.
Qed.

Lemma pawn_captures_sound : forall move loc pos,
  In move (pawn_captures loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. 
  simpl in H. unfold pawn_captures in H.
  destruct pos eqn:Epos. destruct loc eqn:Eloc.
  destruct (indices_valid rank file) eqn:Hivsrc; try inversion H.
  rewrite <- location_valid_iff in *.
  Ltac tac1 :=
    match goal with
    | H: In _ (if occupied_by_enemy_piece ?r ?f ?pp ?c then _ else _) |- _
          => destruct (occupied_by_enemy_piece r f pp c) eqn: Eoc
    end;
    try inversion H; try inversion H0;
    match goal with
    | H: (occupied_by_enemy_piece ?r ?f ?pp ?c = _) |- _ 
          => apply occupied_by_enemy_piece_correct in H; 
             destruct H as [c2 [piece [Hiv [Hoc Henemy]]]]
    end;
    subst; try rewrite <- location_valid_iff in *; 
    eapply PawnCanCaptureDiagonallyForward; simpl; eauto.
  apply in_app_or in H. destruct H as [H | H]; tac1.
Qed.

Lemma pawn_double_steps_sound : forall move loc pos,
  In move (pawn_double_steps loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros.
  simpl in H. unfold pawn_double_steps in H.
  destruct pos eqn:Epos. destruct loc eqn:Eloc.
  Ltac tac2 := match goal with
  | H : In _ (if ?c then _ else _) |- _ => destruct c eqn:?H
  | H : In _ [] |- _ => inversion H
  end.
  repeat tac2. rewrite <- location_valid_iff in *.
  rewrite Bool.andb_true_iff in *. repeat rewrite is_square_empty_rank_file_correct in *.
  inversion H; inversion H3. subst. destruct H2 as [Hempty1 Hempty2].
  rewrite PeanoNat.Nat.eqb_eq in H1. eapply PawnCanDoubleStep; eauto.
Qed.

Lemma en_passant_moves_sound : forall move loc pos,
  In move (en_passant_moves loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. unfold en_passant_moves in H.
  destruct loc eqn:Eloc.
  repeat tac2.
  destruct pos eqn:Epos.
  destruct pawnDoubleStep eqn:Edstep; try inversion H.
  destruct p eqn:Ep.
  repeat tac2.
  rewrite PeanoNat.Nat.eqb_eq in H1.
  inversion H; inversion H3.
  rewrite Bool.orb_true_iff in H2. repeat rewrite PeanoNat.Nat.eqb_eq in H2.
  rewrite <- location_valid_iff in *.
  simpl. eapply PawnCanCaptureEnPassant; simpl; eauto; simpl; try lia.
Qed.

Lemma pawn_moves_sound : forall move loc pos,
  In move (pawn_moves loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. unfold pawn_moves in H.
  Ltac in_app_to_or := match goal with
  | H : In _ (_ ++ _) |- _ => apply in_app_or in H
  | H : In _ _ \/ In _ _ |- _ => destruct H as [H | H]
  end.
  repeat in_app_to_or.
  - apply pawn_forward_moves_sound. auto.
  - apply pawn_captures_sound. auto.
  - apply pawn_double_steps_sound. auto.
  - apply en_passant_moves_sound. auto.
Qed.

Lemma pawn_moves_complete : forall move loc pos,
  PawnCanMakeMove pos loc move -> In move (pawn_moves loc pos).
Proof.
  intros.
  Ltac if_cond_destruct_in_goal := match goal with
  | |- In _ (if ?c then _ else _) => destruct c eqn:?H
  end.
  inversion H; subst; unfold pawn_moves.
  - rewrite in_app_iff. left. simpl.
    rewrite location_valid_iff in *. rewrite H3. rewrite H4. simpl.
    rewrite <- is_square_empty_rank_file_correct in *. rewrite H5. constructor. auto.
  - rewrite in_app_iff. right. rewrite in_app_iff. left.
    rewrite location_valid_iff in *. 
    simpl. rewrite H4. destruct H3 as [Hr | Hl].
    + rewrite in_app_iff. right. subst. if_cond_destruct_in_goal.
      * constructor. auto.
      * rewrite <- Bool.not_true_iff_false in H0. exfalso. apply H0. 
        apply occupied_by_enemy_piece_correct. eexists. eexists. eauto.
    + rewrite in_app_iff. left. subst. if_cond_destruct_in_goal.
      * constructor. auto.
      * rewrite <- Bool.not_true_iff_false in H0. exfalso. apply H0. 
        apply occupied_by_enemy_piece_correct. eexists. eexists. eauto.
  - rewrite in_app_iff. right. rewrite in_app_iff. right. rewrite in_app_iff.
    left.
    simpl. rewrite location_valid_iff in *. rewrite H2.
    rewrite PeanoNat.Nat.eqb_refl. rewrite <- is_square_empty_rank_file_correct in *.
    rewrite H6. rewrite H7. simpl. left. auto.
  - rewrite in_app_iff. right. rewrite in_app_iff. right. rewrite in_app_iff.
    right. simpl. rewrite location_valid_iff in *. rewrite H2. 
    rewrite PeanoNat.Nat.eqb_refl. 
    destruct ((dstf =? sf + 1) || (dstf =? sf - 1))%bool eqn:Edstf.
    + constructor. auto.
    + rewrite Bool.orb_false_iff in Edstf. 
      repeat rewrite PeanoNat.Nat.eqb_neq in Edstf. lia.
Qed.

Lemma difference_n_n: forall n, difference n n = 0.
Proof.
  intros. unfold difference. destruct (n <? n); lia.
Qed.

Lemma difference_n_nm1: forall n, difference n (n - 1) <= 1.
Proof.
  intros. unfold difference. destruct (n <? n - 1); lia.
Qed.

Lemma difference_n_np1: forall n, difference n (n + 1) <= 1.
Proof.
  intros. unfold difference. destruct (n <? n + 1); lia.
Qed.

Lemma difference_nm1_n: forall n, difference (n - 1) n <= 1.
Proof.
  intros. unfold difference. destruct (n - 1 <? n); lia.
Qed.

Lemma difference_np1_n: forall n, difference (n + 1) n <= 1.
Proof.
  intros. unfold difference. destruct (n + 1 <? n); lia.
Qed.

Definition SquaresAdjacent (loc1 : SquareLocation) (loc2 : SquareLocation)
  : Prop :=
  match loc1 with
  | Loc rank1 file1 => 
    match loc2 with
    | Loc rank2 file2 => 
      (difference rank1 rank2) <= 1 /\ (difference file1 file2) <= 1
    end
  end.

Lemma are_squares_adjacent_correct : forall loc1 loc2,
  are_squares_adjacent loc1 loc2 = true <-> SquaresAdjacent loc1 loc2.
Proof.
  intros. split.
  - intros. unfold are_squares_adjacent in H. destruct loc1 eqn:Eloc1.
    destruct loc2 eqn:Eloc2. rewrite Bool.andb_true_iff in H.
    repeat rewrite PeanoNat.Nat.leb_le in H. constructor; lia.
  - intros. unfold SquaresAdjacent in H. destruct loc1 eqn:Eloc1.
    destruct loc2 eqn:Eloc2. repeat rewrite <- PeanoNat.Nat.leb_le in H. 
    rewrite <- Bool.andb_true_iff in H. auto.
Qed.

Lemma Sn_lt_Snp1 : forall n, S n <? S (n + 1) = true.
Proof.
  intros. rewrite PeanoNat.Nat.ltb_lt. lia.
Qed.

Lemma Sn_lt_n : forall n, S n <? n = false.
Proof.
  intros. destruct (S n <? n) eqn:Es; auto. rewrite PeanoNat.Nat.ltb_lt in *. 
  lia.
Qed.

Lemma n_lt_nm1 : forall n, n <? n - 1 = false.
Proof.
  intros. destruct (n <? n - 1) eqn:Es; auto. rewrite PeanoNat.Nat.ltb_lt in *. 
  lia.
Qed.

Lemma n_lt_np1 : forall n, n <? n + 1 = true.
Proof.
  intros. rewrite PeanoNat.Nat.ltb_lt in *. lia.
Qed.

Lemma one_step_along_vector_adjacent : forall l l2 v,
  l2 = (one_step_along_vector l v) -> l = l2 \/ SquaresAdjacent l l2.
Proof.
  Ltac split_and_differences := match goal with
  | |- difference _ _ <= 1 /\ difference _ _ <= 1 => split
  | |- difference ?x ?x <= 1 => rewrite difference_n_n; lia
  | |- difference ?x (?x - 1) <= 1 => apply difference_n_nm1
  | |- difference ?x (?x + 1) <= 1 => apply difference_n_np1
  end.
  intros. unfold one_step_along_vector in *.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehs.
  destruct d eqn:Ed; destruct n eqn:En; destruct vstep eqn:Evs;
  destruct d0 eqn:Ed0; destruct n0 eqn:En0; auto; right; simpl; rewrite H;
  repeat split_and_differences; destruct n1 eqn:En1; repeat split_and_differences.
Qed.

Inductive SquaresBetweenEmpty (pp : PiecePlacements)
  : SquareLocation -> SquareLocation -> Prop :=
  | NothingOccupiedBetweenAdjacentSquares : forall loc1 loc2, 
    SquaresAdjacent loc1 loc2 -> SquaresBetweenEmpty pp loc1 loc2
  | NothingOccupiedBetweenSingleSquare : forall loc,
    SquaresBetweenEmpty pp loc loc
  | SquaresAlongVectorEmpty : forall loc1 loc2 v first_step,
    vector_from_a_to_b loc1 loc2 = v ->
    (one_step_along_vector loc1 v) = first_step ->
    is_square_empty first_step pp = true ->
    SquaresBetweenEmpty pp first_step loc2 ->
    SquaresBetweenEmpty pp loc1 loc2.

Lemma one_step_along_vector_and_location_adjacent : forall l v l1 v1,
  one_step_along_vector_and_location l v = (v1, l1) -> 
  l = l1 \/ SquaresAdjacent l l1.
Proof.
  intros. unfold one_step_along_vector_and_location in H. repeat Hdestruct;
  subst; inversion H; auto; right; split; unfold difference;
  repeat match goal with
  | |- (if ?x <? ?y then _ else _) <= _ => destruct (x <? y) eqn:?H; lia
  end.
Qed.

Lemma one_step_along_vector_and_location_shorter : forall l v v1 l1,
  vector_length v <> 0 ->
  one_step_along_vector_and_location l v = (v1,l1) -> 
  vector_length v1 < vector_length v.
Proof.
  intros.
  unfold one_step_along_vector_and_location in H0.
  destruct l eqn:El.
  destruct v eqn:Ev.
  repeat Hdestruct; inversion H0; subst; simpl in H; try lia; simpl; try lia.
Qed.

Lemma one_step_along_vector_and_location_diagonal : forall l v v1 l1,
  RankFileOrDiagonalVector v ->
  one_step_along_vector_and_location l v = (v1,l1) ->
  RankFileOrDiagonalVector v1.
Proof.
  intros. unfold one_step_along_vector_and_location in H0. 
  destruct l eqn:El. unfold RankFileOrDiagonalVector in H.
  destruct H as [HR | [HF | HD]].
  - inversion HR. subst. repeat Hdestruct; inversion H0; subst; left; 
    constructor.
  - inversion HF. subst. repeat Hdestruct; inversion H0; subst; right; left;
    constructor.
  - inversion HD. subst. repeat Hdestruct; inversion H0; subst; right; right;
    constructor.
Qed.

Lemma vector_length_0_iff : forall d1 n d2 m,
  vector_length (VectorHV (HStep d1 n) (VStep d2 m)) = 0 <-> (n = 0) /\ (m = 0).
Proof.
  intros. simpl. split; intros; lia.
Qed.

Lemma vector_length_not_0_iff : forall d1 n d2 m,
  vector_length (VectorHV (HStep d1 n) (VStep d2 m)) <> 0 <-> 
  (n > 0) \/ (m > 0).
Proof.
  intros. simpl. split; intros; lia.
Qed.

Lemma apply_null_vector : forall v l, 
  vector_length v = 0 -> apply_vector v l = l.
Proof.
  intros. unfold vector_length in H. repeat Hdestruct.
  assert (Hn_is_zero: n = 0). lia.
  assert (H_n0_is_zero: n0 = 0). lia.
  subst. simpl. destruct d0 eqn:Ed0; destruct d eqn:Ed; destruct l eqn:El;
  apply eq_Loc; try lia.
Qed.

Theorem strong_induction:
  forall P : nat -> Prop,
  (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
  forall n : nat, P n.
Proof.
  intros P H.
  assert (Hsi: forall n, forall k, k <= n -> P k).
  - induction n.
    + intros. assert (Hk: k = 0). lia. subst. apply H. intros. lia.
    + intros. destruct (k =? S n) eqn:Ek.
      * rewrite PeanoNat.Nat.eqb_eq in Ek. subst. apply H. intros. apply IHn.
        lia.
      * rewrite PeanoNat.Nat.eqb_neq in Ek. assert (Eklen: k <= n). lia.
        apply IHn. auto.
  - intros. apply Hsi with (n:=n). auto.
Qed. 

Lemma one_step_along_vector_and_location_correct: forall s v v1 s1,
  one_step_along_vector_and_location s v = (v1, s1) ->
  apply_vector v s = apply_vector v1 s1.
Proof.
  intros. unfold one_step_along_vector_and_location in H. repeat Hdestruct;
  inversion H; subst; try reflexivity; simpl; try apply eq_Loc; try lia.
Qed.

Lemma eq_VectorHV: forall dh1 n1 dv1 m1 dh2 n2 dv2 m2,
  dh1 = dh2 -> n1 = n2 -> dv1 = dv2 -> m1 = m2 ->
  VectorHV (HStep dh1 n1) (VStep dv1 m1) = VectorHV (HStep dh2 n2) (VStep dv2 m2).
Proof.
  intros. subst. auto.
Qed.

Lemma one_step_along_vector_and_location_last_step: forall s v v1 s1,
  one_step_along_vector_and_location s v = (v1, s1) ->
  vector_length v <> 0 -> vector_length v1 = 0 ->
  s1 = apply_vector v s.
Proof.
  intros. rewrite (one_step_along_vector_and_location_correct s v v1 s1); auto.
  rewrite apply_null_vector; auto.
Qed.

Definition vector_stays_within_boundaries (v : Vector) (l : SquareLocation) 
  : Prop :=
  match l with
  | Loc x y =>
    match v with
    | VectorHV (HStep Left n) (VStep Down m) => (n <= x) /\ (m <= y)
    | VectorHV (HStep Left n) (VStep Up _) => n <= x
    | VectorHV (HStep Right _) (VStep Down m) => m <= y
    | _ => True
    end
  end.

Lemma vector_from_a_to_b_preserves_diagonal : forall v start,
  vector_stays_within_boundaries v start ->
  RankFileOrDiagonalVector v -> 
  RankFileOrDiagonalVector (vector_from_a_to_b start (apply_vector v start)).
Proof.
  intros v start Hbounds Hvdiag. unfold vector_from_a_to_b.
  destruct start eqn:Estart.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl.
  Ltac simplify_calculations := try inversion Hr; try inversion Hf; 
    try inversion Hd; subst; repeat rewrite PeanoNat.Nat.add_0_r; 
    repeat rewrite PeanoNat.Nat.sub_0_r; repeat rewrite PeanoNat.Nat.sub_diag;
    repeat rewrite PeanoNat.Nat.leb_refl.
  Ltac finish1 := left; constructor.
  Ltac finish2 := right; left; constructor.
  Ltac finish3 := right; right; constructor.
  Ltac finish := try finish1; try finish2; try finish3.
  - simpl in Hbounds. destruct Hvdiag as [Hr | [Hf | Hd]];
    simplify_calculations; finish.
    inversion Hd. subst. replace (file <=? file + n0) with true; 
    try symmetry; try rewrite PeanoNat.Nat.leb_le; try lia. 
    replace (file + n0 - file) with n0; try lia.
    destruct rank eqn:Hrnk. simpl. right. left. constructor.
    destruct (S n <=? S n - n0) eqn:En.
    + replace (S n - n0 - S n) with 0; try lia. right. left. constructor.
    + rewrite PeanoNat.Nat.leb_gt in En. replace (S n - (S n - n0)) with n0; 
      try lia. right. right. constructor.
  - simpl in Hbounds. destruct Hbounds as [Hbounds1 Hbounds2].
    destruct Hvdiag as [Hr | [Hf | Hd]]; simplify_calculations; finish.
    destruct n0. simplify_calculations. finish.
    replace (rank <=? rank - S n0) with false; try symmetry; 
    try rewrite PeanoNat.Nat.leb_gt; try lia.
    replace (file <=? file - S n0) with false; try symmetry; 
    try rewrite PeanoNat.Nat.leb_gt; try lia.
    replace (rank - (rank - S n0)) with (S n0); try lia.
    replace (file - (file - S n0)) with (S n0); try lia. finish.
  - simpl in Hbounds. destruct Hvdiag as [Hr | [Hf | Hd]]; 
    simplify_calculations; finish.
    replace (rank <=? rank + n0) with true; try symmetry; 
    try rewrite PeanoNat.Nat.leb_le; try lia.
    replace (file <=? file + n0) with true; try symmetry; 
    try rewrite PeanoNat.Nat.leb_le; try lia.
    replace (rank + n0 - rank) with n0; try lia.
    replace (file + n0 - file) with n0; try lia. finish.
  - simpl in Hbounds. destruct Hvdiag as [Hr | [Hf | Hd]]; 
    simplify_calculations; finish.
    replace (rank <=? rank + n0) with true; try symmetry; 
    try rewrite PeanoNat.Nat.leb_le; try lia.
    destruct n0. simplify_calculations. finish.
    replace (file <=? file - S n0) with false; try symmetry; 
    try rewrite PeanoNat.Nat.leb_gt; try lia.
    replace (rank + S n0 - rank) with (S n0); try lia.
    replace (file - (file - S n0)) with (S n0); try lia. finish.
Qed.

Lemma vector_from_a_to_b_correct : forall l1 l2,
  apply_vector (vector_from_a_to_b l1 l2) l1 = l2.
Proof.
  intros l1 l2.
  destruct l1 eqn:El1.
  destruct l2 eqn:El2.
  simpl. destruct (file <=? file0) eqn:Efl.
  - Hb2p. destruct (rank <=? rank0) eqn:Ernk; Hb2p; simpl; apply eq_Loc; lia.
  - Hb2p. destruct (rank <=? rank0) eqn:Ernk; Hb2p; simpl; apply eq_Loc; lia.
Qed.

Lemma make_vector_stay_in_bounds_stays_in_bounds : forall v l,
  vector_stays_within_boundaries (make_vector_stay_in_bounds v l) l.
Proof.
  intros.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
  - apply PeanoNat.Nat.le_min_r.
  - split. apply PeanoNat.Nat.le_min_r. apply PeanoNat.Nat.le_min_r.
  - apply PeanoNat.Nat.le_min_r.
Qed.

Lemma one_step_stays_in_bounds : forall v l v0 l0,
  vector_stays_within_boundaries v l ->
  one_step_along_vector_and_location l v = (v0, l0) ->
  vector_stays_within_boundaries v0 l0.
Proof.
  intros v l v0 l0 Hbounds Hos.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; inversion Hos; subst; auto.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
Qed.

Lemma make_vector_stay_in_bounds_eq : forall v l,
  apply_vector v l = apply_vector (make_vector_stay_in_bounds v l) l.
Proof.
  intros.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
  - subst. apply eq_Loc; auto. lia.
  - subst. apply eq_Loc; auto; lia.
  - subst. apply eq_Loc; auto; lia.
Qed.

Lemma one_step_same : forall start v s v0,
  one_step_along_vector_and_location start v = (v0, s) ->
  one_step_along_vector start v = s.
Proof.
  intros start v s v0 Hosvl.
  destruct start eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; simpl in Hosvl; subst; auto;
  destruct n eqn:En; destruct n0 eqn:En0; inversion Hosvl; auto.
Qed.

Lemma one_step_apply_same : forall start v,
  one_step_along_vector start v =
  one_step_along_vector start (vector_from_a_to_b start 
    (apply_vector v start)).
Proof.
  intros. 
  destruct start eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
  - destruct n eqn:En.
    + simplify_calculations.
      replace (file <=? file + n0) with true; try symmetry; 
      try rewrite PeanoNat.Nat.leb_le; try lia.
      replace (file + n0 - file) with n0; try lia.
      destruct n0 eqn:En0; auto.
    + destruct n0 eqn:En0; simpl; destruct (rank <=? rank - S n1) eqn:Ernk.
      * rewrite PeanoNat.Nat.leb_le in Ernk.
        assert (Hrnk2: rank = 0). lia. subst. simpl.
        simplify_calculations. auto.
      * subst. rewrite PeanoNat.Nat.leb_gt in Ernk.
        destruct (rank - (rank - S n1)) eqn:Hrnk2; try lia.
        simplify_calculations. auto.
      * rewrite PeanoNat.Nat.leb_le in Ernk. 
        assert (Hrnk2: rank = 0). lia. subst. simpl. 
        replace (file <=? file + S n2) with true; try symmetry; 
        try rewrite PeanoNat.Nat.leb_le; try lia.
        replace (file + S n2 - file) with (S n2); try lia. auto.
      * subst. rewrite PeanoNat.Nat.leb_gt in Ernk.
        destruct (rank - (rank - S n1)) eqn:Hrnk2; try lia.
        replace (file <=? file + S n2) with true; try symmetry; 
        try rewrite PeanoNat.Nat.leb_le; try lia.
        replace (file + S n2 - file) with (S n2); try lia. auto.
  - destruct n eqn:En.
    + simplify_calculations. destruct n0 eqn:En0. simplify_calculations. auto.
      destruct (file <=? file - S n) eqn:Efl.
      * Hb2p. assert (Hfl2: file = 0). lia. rewrite Hfl2. simpl. auto.
      * Hb2p. destruct (file - (file - S n)) eqn:Efl2; try lia. auto.
    + destruct n0 eqn:En0.
      * simplify_calculations. destruct (rank <=? rank - S n1) eqn:Hrnk.
        -- Hb2p. assert (Hrnk2: rank = 0). lia. rewrite Hrnk2. simpl. auto.
        -- Hb2p. destruct (rank - (rank - S n1)) eqn:Ernk2; try lia. auto.
      * destruct (rank <=? rank - S n1) eqn:Hrnk.
        -- Hb2p. assert (Hrnk2: rank = 0). lia. rewrite Hrnk2. simpl.
           destruct (file <=? file - S n2) eqn:Hfl.
           ++ Hb2p. assert (Hfl2: file = 0). lia. rewrite Hfl2. simpl. auto.
           ++ Hb2p. destruct (file - (file - S n2)) eqn:Hfl2; try lia. auto.
        -- Hb2p. destruct (rank - (rank - S n1)) eqn:Hrnk2; try lia.
           destruct (file <=? file - S n2) eqn:Hfl.
           ++ Hb2p. assert (Hfl2: file = 0). lia. rewrite Hfl2. simpl. auto.
           ++ Hb2p. destruct (file - (file - S n2)) eqn:Hfl2; try lia. auto.
  - destruct n eqn:En.
    + simplify_calculations. destruct n0 eqn:En0. simplify_calculations. auto.
      replace (file <=? file + S n) with true; try Gb2p; try lia.
      replace (file + S n - file) with (S n); try lia. auto.
    + destruct n0 eqn:En0. 
      * simplify_calculations. auto.
        replace (rank <=? rank + S n1) with true; try Gb2p; try lia.
        replace (rank + S n1 - rank) with (S n1); try lia. auto.
      * replace (rank <=? rank + S n1) with true; try Gb2p; try lia.
        replace (rank + S n1 - rank) with (S n1); try lia. auto.
        replace (file <=? file + S n2) with true; try Gb2p; try lia.
        replace (file + S n2 - file) with (S n2); try lia. auto.
  - destruct n eqn:En.
    + simplify_calculations. destruct n0 eqn:En0. simplify_calculations. auto.
      destruct (file <=? file - S n) eqn:Hfl.
      * Hb2p. assert (Hfl2: file = 0). lia. rewrite Hfl2. simpl. auto.
      * Hb2p. destruct (file - (file - S n)) eqn:Hfl2; try lia. auto.
    + destruct n0 eqn:En0. 
      * simplify_calculations. auto.
        replace (rank <=? rank + S n1) with true; try Gb2p; try lia.
        replace (rank + S n1 - rank) with (S n1); try lia. auto.
      * replace (rank <=? rank + S n1) with true; try Gb2p; try lia.
        replace (rank + S n1 - rank) with (S n1); try lia. auto.
        destruct (file <=? file - S n2) eqn:Hfl.
        -- Hb2p. assert (Hfl2: file = 0). lia. rewrite Hfl2. simpl. auto.
        -- Hb2p. destruct (file - (file - S n2)) eqn:Hfl2; try lia. auto.
Qed.

Lemma are_squares_along_vector_empty_sound_aux : forall n,
  forall pp v start,
  n = vector_length v ->
  are_squares_along_vector_empty pp start v = true ->
  (vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))).
Proof.
  induction n using strong_induction.
  intros pp v start Hvlength Hemptyv. 
  rewrite are_squares_along_vector_empty_equation in Hemptyv. 
  destruct n eqn:En. left. auto.
  replace (vector_length v =? 0) with false in Hemptyv; try symmetry;
  try rewrite PeanoNat.Nat.eqb_neq; try lia.
  assert (Hvnot0: vector_length v <> 0). lia.
  right.
  destruct (one_step_along_vector_and_location start v) eqn:Eos.
  destruct (is_square_empty start pp) eqn:Eisempty; try discriminate.
  split; auto.
  assert (Hvlv0: vector_length v0 < S n0). { rewrite Hvlength.
    eapply one_step_along_vector_and_location_shorter; eauto.
  }
  assert (Hduh: vector_length v0 = vector_length v0). { auto. }
  specialize (H (vector_length v0) Hvlv0 pp v0 s Hduh Hemptyv) as Hind.
  destruct Hind as [Hind | Hind].
  - specialize (one_step_along_vector_and_location_last_step start v v0 s Eos 
      Hvnot0 Hind) as Hlaststep. subst.
    specialize (one_step_along_vector_and_location_adjacent _ _ _ _ Eos) 
      as Hadj.
    destruct Hadj as [Hequal | Hadj].
    + rewrite <- Hequal. apply NothingOccupiedBetweenSingleSquare.
    + constructor. auto.
  - eapply SquaresAlongVectorEmpty; eauto.
    + rewrite <- one_step_apply_same. replace (one_step_along_vector start v) with s.
      apply Hind. symmetry. apply (one_step_same start v s v0). auto.
    + rewrite <- one_step_apply_same. rewrite (one_step_same start v s v0); auto.
      erewrite one_step_along_vector_and_location_correct. apply Hind. auto.
Qed.

Lemma are_squares_along_vector_empty_sound : forall pp v start,
  are_squares_along_vector_empty pp start v = true ->
  (vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))).
Proof.
  intros.
  apply are_squares_along_vector_empty_sound_aux with (n:=vector_length v).
  auto. auto.
Qed.

Lemma one_step_along_short_vector : forall v l v0 l0,
  vector_stays_within_boundaries v l ->
  one_step_along_vector_and_location l v = (v0,l0) ->
  SquaresAdjacent l (apply_vector v l) ->
  vector_length v0 = 0.
Proof.
  intros v l v0 l0 Hbounds Hos Hadj.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
  - simpl in Hos. simpl in Hadj. Hdestruct; unfold difference in Hadj; 
    destruct Hadj as [Hadj1 Hadj2].
    + inversion Hos. subst. simpl. auto.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. lia.
    + HreplaceInIf. inversion Hos. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
  - simpl in Hos. simpl in Hadj. Hdestruct; destruct Hadj as [Hadj1 Hadj2];
    unfold difference in *.
    + inversion Hos. simpl. auto.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
  - simpl in Hos. simpl in Hadj. Hdestruct; destruct Hadj as [Hadj1 Hadj2];
    unfold difference in *.
    + inversion Hos. simpl. auto.
    + HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
  - simpl in Hos. simpl in Hadj. Hdestruct; destruct Hadj as [Hadj1 Hadj2];
    unfold difference in *.
    + inversion Hos. simpl. auto.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
Qed.

Lemma apply_vector_idem: forall v l,
  vector_stays_within_boundaries v l -> apply_vector v l = l -> 
  vector_length v = 0.
Proof.
  intros v l Hbounds Hidem.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto; subst;
  simpl in Hidem; simpl in Hbounds; inversion Hidem; lia.
Qed.

Lemma are_squares_along_vector_empty_complete_aux : forall n,
  forall pp v start,
  (vector_length v) = n ->
  vector_stays_within_boundaries v start ->
  ((vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))) ->
  are_squares_along_vector_empty pp start v = true).
Proof.
  induction n using strong_induction.
  intros pp v start Hvl Hbounds [Hv0 | [Hfstempty Hrestempty]]; 
  rewrite are_squares_along_vector_empty_equation. Hp2b. rewrite Hv0. auto.
  destruct (vector_length v =? 0) eqn:Evl; auto. Hb2p.
  destruct (one_step_along_vector_and_location start v) eqn:Eos.
  rewrite Hfstempty. apply H with (k:=vector_length v0). rewrite <- Hvl.
  eapply one_step_along_vector_and_location_shorter; eauto. auto.
  apply (one_step_stays_in_bounds v start v0 s Hbounds Eos).
  inversion Hrestempty.
  - subst. left. eapply one_step_along_short_vector; eauto.
  - exfalso. apply Evl. eapply apply_vector_idem; eauto.
  - assert (Hfst_s: first_step = s). { subst. rewrite <- one_step_apply_same.
      eapply one_step_same. apply Eos.
    }
    right. rewrite Hfst_s in H2. split; auto. rewrite Hfst_s in H3.
    rewrite <- (one_step_along_vector_and_location_correct _ _ _ _ Eos). auto.
Qed.

Lemma are_squares_along_vector_empty_complete : forall pp v start,
  vector_stays_within_boundaries v start ->
  ((vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))) ->
  are_squares_along_vector_empty pp start v = true).
Proof.
  intros.
  apply are_squares_along_vector_empty_complete_aux with (n:=vector_length v);
  auto.
Qed.

Lemma vector_from_a_to_b_in_bounds : forall l1 l2,
  vector_stays_within_boundaries (vector_from_a_to_b l1 l2) l1.
Proof.
  intros l1 l2.
  destruct l1 eqn:El1.
  destruct l2 eqn:El2.
  simpl. destruct (rank <=? rank0) eqn:Ernk.
  - destruct (file <=? file0) eqn:Efl; auto. lia.
  - destruct (file <=? file0) eqn:Efl; auto. lia. split; auto; lia.
Qed.

Lemma are_squares_along_vector_empty_correct : forall pp v start,
  vector_stays_within_boundaries v start ->
  ((vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))) <->
  are_squares_along_vector_empty pp start v = true).
Proof.
  intros. split.
  - apply are_squares_along_vector_empty_complete. auto.
  - apply are_squares_along_vector_empty_sound.
Qed.

Lemma vector_from_a_to_b_zero_iff : forall l1 l2, 
  vector_length (vector_from_a_to_b l1 l2) = 0 <-> l1 = l2.
Proof.
  intros l1 l2. split.
  - intros Hlen0. rewrite <- (vector_from_a_to_b_correct l1 l2).
    symmetry. apply apply_null_vector. auto.
  - intros Heq. rewrite Heq. destruct l2 eqn:El2. simpl.
    replace (rank <=? rank) with true; try Gb2p; try lia.
    replace (file <=? file) with true; try Gb2p; try lia.
Qed.

Lemma are_squares_between_empty_sound : forall pp l1 l2,
  are_squares_between_empty pp l1 l2 = true -> SquaresBetweenEmpty pp l1 l2.
Proof.
  intros pp l1 l2 Htrue.
  unfold are_squares_between_empty in *.
  destruct (one_step_along_vector_and_location l1 (vector_from_a_to_b l1 l2))
    eqn:Eos.
  apply are_squares_along_vector_empty_sound in Htrue.
  destruct (vector_length (vector_from_a_to_b l1 l2)) eqn:El1l2len.
  - rewrite vector_from_a_to_b_zero_iff in El1l2len. rewrite El1l2len.
    apply NothingOccupiedBetweenSingleSquare.
  - destruct Htrue as [Hv0 | Halong].
    + assert (HsIsl2: s = l2). { rewrite <- (vector_from_a_to_b_correct l1 l2).
        rewrite (one_step_along_vector_and_location_correct _ _ _ _ Eos).
        rewrite apply_null_vector; auto.
      }
      destruct (one_step_along_vector_and_location_adjacent _ _ _ _ Eos) as
        [Hsame | Hadj]. subst. apply NothingOccupiedBetweenSingleSquare.
      subst. constructor; auto.
    + destruct Halong as [Hfstempty Hrestempty].
      apply (SquaresAlongVectorEmpty pp l1 l2 (vector_from_a_to_b l1 l2) s);
      auto.
      * eapply one_step_same; eauto.
      * rewrite <- (vector_from_a_to_b_correct l1 l2).
        rewrite (one_step_along_vector_and_location_correct _ _ _ _ Eos). auto.
Qed.

Lemma one_step_along_zero : forall v l,
  vector_length v = 0 ->
  one_step_along_vector_and_location l v = (v, l).
Proof.
  intros v l Hlen.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  rewrite vector_length_0_iff in Hlen. destruct Hlen as [Hlen1 Hlen2]. subst.
  simpl. destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
Qed.

Lemma are_squares_between_empty_complete : forall pp l1 l2,
  SquaresBetweenEmpty pp l1 l2 -> are_squares_between_empty pp l1 l2 = true.
Proof.
  intros pp l1 l2 Hempty. unfold are_squares_between_empty.
  destruct (one_step_along_vector_and_location l1 (vector_from_a_to_b l1 l2))
    eqn:Eos.
  inversion Hempty.
  - subst. assert (Hv0: vector_length v = 0). { 
      apply (one_step_along_short_vector (vector_from_a_to_b l1 l2) l1 v s);
      auto. apply vector_from_a_to_b_in_bounds.
      rewrite (vector_from_a_to_b_correct l1 l2). auto.
    }
    rewrite are_squares_along_vector_empty_equation. Hp2b. rewrite Hv0. auto.
  - subst. assert (Hl1l2zero: vector_length (vector_from_a_to_b l2 l2) = 0).
    { apply vector_from_a_to_b_zero_iff. auto. }
    assert (Hosidem : one_step_along_vector_and_location l2 (vector_from_a_to_b l2 l2)
      = (vector_from_a_to_b l2 l2, l2)). { apply one_step_along_zero. auto. }
    rewrite Eos in Hosidem. inversion Hosidem. subst.
    rewrite are_squares_along_vector_empty_equation. Hp2b. rewrite Hl1l2zero.
    auto.
  - subst. apply are_squares_along_vector_empty_complete.
    + eapply one_step_stays_in_bounds. apply vector_from_a_to_b_in_bounds.
      apply Eos.
    + right. split. rewrite (one_step_same _ _ _ _ Eos) in H1. auto.
      rewrite (one_step_same _ _ _ _ Eos) in H2. 
      rewrite <- (one_step_along_vector_and_location_correct _ _ _ _ Eos).
      rewrite vector_from_a_to_b_correct. auto.
Qed.

Lemma are_squares_between_empty_correct : forall pp l1 l2,
  SquaresBetweenEmpty pp l1 l2 <-> are_squares_between_empty pp l1 l2 = true.
Proof.
  intros. split.
  - intros. apply are_squares_between_empty_complete. auto.
  - intros. apply are_squares_between_empty_sound. auto.
Qed.
