Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.

Definition is_knight_jump_vector (v : Vector) :=
  match v with
    | VectorHV (HStep _ 1) (VStep _ 2) => true
    | VectorHV (HStep _ 2) (VStep _ 1) => true
    | _ => false
  end.

Definition is_knight_jump (from to : SquareLocation) :=
  is_knight_jump_vector (vector_from_a_to_b from to).

Inductive KnightCanMakeMove (pos : Position)
  : SquareLocation -> Color -> Move -> Prop :=
  | KnightCanMove : forall pp c pos_c dstep from to, 
    location_valid from -> location_valid to ->
    pos = Posn pp pos_c dstep ->
    from <> to ->
    is_knight_jump from to = true ->
    is_square_empty to pp = true ->
    KnightCanMakeMove pos from c (FromTo from to)
  | KnightCanCapture : forall pp c pos_c dstep from to, 
    location_valid from -> location_valid to ->
    pos = Posn pp pos_c dstep ->
    from <> to ->
    is_knight_jump from to = true ->
    is_square_occupied_by_enemy_piece to pp c = true ->
    KnightCanMakeMove pos from c (Capture from to).

Definition knight_move_to_square (pos : Position) (c : Color)
  (fromL : SquareLocation) (toL : SquareLocation) : option Move :=
  match pos with
  | Posn pp _ _ =>
    if is_square_empty toL pp then Some (FromTo fromL toL)
    else if is_square_occupied_by_enemy_piece toL pp c 
      then Some (Capture fromL toL)
      else None
  end.

Fixpoint knight_moves_to_squares (pos : Position) (c : Color)
(from : SquareLocation) (tos : list SquareLocation) :=
  match tos with
  | [] => []
  | to :: rtos => 
    match knight_move_to_square pos c from to with
    | Some move => move :: (knight_moves_to_squares pos c from rtos)
    | _ => (knight_moves_to_squares pos c from rtos)
    end
  end.

Definition knight_moves (l : SquareLocation) (c: Color) (pos : Position) 
: (list Move) :=
  let llu := (VectorHV (HStep Left 2) (VStep Up 1)) in
  let lld := (VectorHV (HStep Left 2) (VStep Down 1)) in
  let rru := (VectorHV (HStep Right 2) (VStep Up 1)) in
  let rrd := (VectorHV (HStep Right 2) (VStep Down 1)) in
  let uul := (VectorHV (HStep Left 1) (VStep Up 2)) in
  let uur := (VectorHV (HStep Right 1) (VStep Up 2)) in
  let ddl := (VectorHV (HStep Left 1) (VStep Down 2)) in
  let ddr := (VectorHV (HStep Right 1) (VStep Down 2)) in
  knight_moves_to_squares pos c l 
    (target_squares l [llu;lld;rru;rrd;uul;uur;ddl;ddr]).


(******Proofs******)

Lemma knight_move_to_square_from : forall pos c fromL toL move,
  knight_move_to_square pos c fromL toL = Some move -> fromOfMove move = fromL.
Proof.
  intros pos c fromL toL move Hkm. unfold knight_move_to_square in *. 
  repeat DHmatch; inversion Hkm; simpl; auto.
Qed.

Lemma knight_moves_to_squares_from : forall tos pos c from move,
  In move (knight_moves_to_squares pos c from tos) -> fromOfMove move = from.
Proof.
  induction tos.
  - intros. simpl in *. contradiction.
  - intros pos c from move Hin. simpl in Hin. repeat DHmatch.
    + HinCases; subst.
      * eapply knight_move_to_square_from. eauto.
      * eapply IHtos. eauto.
    + eapply IHtos. eauto.
Qed.

Lemma knight_moves_from : forall l c pos move,
  In move (knight_moves l c pos) -> fromOfMove move = l.
Proof.
  intros l c pos move Hin. unfold knight_moves in *. 
  eapply knight_moves_to_squares_from. eauto.
Qed.

Lemma knight_move_to_square_iff : forall pp c toMove pds m from to,
  knight_move_to_square (Posn pp toMove pds) c from to = Some m <-> 
  ((is_square_empty to pp = true) /\ m = (FromTo from to)) \/
  ((is_square_occupied_by_enemy_piece to pp c = true) /\ 
    m = (Capture from to)).
Proof.
  intros pp c toMove pds m from to.
  split.
  - intros Hkm. unfold knight_move_to_square in *. DHif.
    + inversion Hkm. subst. auto.
    + DHif; try discriminate. inversion Hkm. subst. auto.
  - intros Hres. destruct Hres as [[Hempty1 Hempty2] | [Hoc1 Hoc2]]; subst; 
    simpl.
    + rewrite Hempty1. auto.
    + rewrite Hoc1. rewrite (occupied_not_empty _ _ _ Hoc1). auto.
Qed.

Lemma knight_jump_neq : forall from to,
  is_knight_jump from to = true -> from <> to.
Proof.
  intros. intros C. subst. destruct to. unfold is_knight_jump in *.
  simpl in H. diagonal_destruct. rewrite PeanoNat.Nat.sub_diag in *.
  discriminate.
Qed.

Ltac destruct_knight_move := match goal with
    | H : context[match knight_move_to_square ?a ?b ?c ?d with _ => _ end] |- _ 
      => destruct (knight_move_to_square a b c d) eqn:?E
    end.

Ltac knight_move_cases := match goal with
  | H : knight_move_to_square ?p _ _ _ = Some ?m |- KnightCanMakeMove ?p _ _ ?m
    => destruct p; rewrite knight_move_to_square_iff in H; 
       destruct H as [[?H ?H] | [?H ?H]]; subst
  | |- KnightCanMakeMove _ _ _ (FromTo _ _)
    => eapply KnightCanMove; eauto; unfold location_valid; try lia; 
       discriminate
  | |- KnightCanMakeMove _ _ _ (Capture _ _)
    => eapply KnightCanCapture; eauto; unfold location_valid; try lia; 
       discriminate
  end.

Lemma is_knight_jump_vector_iff : forall v,
  is_knight_jump_vector v = true <-> 
  In v [(VectorHV (HStep Left 2) (VStep Up 1));
        (VectorHV (HStep Left 2) (VStep Down 1));
        (VectorHV (HStep Right 2) (VStep Up 1));
        (VectorHV (HStep Right 2) (VStep Down 1));
        (VectorHV (HStep Left 1) (VStep Up 2));
        (VectorHV (HStep Right 1) (VStep Up 2));
        (VectorHV (HStep Left 1) (VStep Down 2));
        (VectorHV (HStep Right 1) (VStep Down 2))].
Proof.
  intros. split.
  - intros. unfold is_knight_jump_vector in *.
    destruct v. destruct hstep. destruct vstep.
    destruct n; destruct n0; try discriminate; destruct n; try discriminate.
    + destruct n; try discriminate.
    + destruct n0; try discriminate. destruct n0; try discriminate.
      destruct d; destruct d0; fIn.
    + destruct n; try discriminate. destruct n0; try discriminate.
      destruct d; destruct d0; fIn.
  - intros. repeat HinCases; subst; simpl; auto.
Qed.

Lemma knight_jump_vector_from_a_to_b_eq : forall from v,
  location_valid from -> does_vector_stay_within_boundaries v from = true ->
  is_knight_jump_vector v = true ->
  v = vector_from_a_to_b from (apply_vector v from).
Proof.
  intros. apply valid_squares in H. unfold valid_locations in H. 
  repeat HinCases; rewrite is_knight_jump_vector_iff in H1; repeat HinCases; 
  subst; simpl; simpl in H0; try discriminate; auto.
Qed.

Lemma knight_moves_sound_aux : forall vs from c pos move,
  location_valid from ->
  (forall v, In v vs -> is_knight_jump_vector v = true) ->
  In move (knight_moves_to_squares pos c from (target_squares from vs)) ->
  KnightCanMakeMove pos from c move.
Proof.
  induction vs; intros from c pos move Hfromv Hjvs Hin. 
  - simpl in Hin. contradiction.
  - simpl in Hin. DHif.
    + simpl in Hin. destruct_knight_move.
      * HinCases.
        -- subst. knight_move_cases.
           ++ eapply KnightCanMove; eauto. 
              apply does_vector_stay_within_boundaries_correct; auto.
              apply knight_jump_neq. unfold is_knight_jump.
              rewrite <- knight_jump_vector_from_a_to_b_eq; auto. apply Hjvs.
              apply in_eq. apply Hjvs. apply in_eq. unfold is_knight_jump. 
              rewrite <- knight_jump_vector_from_a_to_b_eq; auto.
              apply Hjvs. apply in_eq. apply Hjvs. apply in_eq.
           ++ eapply KnightCanCapture; eauto. 
              apply does_vector_stay_within_boundaries_correct; auto.
              apply knight_jump_neq. unfold is_knight_jump.
              rewrite <- knight_jump_vector_from_a_to_b_eq; auto. apply Hjvs.
              apply in_eq. apply Hjvs. apply in_eq. unfold is_knight_jump. 
              rewrite <- knight_jump_vector_from_a_to_b_eq; auto.
              apply Hjvs. apply in_eq. apply Hjvs. apply in_eq.
        -- apply IHvs; auto. intros. apply Hjvs. apply in_cons. auto.
      * apply IHvs; auto. intros. apply Hjvs. apply in_cons. auto.
    + apply IHvs; auto. intros. apply Hjvs. apply in_cons. auto.
Qed.

Lemma knight_moves_sound : forall pos from c move,
  location_valid from -> 
  In move (knight_moves from c pos) -> KnightCanMakeMove pos from c move.
Proof.
  intros pos from move Hv Hin.
  Ltac knight_move_finish_case := repeat destruct_knight_move; 
    repeat HinCases; subst; repeat knight_move_cases.
  unfold knight_moves in *.
  remember [VectorHV (HStep Left 2) (VStep Up 1);
              VectorHV (HStep Left 2) (VStep Down 1);
              VectorHV (HStep Right 2) (VStep Up 1);
              VectorHV (HStep Right 2) (VStep Down 1);
              VectorHV (HStep Left 1) (VStep Up 2);
              VectorHV (HStep Right 1) (VStep Up 2);
              VectorHV (HStep Left 1) (VStep Down 2);
              VectorHV (HStep Right 1) (VStep Down 2)] as vs.
  apply (knight_moves_sound_aux vs); auto.
  intros. rewrite Heqvs in H. apply is_knight_jump_vector_iff; auto.
Qed.

