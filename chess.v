Require Import List.
Require Import Nat.
From Coq Require Export Lia.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Inductive Color : Type :=
  | White
  | Black.

Definition ceq (c1 : Color) (c2 : Color) :=
  match c1 with
  | White => match c2 with White => true | Black => false end
  | Black => match c2 with White => false | Black => true end
  end.

Inductive Piece : Type :=
  | Pawn
  | Rook
  | Knight
  | Bishop
  | Queen
  | King.

Inductive Square : Type :=
  | Empty
  | Occupied (c : Color) (p : Piece).

Inductive File : Type :=
  | Squares (s1 : Square) (s2 : Square) (s3 : Square) (s4 : Square)
            (s5 : Square) (s6 : Square) (s7 : Square) (s8 : Square).

Inductive PiecePlacements : Type :=
  | Files (a : File) (b : File) (c : File) (d : File)
          (e : File) (f : File) (g : File) (h : File).

Inductive FileName : Type :=
  | fa
  | fb
  | fc
  | fd
  | fe
  | ff
  | fg
  | fh.

Inductive RankName : Type :=
  | r1
  | r2
  | r3
  | r4
  | r5
  | r6
  | r7
  | r8.

Definition rank_index (rn : RankName) : nat :=
  match rn with
  | r1 => 0
  | r2 => 1
  | r3 => 2
  | r4 => 3
  | r5 => 4
  | r6 => 5
  | r7 => 6
  | r8 => 7
  end.

Definition index_to_rank (i : nat) : RankName :=
  match i with
  | 0 => r1
  | 1 => r2
  | 2 => r3
  | 3 => r4
  | 4 => r5
  | 5 => r6
  | 6 => r7
  | 7 => r8
  | _ => r8
  end.

Definition file_index (fn : FileName) : nat :=
  match fn with
  | fa => 0
  | fb => 1
  | fc => 2
  | fd => 3
  | fe => 4
  | ff => 5
  | fg => 6
  | fh => 7
  end.

Definition index_to_file (i : nat) : FileName :=
  match i with
  | 0 => fa
  | 1 => fb
  | 2 => fc
  | 3 => fd
  | 4 => fe
  | 5 => ff
  | 6 => fg
  | 7 => fh
  | _ => fh
  end.

Definition get_file (pp : PiecePlacements) (fn : FileName) : File :=
  match pp with
  | Files a b c d e f g h =>
    match fn with
    | fa => a
    | fb => b
    | fc => c
    | fd => d
    | fe => e
    | ff => f
    | fg => g
    | fh => h
    end
  end.

Definition list_of_file (f : File) : (list Square) :=
  match f with
  | Squares s1 s2 s3 s4 s5 s6 s7 s8 => [s1;s2;s3;s4;s5;s6;s7;s8]
  end.

Definition get_square (pp : PiecePlacements) (rn : RankName) (fn : FileName)
  : Square :=
  match (get_file pp fn) with
  | Squares s1 s2 s3 s4 s5 s6 s7 s8 =>
    match rn with
    | r1 => s1
    | r2 => s2
    | r3 => s3
    | r4 => s4
    | r5 => s5
    | r6 => s6
    | r7 => s7
    | r8 => s8
    end
  end.

Definition get_file_list (pp : PiecePlacements) (fn : FileName) : 
(list Square) := 
  list_of_file (get_file pp fn).

Fixpoint collect_squares (i : nat) (l : list (list Square)) : (list Square) :=
  match l with
  | sqs :: l' 
    => match (nth_error sqs i) with
       | Some sq => sq :: collect_squares i l'
       | None => nil
       end
  | nil => nil
  end.

Definition get_rank_list (pp : PiecePlacements) (rn : RankName) : 
(list Square) :=
  match pp with
  | Files a b c d e f g h =>
    collect_squares (rank_index rn) (map list_of_file [a;b;c;d;e;f;g;h])
  end.

Definition get_square_by_index (pp : PiecePlacements) (rn : nat) (fn : nat) : 
Square :=
  (get_square pp (index_to_rank rn) (index_to_file fn)).

Definition rank_index_valid (ri : nat) : bool := ri <=? 7.
Definition file_index_valid := rank_index_valid.

Definition indices_valid (ri : nat) (fi : nat) : bool :=
  (file_index_valid fi) && (rank_index_valid ri).

Definition set_file (pp : PiecePlacements) (fn : FileName) (file : File)
: PiecePlacements :=
  match pp with
  | Files a b c d e f g h =>
    match fn with
    | fa => (Files file b c d e f g h)
    | fb => (Files a file c d e f g h)
    | fc => (Files a b file d e f g h)
    | fd => (Files a b c file e f g h)
    | fe => (Files a b c d file f g h)
    | ff => (Files a b c d e file g h)
    | fg => (Files a b c d e f file h)
    | fh => (Files a b c d e f g file)
    end
  end.

Definition set_file_by_index (pp : PiecePlacements) (i : nat) (file : File)
: PiecePlacements :=
  set_file pp (index_to_file i) file.

Definition set_square_in_file (r : RankName) (f : File) (s : Square) : 
File :=
  match f with
  | Squares s1 s2 s3 s4 s5 s6 s7 s8 =>
    match r with
    | r1 => Squares s s2 s3 s4 s5 s6 s7 s8
    | r2 => Squares s1 s s3 s4 s5 s6 s7 s8
    | r3 => Squares s1 s2 s s4 s5 s6 s7 s8
    | r4 => Squares s1 s2 s3 s s5 s6 s7 s8
    | r5 => Squares s1 s2 s3 s4 s s6 s7 s8
    | r6 => Squares s1 s2 s3 s4 s5 s s7 s8
    | r7 => Squares s1 s2 s3 s4 s5 s6 s s8
    | r8 => Squares s1 s2 s3 s4 s5 s6 s7 s
    end
  end.

Definition set_square_in_file_by_index (ri : nat) (f : File) (s : Square)
: File :=
  set_square_in_file (index_to_rank ri) f s.

Definition set_square (pp : PiecePlacements) (rn : RankName) (fn : FileName) 
(s : Square) : PiecePlacements :=
  set_file pp fn (set_square_in_file rn (get_file pp fn) s).

Definition set_square_by_index (pp : PiecePlacements) (ri : nat) (fi : nat)
(s : Square) : PiecePlacements :=
  if (indices_valid ri fi) then
  set_square pp (index_to_rank ri) (index_to_file fi) s
  else pp.

Lemma get_set_file_correct : forall pp fn f,
  get_file (set_file pp fn f) fn = f.
Proof.
  intros. unfold set_file. destruct pp eqn:Epp. destruct fn eqn:Efn;
  auto.
Qed.

Lemma get_set_square_correct : forall pp fn rn s,
  get_square (set_square pp rn fn s) rn fn = s.
Proof.
  Ltac destructFile := match goal with
  | |- match match ?x with _ => _ end with _ => _ end = _ => destruct x eqn:?H
  end.
  intros. destruct pp eqn:Epp. destruct fn eqn:Efn; destruct rn eqn:Ern;
  simpl; unfold set_square_in_file; unfold get_square; simpl; auto.
  all: destructFile; auto.
Qed.

Lemma get_set_square_by_index_correct : forall pp fi ri s,
  indices_valid ri fi = true ->
  get_square_by_index (set_square_by_index pp ri fi s) ri fi = s.
Proof.
  intros. unfold get_square_by_index. unfold set_square_by_index.
  rewrite H. apply get_set_square_correct.
Qed.

Inductive SquareLocation : Type :=
  | Loc (rank : nat) (file : nat).

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

Inductive Move : Type :=
  | FromTo (from : SquareLocation) (to : SquareLocation)
  | Capture (from : SquareLocation) (to : SquareLocation)
  | DoubleStep (from : SquareLocation) (to : SquareLocation)
  | EnPassant (from : SquareLocation) (to : SquareLocation).

Definition advance_pawn (c : Color) (rank_index : nat) :=
  match c with
  | White => (rank_index + 1)
  | Black => (rank_index - 1)
  end.

Definition starting_rank_of_pawn (c : Color) : nat :=
  match c with
  | White => 1
  | Black => 6
  end.

Inductive PawnDoubleStep : Type :=
  | DoubleStepRankFile (toRank : nat) (onFile : nat).

Definition get_double_step_target_rank (dstep : PawnDoubleStep) :=
  match dstep with
  | DoubleStepRankFile r f => r
  end.

Definition get_double_step_file (dstep : PawnDoubleStep) :=
  match dstep with
  | DoubleStepRankFile r f => f
  end.

Inductive Position : Type :=
  | Posn (pp : PiecePlacements) (toMove : Color) 
    (pawnDoubleStep : option PawnDoubleStep).

Definition get_piece_placements (pos : Position) :=
  match pos with
  | Posn pp _ _ => pp
  end.

Definition get_to_move (pos : Position) :=
  match pos with
  | Posn _ toMove _ => toMove
  end.

Definition get_pawn_double_step (pos : Position) :=
  match pos with
  | Posn _ _ dstep => dstep
  end.

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

Definition is_square_empty_rank_file (rank : nat) (file : nat) 
  (pp : PiecePlacements) :=
  match (get_square_by_index pp rank file) with
  | Empty => true
  | _ => false
  end.

Definition is_square_empty (loc : SquareLocation) (pp : PiecePlacements) :=
  match loc with Loc r f => is_square_empty_rank_file r f pp end.

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

Definition pawn_forward_moves (pawn_loc : SquareLocation)
  (pos : Position) : (list Move) :=
  match pos with
  | Posn pp c _ =>
    match pawn_loc with
    | Loc r f => 
      let new_r := advance_pawn c r in
        if andb (indices_valid r f) (indices_valid new_r f) then
          if (is_square_empty_rank_file new_r f pp) then [FromTo pawn_loc (Loc new_r f)]
          else nil
        else nil
    end
  end.

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

Definition occupied_by_enemy_piece (r : nat) (f : nat) (pp : PiecePlacements)
  (c : Color) : bool :=
  if (indices_valid r f) then
    match (get_square_by_index pp r f) with
    | Empty => false
    | Occupied oc _ => if (ceq oc c) then false else true
    end
  else
    false.

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

Definition pawn_captures (pawn_loc : SquareLocation) (pos : Position) 
  : (list Move) :=
  match pos with
  | Posn pp c _ =>
    match pawn_loc with
    | Loc r f =>
      if (indices_valid r f) then
        let new_r := advance_pawn c r in
        let left_capture := 
          if (occupied_by_enemy_piece new_r (f - 1) pp c) 
          then [Capture pawn_loc (Loc new_r (f - 1))] else []
        in
        let right_capture :=
          if (occupied_by_enemy_piece new_r (f + 1) pp c) 
          then [Capture pawn_loc (Loc new_r (f + 1))] else []
        in left_capture ++ right_capture
        else []
    end
  end.

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

Definition pawn_double_steps (pawn_loc : SquareLocation) 
  (pos : Position) :=
  match pos with
  | Posn pp c _ =>
    match pawn_loc with
    | Loc r f =>
      if (indices_valid r f) then
        if (starting_rank_of_pawn c) =? r then
          let step1r := (advance_pawn c r) in
          let step2r := (advance_pawn c step1r) in
            if andb (is_square_empty_rank_file step1r f pp) (is_square_empty_rank_file step2r f pp)
            then [DoubleStep pawn_loc (Loc step2r f)] else []
        else []
      else []
    end
  end.

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

Definition en_passant_moves (pawn_loc : SquareLocation) 
  (pos : Position) : (list Move) :=
  match pawn_loc with
  | Loc r f =>
    if (indices_valid r f) then
      match pos with
      | Posn pp toMove (Some (DoubleStepRankFile dsr dsf)) =>
        if (dsr =? r) then
          if (orb (dsf =? f + 1) (dsf =? f - 1)) then
            [EnPassant pawn_loc (Loc (advance_pawn toMove r) dsf)]
          else []
        else []
      | _ => []
      end
    else []
  end.

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

Definition pawn_moves (pawn_loc : SquareLocation) (pos : Position) :=
  (pawn_forward_moves pawn_loc pos) ++
  (pawn_captures pawn_loc pos) ++
  (pawn_double_steps pawn_loc pos) ++
  (en_passant_moves pawn_loc pos).

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

Inductive HorizontalDirection : Type :=
  | Left
  | Right.

Inductive VerticalDirection : Type :=
  | Up
  | Down.

Inductive HorizontalStep : Type :=
  | HStep (d : HorizontalDirection) (n : nat).

Inductive VerticalStep : Type :=
  | VStep (d : VerticalDirection) (n : nat).

Inductive Vector : Type :=
  | VectorHV (hstep : HorizontalStep) (vstep : VerticalStep).

Inductive VectorOnRank : Vector -> Prop :=
  | VectorOnRankConstr : forall hstep d,
    VectorOnRank (VectorHV hstep (VStep d 0)).

Inductive VectorOnFile : Vector -> Prop :=
  | VectorOnFileConstr : forall vstep d,
    VectorOnFile (VectorHV (HStep d 0) vstep).

Inductive DiagonalVector : Vector -> Prop :=
  | DiagonalVectorConstr : forall dh dv n,
    DiagonalVector (VectorHV (HStep dh n) (VStep dv n)).

Definition RankFileOrDiagonalVector (v : Vector) : Prop :=
  (VectorOnRank v) \/ (VectorOnFile v) \/ (DiagonalVector v).

Definition vector_from_a_to_b (a : SquareLocation) (b : SquareLocation) :=
  match a with Loc r_a f_a =>
    match b with Loc r_b f_b =>
      let rank_step := if r_a <=? r_b then (HStep Right (r_b - r_a))
        else (HStep Left (r_a - r_b)) in
      let file_step := if f_a <=? f_b then (VStep Up (f_b - f_a))
        else (VStep Down (f_a - f_b)) in
      (VectorHV rank_step file_step)
    end
  end.

Definition difference (i : nat) (j : nat) :=
  if (i <? j) then (j - i) else (i - j).

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

Definition are_squares_adjacent (loc1 : SquareLocation) (loc2 : SquareLocation)
  : bool :=
  match loc1, loc2 with
  | Loc rank1 file1, Loc rank2 file2 => 
    (andb ((difference rank1 rank2) <=? 1) ((difference file1 file2) <=? 1))
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

Definition one_step_along_vector (l : SquareLocation) (v : Vector) :=
  match l with
  | Loc r f => match v with
    | VectorHV (HStep _ 0) (VStep _ 0) => l
    | VectorHV (HStep _ 0) (VStep Up (S _)) => Loc r (f + 1)
    | VectorHV (HStep _ 0) (VStep Down (S _)) => Loc r (f - 1)
    | VectorHV (HStep Left (S _)) (VStep _ 0) => Loc (r - 1) f
    | VectorHV (HStep Right (S _)) (VStep _ 0) => Loc (r + 1) f
    | VectorHV (HStep Right (S _)) (VStep Up (S _)) => Loc (r + 1) (f + 1)
    | VectorHV (HStep Left (S _)) (VStep Up (S _)) => Loc (r - 1) (f + 1)
    | VectorHV (HStep Right (S _)) (VStep Down (S _)) => Loc (r + 1) (f - 1)
    | VectorHV (HStep Left (S _)) (VStep Down (S _)) => Loc (r - 1) (f - 1)
    end
  end.

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

Definition locations_equal (loc1 : SquareLocation) (loc2 : SquareLocation) :=
  match loc1,loc2 with
  | Loc x1 y1, Loc x2 y2 => ((x1 =? x2) && (y1 =? y2))%bool
  end.

Definition vector_length (v: Vector) : nat :=
  match v with
  | VectorHV (HStep _ n) (VStep _ m) => n + m
  end.

Definition manhattan_distance (loc1 : SquareLocation) (loc2 : SquareLocation)
:= vector_length (vector_from_a_to_b loc1 loc2).

Require Import Recdef. (* Must import this to use the Function feature *)

Definition one_step_along_vector_and_location (l : SquareLocation) (v : Vector) 
  : (Vector * SquareLocation) :=
  match l with
  | Loc r f => match v with
    | VectorHV (HStep dh 0) (VStep dv 0) => 
      (VectorHV (HStep dh 0) (VStep dv 0), l)
    | VectorHV (HStep dh 0) (VStep Up (S m)) => 
      (VectorHV (HStep dh 0) (VStep Up m), Loc r (f + 1))
    | VectorHV (HStep dh 0) (VStep Down (S m)) => 
      (VectorHV (HStep dh 0) (VStep Down m), Loc r (f - 1))
    | VectorHV (HStep Left (S n)) (VStep dv 0) => 
      (VectorHV (HStep Left n) (VStep dv 0), Loc (r - 1) f)
    | VectorHV (HStep Right (S n)) (VStep dv 0) => 
      (VectorHV (HStep Right n) (VStep dv 0), Loc (r + 1) f)
    | VectorHV (HStep Right (S n)) (VStep Up (S m)) => 
      (VectorHV (HStep Right n) (VStep Up m), Loc (r + 1) (f + 1))
    | VectorHV (HStep Left (S n)) (VStep Up (S m)) => 
      (VectorHV (HStep Left n) (VStep Up m), Loc (r - 1) (f + 1))
    | VectorHV (HStep Right (S n)) (VStep Down (S m)) => 
      (VectorHV (HStep Right n) (VStep Down m), Loc (r + 1) (f - 1))
    | VectorHV (HStep Left (S n)) (VStep Down (S m)) => 
      (VectorHV (HStep Left n) (VStep Down m), Loc (r - 1) (f - 1))
    end
  end.

Ltac Hdestruct :=
repeat match goal with 
  | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?H 
end.

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

Definition is_vector_to_adjacent_square (v : Vector) :=
  match v with
  | VectorHV (HStep _ n) (VStep _ m) =>
    ((n <=? 1) && (m <=? 1))%bool
  end.

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

Function are_squares_along_vector_empty (pp : PiecePlacements) 
  (start : SquareLocation) (v : Vector) {measure vector_length v} :=
  if (vector_length v) =? 0 then true
  else let (v2, fst) := one_step_along_vector_and_location start v in
    if is_square_empty start pp then
      are_squares_along_vector_empty pp fst v2
    else false.
Proof.
  intros. rewrite PeanoNat.Nat.eqb_neq in teq. 
  unfold one_step_along_vector_and_location in *. destruct start eqn:Es.
  destruct v eqn:Ev. repeat Hdestruct; simpl in teq; try lia; inversion teq0;
  subst; simpl; lia.
Defined.

Definition apply_hstep (s : HorizontalStep) (loc : SquareLocation) 
  : SquareLocation :=
  match s,loc with
  | HStep Left n, Loc r f => Loc (r - n) f
  | HStep Right n, Loc r f => Loc (r + n) f
  end.

Definition apply_vstep (s : VerticalStep) (loc : SquareLocation) 
  : SquareLocation :=
  match s,loc with
  | VStep Up n, Loc r f => Loc r (f + n)
  | VStep Down n, Loc r f => Loc r (f - n)
  end.

Definition apply_vector (v : Vector) (loc : SquareLocation) : SquareLocation :=
  match v with
  | VectorHV hstep vstep => (apply_vstep vstep (apply_hstep hstep loc))
  end.

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

Ltac dall := match goal with
| H : match ?x with _ => _ end = _ |- _ => destruct x eqn:?H
| |- match ?x with _ => _ end = _ => destruct x eqn:?H
| |- _ = match ?x with _ => _ end => destruct x eqn:?H
end.

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

(* Incorrect. v = vector_from_a_to_b s loc2 is not necessariliy true,
    because (0,Up) != (0,Down)

Lemma one_step_along_vector_and_location_correct2: forall loc1 loc2 v s,
  one_step_along_vector_and_location loc1 (vector_from_a_to_b loc1 loc2) 
    = (v, s) -> v = vector_from_a_to_b s loc2.
Proof.
  intros. unfold vector_from_a_to_b in H. 
  destruct loc1 eqn:Eloc1. destruct loc2 eqn:Eloc2.
  destruct (rank <=? rank0) eqn:Ernk; destruct (file <=? file0) eqn:Efl.
  - simpl in H. destruct (rank0 - rank) eqn:Ernk2; 
    destruct (file0 - file) eqn:Efl2; inversion H; subst.
    + simpl. rewrite Ernk. rewrite Efl. rewrite Ernk2. rewrite Efl2. auto.
    + simpl. rewrite Ernk. rewrite PeanoNat.Nat.leb_le in *.
      assert (Hfl3: file + 1 <= file0). lia. 
      rewrite <- PeanoNat.Nat.leb_le in Hfl3. rewrite Hfl3. apply eq_VectorHV;
      auto. lia.
    + simpl. rewrite Efl. rewrite PeanoNat.Nat.leb_le in *.
      assert (Hrnk3: rank + 1 <= rank0). lia. 
      rewrite <- PeanoNat.Nat.leb_le in Hrnk3. rewrite Hrnk3. 
      apply eq_VectorHV; auto. lia.
    + simpl. rewrite PeanoNat.Nat.leb_le in *.
      assert (Hfl3: file + 1 <= file0). lia.
      assert (Hrnk3: rank + 1 <= rank0). lia. rewrite <- PeanoNat.Nat.leb_le in *.
      rewrite Hfl3. rewrite Hrnk3. apply eq_VectorHV; auto; lia.
  - simpl in H. destruct (rank0 - rank) eqn:Ernk2; 
    destruct (file - file0) eqn:Efl2; inversion H; subst.
    + simpl. rewrite Ernk. rewrite Efl. rewrite Ernk2. rewrite Efl2. auto.
    + simpl. rewrite Ernk. destruct (file - 1 <=? file0) eqn:Efl3.
      * rewrite Ernk2. rewrite PeanoNat.Nat.leb_le in Efl3.
        assert (Hn: n = 0). lia. rewrite Hn. rewrite Hn in Efl2.
        assert (Hfl4: file0 - (file - 1) = 0). lia. rewrite Hfl4.
Qed.
*)

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

Definition make_vector_stay_in_bounds (v : Vector) (l : SquareLocation) :=
  match l with
  | Loc x y =>
    match v with
    | VectorHV (HStep Left n) (VStep Down m) =>
      VectorHV (HStep Left (min n x)) (VStep Down (min m y))
    | VectorHV (HStep Left n) (VStep Up m) =>
      VectorHV (HStep Left (min n x)) (VStep Up m)
    | VectorHV (HStep Right n) (VStep Down m) =>
      VectorHV (HStep Right n) (VStep Down (min m y))
    | _ => v
    end
  end.

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

Ltac Hb2p := match goal with
  | H : (_ <=? _) = true |- _ => rewrite PeanoNat.Nat.leb_le in H
  | H : (_ <=? _) = false |- _ => rewrite PeanoNat.Nat.leb_gt in H
  end.

Ltac Gb2p := match goal with
  | |- (_ <=? _) = true => rewrite PeanoNat.Nat.leb_le
  | |- (_ <=? _) = false => rewrite PeanoNat.Nat.leb_gt
  | |- true = (_ <=? _) => symmetry; rewrite PeanoNat.Nat.leb_le
  | |- false = (_ <=? _) => symmetry; rewrite PeanoNat.Nat.leb_gt
  end.

Lemma one_step_same : forall start v,
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
  - 

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
    + 
      

Definition are_squares_between_empty (pp : PiecePlacements) 
  (loc1 : SquareLocation) (loc2 : SquareLocation) :=
  let (v, start) := 
    one_step_along_vector_and_location loc1 (vector_from_a_to_b loc1 loc2) in
  are_squares_along_vector_empty pp start v.
