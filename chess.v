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
    sr = starting_rank_of_pawn c ->
    step1r = advance_pawn c sr ->
    tr = advance_pawn c step1r ->
    get_square_by_index pp step1r sf = Empty ->
    get_square_by_index pp tr sf = Empty ->
    PawnCanMakeMove pos loc (DoubleStep loc (Loc tr sf))
  | PawnCanCaptureEnPassant : forall pp c dstep loc dstf sf sr tr,
    pos = Posn pp c (Some dstep) -> loc = Loc sr sf ->
    dstep = (DoubleStepRankFile sr dstf) ->
    (sf = dstf + 1 \/ sf = dstf - 1) ->
    tr = advance_pawn c sr ->
    PawnCanMakeMove pos loc (EnPassant loc (Loc tr dstf)).

Definition is_square_empty (rank : nat) (file : nat) (pp : PiecePlacements) :=
  match (get_square_by_index pp rank file) with
  | Empty => true
  | _ => false
  end.

Lemma is_square_empty_correct : forall r f pp,
  is_square_empty r f pp = true <-> (get_square_by_index pp r f) = Empty.
Proof.
  intros. 
  split.
  - intros. unfold is_square_empty in *. 
    destruct (get_square_by_index pp r f) eqn:Egs; auto. discriminate.
  - intros. unfold is_square_empty in *. 
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
          if (is_square_empty new_r f pp) then [FromTo pawn_loc (Loc new_r f)]
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
  destruct (is_square_empty (advance_pawn toMove rank) file pp) eqn:Eempty;
    try simpl in H; try contradiction.
  destruct H as [H | W]; try contradiction.
  subst. rewrite <- location_valid_iff in *. 
  rewrite is_square_empty_correct in *.
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
            if andb (is_square_empty step1r f pp) (is_square_empty step2r f pp)
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
  rewrite Bool.andb_true_iff in *. repeat rewrite is_square_empty_correct in *.
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
  simpl. eapply PawnCanCaptureEnPassant; simpl; eauto; simpl. lia.
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
    rewrite <- is_square_empty_correct in *. rewrite H5. constructor. auto.
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
    simpl.
Admitted.
    
