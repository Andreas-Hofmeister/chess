Require Import List.
Require Import Nat.

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
  | DoubleStepFileRank (onFile : nat) (toRank : nat).

Definition get_double_step_target_rank (dstep : PawnDoubleStep) :=
  match dstep with
  | DoubleStepFileRank f r => r
  end.

Definition get_double_step_file (dstep : PawnDoubleStep) :=
  match dstep with
  | DoubleStepFileRank f r => f
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

Inductive PawnCanMoveTo (pos : Position) (c : Color) 
: nat -> nat -> nat -> nat -> Prop :=
  | PawnCanMoveForward : forall pp sf sr tr,
    pp = get_piece_placements pos ->
    tr = advance_pawn c sr -> 
    (indices_valid sr sf) = true -> 
    (indices_valid tr sf) = true ->
    get_square_by_index pp tr sf = Empty -> PawnCanMoveTo pos c sr sf tr sf
  | PawnCanCaptureDiagonallyForward : forall pp sf sr tf tr tc p,
    pp = get_piece_placements pos ->
    tr = advance_pawn c sr ->
    (tf = sf + 1 \/ tf = sf - 1) ->
    (indices_valid sr sf) = true -> 
    (indices_valid tr tf) = true ->
    get_square_by_index pp tr tf = Occupied tc p ->
    tc <> c -> PawnCanMoveTo pos c sr sf tr tf
  | PawnCanDoubleStep : forall pp sf sr tr,
    pp = get_piece_placements pos ->
    sr = starting_rank_of_pawn c ->
    tr = advance_pawn c (advance_pawn c sr) ->
    get_square_by_index pp tr sf = Empty ->
    PawnCanMoveTo pos c sr sf tr sf
  | EnPassant : forall pp dstep dstf sf sr tr,
    pp = get_piece_placements pos ->
    get_pawn_double_step pos = Some dstep ->
    sr = get_double_step_target_rank dstep ->
    dstf = get_double_step_file dstep ->
    (sf = dstf + 1 \/ sf = dstf - 1) ->
    tr = advance_pawn c sr ->
    PawnCanMoveTo pos c sr sf tr dstf.

Inductive SquareLocation : Type :=
  | Loc (rank : nat) (file : nat).

Definition is_square_empty (rank : nat) (file : nat) (pp : PiecePlacements) :=
  match (get_square_by_index pp rank file) with
  | Empty => true
  | _ => false
  end.

Definition pawn_forward_movements (pawn_loc : SquareLocation)
  (pp : PiecePlacements) (c : Color) : (list SquareLocation) :=
  match pawn_loc with
  | Loc r f => 
    let new_r := advance_pawn c r in
      if andb (indices_valid r f) (indices_valid new_r f) then
        if (is_square_empty new_r f pp) then [Loc new_r f]
        else nil
      else nil
  end.

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

Definition pawn_captures (pawn_loc : SquareLocation) (pp : PiecePlacements)
  (c : Color) : (list SquareLocation) :=
  match pawn_loc with
  | Loc r f =>
    if (indices_valid r f) then
      let new_r := advance_pawn c r in
      let left_capture := 
        if (occupied_by_enemy_piece new_r (f - 1) pp c) 
        then [Loc new_r (f - 1)] else []
      in
      let right_capture :=
        if (occupied_by_enemy_piece new_r (f + 1) pp c) 
        then [Loc new_r (f + 1)] else []
      in left_capture ++ right_capture
      else []
  end.

Definition pawn_movements (pawn_loc : SquareLocation) (pos : Position) :=
  match pos with
  | Posn pp toMove dstep =>
    (pawn_forward_movements pawn_loc pp toMove) ++
    (pawn_captures pawn_loc pp toMove)
  end.

Lemma pawn_movements_sound : forall sr sf tr tf pos,
  In (Loc tr tf) (pawn_movements (Loc sr sf) pos) ->
  PawnCanMoveTo pos (get_to_move pos) sr sf tr tf.
Proof.
  intros. unfold pawn_movements in H. destruct pos eqn:Epos. 
  apply in_app_or in H.
  destruct H as [H | H].
  - simpl in H.
    simpl.
    destruct (indices_valid (advance_pawn toMove sr) sf) eqn:Eiv; 
      try rewrite Bool.andb_false_r in H; simpl in H; try contradiction.
    destruct (indices_valid sr sf) eqn:Eiv2; try simpl in H; try contradiction.
    destruct (is_square_empty (advance_pawn toMove sr) sf pp) eqn:Eempty;
      try simpl in H; try contradiction.
    inversion H; try inversion H0.
    subst. eapply PawnCanMoveForward; eauto. simpl. 
    unfold is_square_empty in Eempty.
    destruct (get_square_by_index pp (advance_pawn toMove sr) tf); auto.
    discriminate.
  - simpl in H.
    destruct (indices_valid sr sf) eqn:Hivsrc; try inversion H.
    apply in_app_or in H. destruct H as [H | H].
    + destruct 
      (occupied_by_enemy_piece (advance_pawn toMove sr) (sf - 1) pp toMove)
      eqn: Eoc; try inversion H; try inversion H0.
      apply occupied_by_enemy_piece_correct in Eoc.
      destruct Eoc as [c2 [piece [Hiv [Hoc Henemy]]]].
      subst.
      eapply PawnCanCaptureDiagonallyForward; simpl; eauto.
    + destruct 
      (occupied_by_enemy_piece (advance_pawn toMove sr) (sf + 1) pp toMove)
      eqn: Eoc; try inversion H; try inversion H0.
      apply occupied_by_enemy_piece_correct in Eoc.
      destruct Eoc as [c2 [piece [Hiv [Hoc Henemy]]]].
      subst.
      eapply PawnCanCaptureDiagonallyForward; simpl; eauto.
Qed.
