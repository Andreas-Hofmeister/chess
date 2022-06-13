Require Import List.
Require Import Nat.
From Coq Require Export Lia.
From CHESS Require Export proof_tactics.

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

Inductive SquareLocation : Type :=
  | Loc (rank : nat) (file : nat).

Definition SquaresOnSameFile (l1 l2 : SquareLocation) : Prop :=
  match l1,l2 with Loc _ file1, Loc _ file2 => file1 = file2 end.

Definition SquaresOnSameRank (l1 l2 : SquareLocation) : Prop :=
  match l1,l2 with Loc rank1 _, Loc rank2 _ => rank1 = rank2 end.

Definition eqSL (l1 l2: SquareLocation) :=
  match l1,l2 with Loc rank1 file1, Loc rank2 file2 =>
    ((rank1 =? rank2) && (file1 =? file2))%bool
  end.

Inductive PawnDoubleStep : Type :=
  | DoubleStepRankFile (toRank : nat) (onFile : nat).

Inductive Position : Type :=
  | Posn (pp : PiecePlacements) (toMove : Color) 
    (pawnDoubleStep : option PawnDoubleStep).

Definition get_piece_placements (pos : Position) :=
  match pos with
  | Posn pp _ _ => pp
  end.

Inductive IsOccupiedBy (pos : Position) 
  : SquareLocation -> Color -> Piece -> Prop :=
  | IsOccupiedBy_iff : forall pp rank_index file_index color piece,
    pp = get_piece_placements pos -> 
    get_square_by_index pp rank_index file_index = Occupied color piece ->
    IsOccupiedBy pos (Loc rank_index file_index) color piece.

Definition get_to_move (pos : Position) :=
  match pos with
  | Posn _ toMove _ => toMove
  end.

Definition get_pawn_double_step (pos : Position) :=
  match pos with
  | Posn _ _ dstep => dstep
  end.

Definition is_square_empty_rank_file (rank : nat) (file : nat) 
  (pp : PiecePlacements) :=
  match (get_square_by_index pp rank file) with
  | Empty => true
  | _ => false
  end.

Definition is_square_empty (loc : SquareLocation) (pp : PiecePlacements) :=
  match loc with Loc r f => is_square_empty_rank_file r f pp end.

Definition occupied_by_enemy_piece (r : nat) (f : nat) (pp : PiecePlacements)
  (c : Color) : bool :=
  if (indices_valid r f) then
    match (get_square_by_index pp r f) with
    | Empty => false
    | Occupied oc _ => if (ceq oc c) then false else true
    end
  else
    false.

Definition is_square_occupied_by_enemy_piece (l : SquareLocation) 
  (pp : PiecePlacements) (c : Color) : bool :=
  match l with Loc rank file => occupied_by_enemy_piece rank file pp c end.

Definition difference (i : nat) (j : nat) :=
  if (i <? j) then (j - i) else (i - j).

Definition locations_equal (loc1 : SquareLocation) (loc2 : SquareLocation) :=
  match loc1,loc2 with
  | Loc x1 y1, Loc x2 y2 => ((x1 =? x2) && (y1 =? y2))%bool
  end.

Definition are_squares_adjacent (loc1 : SquareLocation) (loc2 : SquareLocation)
  : bool :=
  match loc1, loc2 with
  | Loc rank1 file1, Loc rank2 file2 => 
    (andb (negb (locations_equal loc1 loc2))
      (andb ((difference rank1 rank2) <=? 1) ((difference file1 file2) <=? 1)))
  end.

Definition append_forall {A B : Type} (f : A -> list B) (l : list A) :=
  let f_inner := (fun acc x => (f x) ++ acc) in
    fold_left f_inner l [].

Fixpoint for_accumulate {A : Type} (f : nat -> A) (cond : nat -> bool) 
  (min_i max_i : nat) : list A :=
  match max_i with
  | 0 => if (cond 0) then [f 0] else []
  | S n => let new_elm := if (cond max_i) then [f max_i] else [] in
    if max_i =? min_i then
      if (cond max_i) then [f max_i] else []
    else 
      if (cond max_i) then (f max_i) :: (for_accumulate f cond min_i n)
      else (for_accumulate f cond min_i n)
  end.

Definition squares_on_same_rank (l : SquareLocation) : (list SquareLocation) :=
  match l with Loc rank file =>
    let make_square := (fun n => Loc rank n) in
    for_accumulate make_square (fun n => negb (n =? file)) 0 7
  end.

Definition squares_on_same_file (l : SquareLocation) : (list SquareLocation) :=
  match l with Loc rank file =>
    let make_square := (fun n => Loc n file) in
    for_accumulate make_square (fun n => negb (n =? rank)) 0 7
  end.

Definition location_valid (loc : SquareLocation) : Prop :=
  match loc with
  | Loc r f => r <= 7 /\ f <= 7
  end.

Definition is_location_valid (loc : SquareLocation) : bool :=
  match loc with
  | Loc r f => (r <=? 7) && (f <=? 7)
  end.

Definition SquaresAdjacent (loc1 : SquareLocation) (loc2 : SquareLocation)
  : Prop :=
  match loc1 with
  | Loc rank1 file1 => 
    match loc2 with
    | Loc rank2 file2 => 
      (difference rank1 rank2) <= 1 /\ (difference file1 file2) <= 1 /\
      loc1 <> loc2
    end
  end.

Definition locations_neq (loc1 loc2 : SquareLocation) : bool :=
  match loc1,loc2 with
  | Loc rnk1 fl1, Loc rnk2 fl2 => (negb (rnk1 =? rnk2)) || (negb (fl1 =? fl2))
  end.

Definition adjacent_squares (loc : SquareLocation) : (list SquareLocation) :=
  match loc with
  | Loc r f => filter (locations_neq loc) (filter is_location_valid 
    [Loc r (f+1); Loc (r+1) (f+1); Loc (r+1) f; Loc (r+1) (f-1); Loc r (f-1);
    Loc (r-1) (f-1); Loc (r-1) f; Loc (r-1) (f+1)])
  end.

(******************************Proofs**********************************)

Lemma locations_neq_iff: forall loc1 loc2,
  locations_neq loc1 loc2 = true <-> loc1 <> loc2.
Proof.
  intros loc1 loc2. unfold locations_neq. repeat DGmatch. split.
  - intros H. Hb2p. HdOr; repeat Hb2p; intros C; inversion C; lia.
  - intros H. Gb2p. destruct (rank =? rank0) eqn:?E; 
    destruct (file =? file0) eqn:?E; simpl; auto. repeat Hb2p. exfalso.
    apply H. subst. auto.
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

Lemma valid_squares : forall loc,
  location_valid loc ->
  In loc 
  [Loc 0 0; Loc 0 1; Loc 0 2; Loc 0 3; Loc 0 4; Loc 0 5; Loc 0 6; Loc 0 7;
   Loc 1 0; Loc 1 1; Loc 1 2; Loc 1 3; Loc 1 4; Loc 1 5; Loc 1 6; Loc 1 7;
   Loc 2 0; Loc 2 1; Loc 2 2; Loc 2 3; Loc 2 4; Loc 2 5; Loc 2 6; Loc 2 7;
   Loc 3 0; Loc 3 1; Loc 3 2; Loc 3 3; Loc 3 4; Loc 3 5; Loc 3 6; Loc 3 7;
   Loc 4 0; Loc 4 1; Loc 4 2; Loc 4 3; Loc 4 4; Loc 4 5; Loc 4 6; Loc 4 7;
   Loc 5 0; Loc 5 1; Loc 5 2; Loc 5 3; Loc 5 4; Loc 5 5; Loc 5 6; Loc 5 7;
   Loc 6 0; Loc 6 1; Loc 6 2; Loc 6 3; Loc 6 4; Loc 6 5; Loc 6 6; Loc 6 7;
   Loc 7 0; Loc 7 1; Loc 7 2; Loc 7 3; Loc 7 4; Loc 7 5; Loc 7 6; Loc 7 7].
Proof.
  intros loc Hv. unfold location_valid in *.
  destruct loc eqn:Eloc.
  destruct Hv as [Hvr Hvf]. 
  destruct rank eqn:?E; destruct file eqn:?E.
  repeat (apply in_eq || apply in_cons).
  destruct n. fIn. destruct n. fIn. destruct n. fIn. destruct n. fIn.
  destruct n. fIn. destruct n. fIn. destruct n. fIn. lia.
  destruct n. fIn. destruct n. fIn. destruct n. fIn. destruct n. fIn.
  destruct n. fIn. destruct n. fIn. destruct n. fIn. lia.
  destruct n. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  lia. 
  destruct n. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  lia. 
  destruct n. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  lia. 
  destruct n. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  lia. 
  destruct n. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  lia. 
  destruct n. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  lia. 
  destruct n. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. destruct n0. fIn. 
  lia. 
  lia.
Qed.

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

Lemma eq_Loc : forall rank file rank1 file1, 
  rank = rank1 -> file = file1 -> Loc rank file = Loc rank1 file1.
Proof.
  intros. subst. auto.
Qed.

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

Lemma is_location_valid_correct : forall loc,
  location_valid loc <-> is_location_valid loc = true.
Proof.
  intros loc. split.
  - intros. unfold location_valid in *. unfold is_location_valid.
    DHmatch. Gb2p. split; Gb2p; lia.
  - intros. unfold location_valid in *. unfold is_location_valid in *.
    DHmatch. Hb2p. destruct H as [H1 H2]. repeat Hb2p. auto.
Qed.

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

Lemma are_squares_adjacent_correct : forall loc1 loc2,
  are_squares_adjacent loc1 loc2 = true <-> SquaresAdjacent loc1 loc2.
Proof.
  intros. split.
  - intros. unfold are_squares_adjacent in H. destruct loc1 eqn:Eloc1.
    destruct loc2 eqn:Eloc2. repeat rewrite Bool.andb_true_iff in H.
    repeat rewrite PeanoNat.Nat.leb_le in H. simpl in H.
    rewrite Bool.negb_true_iff in H. destruct H as [H1 [H2 H3]]. Hb2p.
    constructor; auto. split. auto. intros C. inversion C. subst.
    repeat rewrite PeanoNat.Nat.eqb_refl in H1. lia.
  - intros. unfold SquaresAdjacent in H. destruct loc1 eqn:Eloc1.
    destruct loc2 eqn:Eloc2. repeat rewrite <- PeanoNat.Nat.leb_le in H.
    destruct H as [H1 [H2 H3]]. simpl.
    repeat rewrite Bool.andb_true_iff. repeat split; auto. 
    rewrite Bool.negb_true_iff. rewrite Bool.andb_false_iff.
    destruct (rank =? rank0) eqn:?E; destruct (file =? file0) eqn:?E.
    + repeat Hb2p. subst. contradiction.
    + right. auto.
    + left. auto.
    + left. auto.
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

Lemma n_minus_1_minus_n : forall n, n - 1 - n = 0.
Proof. lia. Qed.

Lemma adjacent_squares_correct : forall l1 l2,
  (SquaresAdjacent l1 l2 /\ location_valid l1 /\ location_valid l2) <-> 
  (location_valid l1 /\ In l2 (adjacent_squares l1)).
Proof.
  intros l1 l2. split.
  - intros [Hadj [Hv1 Hv2]]. split; auto.
    unfold SquaresAdjacent in *.
    unfold adjacent_squares. DGmatch. DHmatch. 
    destruct Hadj as [Hdrank [Hdfile Huneq]]. unfold difference in *. 
    repeat DHif; repeat Hb2p.
    + assert (Hdrank2: rank0 = rank + 1). { lia. }
      assert (Hdfile2: file0 = file + 1). { lia. }
      subst. apply filter_In. split. apply filter_In. split. 
      apply in_cons. apply in_eq. rewrite <- is_location_valid_correct. auto.
      apply locations_neq_iff. auto.
    + assert (Hdfile2: file0 = file + 1). { lia. }
      destruct (rank - rank0) eqn:?E.
      * assert (Hdrank2: rank = rank0). { lia. } subst.
        apply filter_In. split. apply filter_In. split. apply in_eq. 
        rewrite <- is_location_valid_correct. auto. apply locations_neq_iff. 
        auto.
      * destruct n eqn:?E; try lia.
        assert (Hdrank2: rank = rank0 + 1). { lia. } subst.
        apply filter_In. split. apply filter_In. split.
        replace (rank0 + 1 - 1) with rank0. 
        repeat (apply in_eq || apply in_cons). lia. 
        rewrite <- is_location_valid_correct. auto. apply locations_neq_iff. 
        auto.
    + assert (Hdrank2: rank0 = rank + 1). { lia. }
      destruct (file - file0) eqn:?E.
      * assert (Hfile2: file0 = file). { lia. } subst.
        apply filter_In. split. apply filter_In. split.
        repeat (apply in_eq || apply in_cons).
        rewrite <- is_location_valid_correct. auto.
        apply locations_neq_iff. auto.
      * destruct n eqn:?E; try lia.
        assert (Hfile2: file = file0 + 1). { lia. } subst.
        apply filter_In. split. apply filter_In. split.
        replace (file0 + 1 - 1) with file0.
        repeat (apply in_eq || apply in_cons). lia.
        rewrite <- is_location_valid_correct. auto.
        apply locations_neq_iff. auto.
    + destruct (rank - rank0) eqn:?E; destruct (file - file0) eqn:?E.
      * assert (Hfile2: file0 = file). { lia. }
        assert (Hdrank2: rank = rank0). { lia. } subst.
        contradiction.
      * destruct n eqn:?E; try lia.
        assert (Hdrank2: rank = rank0). { lia. }
        assert (Hfile2: file = file0 + 1). { lia. } subst.
        apply filter_In. split. apply filter_In. split. 
        replace (file0 + 1 - 1) with file0. 
        repeat (apply in_eq || apply in_cons). lia.
        rewrite <- is_location_valid_correct. auto. apply locations_neq_iff. 
        auto.
      * destruct n eqn:?E; try lia.
        assert (Hdrank2: rank = rank0 + 1). { lia. }
        assert (Hfile2: file = file0). { lia. } subst.
        apply filter_In. split. apply filter_In. split.
        replace (rank0 + 1 - 1) with rank0.
        repeat (apply in_eq || apply in_cons). lia.
        rewrite <- is_location_valid_correct. auto. apply locations_neq_iff.
        auto.
      * destruct n eqn:?E; try lia. destruct n0 eqn:?E; try lia.
        assert (Hdrank2: rank = rank0 + 1). { lia. }
        assert (Hfile2: file = file0 + 1). { lia. } subst.
        apply filter_In. split. apply filter_In. split.
        replace (rank0 + 1 - 1) with rank0. replace (file0 + 1 - 1) with file0.
        repeat (apply in_eq || apply in_cons). lia. lia. 
        rewrite <- is_location_valid_correct. auto. apply locations_neq_iff. 
        auto.
  - intros Hin. unfold adjacent_squares in *. DHmatch. rewrite filter_In in Hin.
    destruct Hin as [Hvalid1 [Hin Hneq]]. rewrite filter_In in Hin.
    destruct Hin as [Hin Hvalid2].
    rewrite <- is_location_valid_correct in *. rewrite locations_neq_iff in *.
    split; auto. repeat HinCases; subst.
    + simpl. unfold difference. rewrite PeanoNat.Nat.ltb_irrefl.
      rewrite n_lt_np1. rewrite PeanoNat.Nat.sub_diag.
      replace (file + 1 - file) with 1; try lia. repeat split; try lia.
      intros C. inversion C. lia.
    + simpl. unfold difference. repeat rewrite n_lt_np1. 
      repeat rewrite PeanoNat.Nat.ltb_irrefl. 
      replace (file + 1 - file) with 1; try lia.
      replace (rank + 1 - rank) with 1; try lia.
      repeat split; try lia. intros C. inversion C. lia.
    + simpl. unfold difference. repeat rewrite n_lt_np1. 
      repeat rewrite PeanoNat.Nat.ltb_irrefl. 
      replace (file + 1 - file) with 1; try lia.
      replace (rank + 1 - rank) with 1; try lia.
      repeat split; try lia. intros C. inversion C. lia.
    + simpl. unfold difference. repeat rewrite n_lt_np1. 
      repeat rewrite PeanoNat.Nat.ltb_irrefl. 
      replace (file - 1 - file) with 0; try lia.
      replace (rank + 1 - rank) with 1; try lia.
      destruct (file <? file - 1) eqn:?E; repeat split; auto; try lia.
    + simpl. unfold difference. destruct file eqn:?E. simpl in *. contradiction. 
      rewrite PeanoNat.Nat.ltb_irrefl.
      replace (rank - rank) with 0; try lia. simpl. rewrite PeanoNat.Nat.sub_0_r.
      rewrite Sn_lt_n. DGmatch; repeat split; try lia; auto.
    + simpl. unfold difference. repeat rewrite n_minus_1_minus_n. 
      repeat rewrite n_lt_nm1. repeat split; try lia. auto.
    + simpl. unfold difference. repeat rewrite n_lt_nm1. 
      repeat rewrite PeanoNat.Nat.ltb_irrefl. rewrite PeanoNat.Nat.sub_diag.
      repeat split; try lia. auto.
    + simpl. unfold difference. repeat rewrite n_lt_nm1. repeat rewrite n_lt_np1.
      repeat split; try lia. auto.
Qed.

Lemma append_forall_fold_acc : forall A B (f : A -> list B) l b accl,
  In b accl -> In b (fold_left (fun acc x => (f x) ++ acc) l accl).
Proof.
  intros A B f.
  induction l.
  - intros. simpl. auto.
  - intros. simpl. apply IHl. apply in_or_app. auto.
Qed.

Lemma append_forall_fold_acc2 : forall A B (f : A -> list B) l x accl1 accl2,
  (forall y, In y accl1 -> In y accl2) ->
  In x (fold_left (fun (acc : list B) (x : A) => f x ++ acc) l accl1) ->
  In x (fold_left (fun (acc : list B) (x : A) => f x ++ acc) l accl2).
Proof.
  intros A B f. induction l.
  - intros. simpl in H. simpl. simpl in H0. auto.
  - intros. simpl. simpl in H0. apply IHl with (accl1:=(f a ++ accl1)).
    + intros. apply in_app_or in H1. destruct H1 as [H1 | H1]; apply in_or_app;
      auto.
    + auto.
Qed.

Lemma append_forall_fold_acc3 : forall A B (f : A -> list B) l x accl,
  In x (fold_left (fun (acc : list B) (x : A) => f x ++ acc) l accl) ->
  In x accl \/ exists a, In a l /\ In x (f a).
Proof.
  intros A B f. induction l.
  - intros. simpl in H. auto.
  - intros. simpl in H. specialize (IHl x _ H) as IHl2.
    destruct IHl2 as [IHl2 | [a2 IHl2]].
    + apply in_app_or in IHl2. destruct IHl2 as [IHl2 | IHl2]; auto.
      right. exists a. split. apply in_eq. auto.
    + right. exists a2. split. apply in_cons. apply IHl2. apply IHl2.
Qed.

Lemma in_append_forall_nec : forall A B (f : A -> list B) a l x,
  In a l -> In x (f a) -> In x (append_forall f l).
Proof.
  intros. unfold append_forall.
  induction l.
  - inversion H.
  - inversion H.
    + subst. simpl. apply append_forall_fold_acc. apply in_or_app. auto.
    + simpl. apply append_forall_fold_acc2 with (accl1:=[]). intros y C.
      inversion C. auto.
Qed.

Lemma in_append_forall_suf : forall A B (f : A -> list B) l x,
  In x (append_forall f l) -> exists a, In a l /\ In x (f a).
Proof.
  intros. unfold append_forall in H. apply append_forall_fold_acc3 in H.
  destruct H as [C | [a H]]; try inversion C. exists a. auto.
Qed.

Lemma eqSL_iff : forall l1 l2,
  eqSL l1 l2 = true <-> l1 = l2.
Proof.
  intros. 
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst.
  split.
  - intros. inversion H. subst. Hb2p. destruct H1 as [Hr Hf]. repeat Hb2p.
    subst. auto.
  - intros. inversion H. subst. auto. simpl. 
    repeat rewrite PeanoNat.Nat.eqb_refl. auto.
Qed.

Lemma occupied_not_empty : forall l pp c,
  is_square_occupied_by_enemy_piece l pp c = true ->
  is_square_empty l pp = false.
Proof.
  intros. destruct l eqn:El. 
  unfold is_square_occupied_by_enemy_piece in H.
  simpl. unfold occupied_by_enemy_piece in H.
  destruct (indices_valid rank file) eqn:Eiv; try discriminate.
  destruct (get_square_by_index pp rank file) eqn:Egs; try discriminate.
  unfold is_square_empty_rank_file. rewrite Egs. auto.
Qed.

Lemma for_accumulate_correct : forall A cond (f : nat -> A) mini maxi a,
  mini <= maxi ->
  In a (for_accumulate f cond mini maxi) <-> 
  (exists i, mini <= i /\ i <= maxi /\ (cond i) = true /\ a = (f i)).
Proof.
  intros A cond f mini. induction maxi.
  - intros a Hinrange. split. 
    + intros Hinresult. simpl in Hinresult. destruct (cond 0) eqn:Econd0;
      inversion Hinresult; try inversion H. subst. exists 0. auto.
    + intros [i [Hex1 [Hex2 [Hex3 Hex4]]]]. simpl. assert (Hmini0: mini = 0). 
      lia. subst. assert (Hi0: i = 0). lia. subst. rewrite Hex3.
      constructor. auto.
  - intros a Hinrange. split.
    + intros Hinresult. simpl in Hinresult. 
      destruct mini eqn:Hmini.
      * destruct (cond (S maxi)) eqn:Econd.
        -- inversion Hinresult.
           ++ exists (S maxi). auto.
           ++ assert (Hduh: 0 <= maxi). lia. 
              specialize (IHmaxi a Hduh) as [IH1 IH2].
              specialize (IH1 H) as [i [Hex1 [Hex2 [Hex3 Hex4]]]]. exists i.
              auto.
        -- assert (Hduh: 0 <= maxi). lia. 
           specialize (IHmaxi a Hduh) as [IH1 IH2].
           specialize (IH1 Hinresult) as [i [Hex1 [Hex2 [Hex3 Hex4]]]]. 
           exists i. auto.
      * destruct (maxi =? n) eqn:Hlast.
        -- destruct (cond (S maxi)) eqn:Econd; inversion Hinresult; 
           try inversion H. exists (S maxi). auto.
        -- destruct (cond (S maxi)) eqn:Econd.
           ++ inversion Hinresult.
              ** exists (S maxi). auto.
              ** Hb2p. assert (Hran: S n <= maxi). lia.
                 specialize (IHmaxi a Hran) as [IH1 IH2].
                 specialize (IH1 H) as [i [Hex1 [Hex2 [Hex3 Hex4]]]]. subst.
                 exists i. auto.
           ++ Hb2p. assert (Hran: S n <= maxi). lia.
              specialize (IHmaxi a Hran) as [IH1 IH2].
              specialize (IH1 Hinresult) as [i [Hex1 [Hex2 [Hex3 Hex4]]]].
              exists i. auto.
    + intros [i [Hex1 [Hex2 [Hex3 Hex4]]]].
      destruct (mini =? S maxi) eqn:Elast.
      * Hb2p. assert (HiIsMini: mini = i). lia. subst. simpl.
        replace (maxi =? maxi) with true; try Gb2p; try lia.
        rewrite Hex3. constructor. auto.
      * Hb2p. assert (Hmini: mini <= maxi). lia. simpl.
        destruct mini eqn:Emini.
        -- destruct (cond (S maxi)) eqn:Econd.
           ++ destruct (i =? (S maxi)) eqn:Ei. 
              ** Hb2p. subst. constructor. auto.
              ** Hb2p. apply in_cons. apply IHmaxi; auto. exists i. 
                 repeat split; auto. lia.
           ++ destruct (i =? (S maxi)) eqn:Ei.
              ** Hb2p. subst. rewrite Hex3 in Econd. discriminate.
              ** Hb2p. apply IHmaxi; auto. exists i. repeat split; auto. lia.
        -- assert (maxi <> n). lia. rewrite <- PeanoNat.Nat.eqb_neq in H.
           rewrite H. destruct (i =? (S maxi)) eqn:Ei.
           ++ repeat Hb2p. rewrite Ei in Hex3. rewrite Hex3. subst.
              constructor. auto.
           ++ destruct (cond (S maxi)).
              ** apply in_cons. apply IHmaxi; auto. exists i. repeat split; auto.
                 Hb2p. lia.
              ** apply IHmaxi; auto. exists i. repeat split; auto. Hb2p. lia.
Qed.

Lemma squares_on_same_file_sound : forall l1 l2,
  In l2 (squares_on_same_file l1) -> SquaresOnSameFile l1 l2.
Proof.
  intros l1 l2 Hin. unfold squares_on_same_file in Hin. 
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst.
  rewrite for_accumulate_correct in Hin; try lia. 
  destruct Hin as [i [Hi1 [Hi2 [Hi3 Hi4]]]]. simpl in *.
  inversion Hi4. auto.
Qed.

Lemma squares_on_same_file_complete : forall l1 l2,
  location_valid l1 -> location_valid l2 -> SquaresOnSameFile l1 l2 ->
  l1 <> l2 ->
  In l2 (squares_on_same_file l1).
Proof.
  intros l1 l2 Hv1 Hv2 Hsamef Hunequal.
  unfold location_valid in *.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst. unfold squares_on_same_file.
  apply for_accumulate_correct. lia. unfold SquaresOnSameFile in *.
  exists rank0. repeat split; auto; try lia.
  destruct (rank0 =? rank) eqn:Ernk.
  - Hb2p. subst. contradiction.
  - simpl. auto.
Qed.

Lemma squares_on_same_rank_sound : forall l1 l2,
  In l2 (squares_on_same_rank l1) -> SquaresOnSameRank l1 l2.
Proof.
  intros l1 l2 Hin. unfold squares_on_same_rank in Hin. 
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst.
  rewrite for_accumulate_correct in Hin; try lia. 
  destruct Hin as [i [Hi1 [Hi2 [Hi3 Hi4]]]]. simpl in *.
  inversion Hi4. auto.
Qed.

Lemma squares_on_same_rank_complete : forall l1 l2,
  location_valid l1 -> location_valid l2 -> SquaresOnSameRank l1 l2 ->
  l1 <> l2 ->
  In l2 (squares_on_same_rank l1).
Proof.
  intros l1 l2 Hv1 Hv2 Hsamer Hunequal.
  unfold location_valid in *.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst. unfold squares_on_same_file.
  apply for_accumulate_correct. lia. unfold SquaresOnSameRank in *.
  exists file0. repeat split; auto; try lia.
  destruct (file0 =? file) eqn:Efl.
  - Hb2p. subst. contradiction.
  - simpl. auto.
Qed.

Lemma squares_on_same_rank_valid : forall l1 l2,
  location_valid l1 -> In l2 (squares_on_same_rank l1) -> location_valid l2.
Proof.
  intros l1 l2 Hvalid Hin.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst. simpl.
  unfold squares_on_same_rank in Hin. apply for_accumulate_correct in Hin.
  - destruct Hin as [i [Hi1 [Hi2 [Hi3 Hi4]]]]. unfold location_valid in Hvalid.
    inversion Hi4. subst. lia.
  - lia.
Qed.

Lemma squares_on_same_file_valid : forall l1 l2,
  location_valid l1 -> In l2 (squares_on_same_file l1) -> location_valid l2.
Proof.
  intros l1 l2 Hvalid Hin.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst. simpl.
  unfold squares_on_same_file in Hin. apply for_accumulate_correct in Hin.
  - destruct Hin as [i [Hi1 [Hi2 [Hi3 Hi4]]]]. unfold location_valid in Hvalid.
    inversion Hi4. subst. lia.
  - lia.
Qed.

Lemma n_leb_n_plus_1: forall n, n <=? n + 1 = true.
Proof.
  intros. Gb2p. lia.
Qed.

Lemma n_plus_m_minus_n: forall n m, n + m - n = m.
Proof.
  intros. lia.
Qed.

Lemma Sn_leb_Sn_minus_1: forall n, S n <=? (S n) - 1 = false.
Proof.
  intros. Gb2p. lia.
Qed.

Lemma n_minus_n_minus_m: forall n m, m <= n -> n - (n - m) = m.
Proof.
  intros. lia.
Qed.

Lemma Sn_leb_n: forall n, S n <=? n = false.
Proof.
  intros. Gb2p. lia.
Qed.

Lemma min_or: forall x y, (min x y = x \/ min x y = y).
Proof.
  intros. induction x.
  - simpl. auto.
  - simpl. destruct y; auto. destruct IHx as [IHx | IHx]; lia.
Qed.
