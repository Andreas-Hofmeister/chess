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

Definition eqSL (l1 l2: SquareLocation) :=
  match l1,l2 with Loc rank1 file1, Loc rank2 file2 =>
    ((rank1 =? rank2) && (file1 =? file2))%bool
  end.

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

Definition is_square_empty_rank_file (rank : nat) (file : nat) 
  (pp : PiecePlacements) :=
  match (get_square_by_index pp rank file) with
  | Empty => true
  | _ => false
  end.

Definition is_square_empty (loc : SquareLocation) (pp : PiecePlacements) :=
  match loc with Loc r f => is_square_empty_rank_file r f pp end.

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

Definition pawn_moves (pawn_loc : SquareLocation) (pos : Position) :=
  (pawn_forward_moves pawn_loc pos) ++
  (pawn_captures pawn_loc pos) ++
  (pawn_double_steps pawn_loc pos) ++
  (en_passant_moves pawn_loc pos).

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

Definition are_squares_adjacent (loc1 : SquareLocation) (loc2 : SquareLocation)
  : bool :=
  match loc1, loc2 with
  | Loc rank1 file1, Loc rank2 file2 => 
    (andb ((difference rank1 rank2) <=? 1) ((difference file1 file2) <=? 1))
  end.

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

Definition is_vector_to_adjacent_square (v : Vector) :=
  match v with
  | VectorHV (HStep _ n) (VStep _ m) =>
    ((n <=? 1) && (m <=? 1))%bool
  end.

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

Definition are_squares_between_empty (pp : PiecePlacements) 
  (loc1 : SquareLocation) (loc2 : SquareLocation) :=
  let (v, start) := 
    one_step_along_vector_and_location loc1 (vector_from_a_to_b loc1 loc2) in
  are_squares_along_vector_empty pp start v.

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

Function squares_on_same_rank (l : SquareLocation) : (list SquareLocation) :=
  match l with Loc rank file =>
    let make_square := (fun n => Loc rank n) in
    for_accumulate make_square (fun n => negb (n =? file)) 0 7
  end.

Function squares_on_same_file (l : SquareLocation) : (list SquareLocation) :=
  match l with Loc rank file =>
    let make_square := (fun n => Loc n file) in
    for_accumulate make_square (fun n => negb (n =? rank)) 0 7
  end.

Function rook_move_to_square_on_same_rank_or_file (pos : Position) 
  (fromL : SquareLocation) (toL : SquareLocation) : option Move :=
  match pos with
  | Posn pp c _ =>
    if ((negb (eqSL fromL toL)) && (are_squares_between_empty pp fromL toL))%bool
    then if is_square_empty toL pp then Some (FromTo fromL toL)
    else if is_square_occupied_by_enemy_piece toL pp c 
      then Some (Capture fromL toL)
      else None
    else None
  end.

Function rook_moves_to_square_on_same_rank_or_file_list (pos : Position)
  (fromL : SquareLocation) (toL : SquareLocation) : list Move :=
  match (rook_move_to_square_on_same_rank_or_file pos fromL toL) with
  | Some move => [move]
  | _ => []
  end.

Function rook_moves (l : SquareLocation) (pos : Position) : (list Move) :=
  (append_forall (rook_moves_to_square_on_same_rank_or_file_list pos l)
    (squares_on_same_rank l)) ++
  (append_forall (rook_moves_to_square_on_same_rank_or_file_list pos l)
    (squares_on_same_file l)).
