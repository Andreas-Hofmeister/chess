Require Import List.
Require Import Nat.
From Coq Require Export Lia.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Ltac HdAnd := match goal with
  | H : _ /\ _ |- _ => destruct H as [?H ?H]
  end.

(* Definitions *)

Inductive Color : Type := White | Black.

Definition opponent_of (c : Color) :=
  match c with | White => Black | Black => White end.

Definition ceq (c1 : Color) (c2 : Color) :=
  match c1 with
  | White => match c2 with White => true | Black => false end
  | Black => match c2 with White => false | Black => true end
  end.

Inductive Piece : Type := Pawn | King.

Definition eqPiece (p1 p2 : Piece) :=
  match p1,p2 with
  | Pawn, Pawn => true
  | King, King => true
  | _,_ => false
  end.

Inductive Square : Type := Empty | Occupied (c : Color) (p : Piece).

Definition eqSq (s1 s2 : Square) : bool :=
  match s1,s2 with
  | Empty, Empty => true
  | Occupied c1 p1, Occupied c2 p2 => (andb (eqPiece p1 p2) (ceq c1 c2))
  | _, _ => false
  end.

Inductive File : Type :=
  | Squares (s1 : Square) (s2 : Square) (s3 : Square) (s4 : Square).

Inductive PiecePlacements : Type :=
  | Files (a : File) (b : File) (c : File) (d : File).

Inductive FileName : Type := fa | fb | fc | fd.

Inductive RankName : Type := r1 | r2 | r3 | r4.

Definition rank_index (rn : RankName) : nat :=
  match rn with
  | r1 => 0
  | r2 => 1
  | r3 => 2
  | r4 => 3
  end.

Definition index_to_rank (i : nat) : RankName :=
  match i with
  | 0 => r1
  | 1 => r2
  | 2 => r3
  | 3 => r4
  | _ => r4
  end.

Definition file_index (fn : FileName) : nat :=
  match fn with
  | fa => 0
  | fb => 1
  | fc => 2
  | fd => 3
  end.

Definition index_to_file (i : nat) : FileName :=
  match i with
  | 0 => fa
  | 1 => fb
  | 2 => fc
  | 3 => fd
  | _ => fd
  end.

Definition get_file (pp : PiecePlacements) (fn : FileName) : File :=
  match pp with
  | Files a b c d =>
    match fn with
    | fa => a
    | fb => b
    | fc => c
    | fd => d
    end
  end.

Definition get_square (pp : PiecePlacements) (rn : RankName) (fn : FileName)
  : Square :=
  match (get_file pp fn) with
  | Squares s1 s2 s3 s4 =>
    match rn with
    | r1 => s1
    | r2 => s2
    | r3 => s3
    | r4 => s4
    end
  end.

Definition get_square_by_index (pp : PiecePlacements) (rn : nat) (fn : nat) : 
Square :=
  (get_square pp (index_to_rank rn) (index_to_file fn)).

Inductive SquareLocation : Type :=
  | Loc (rank : nat) (file : nat).

Definition rank_of_loc (loc : SquareLocation) :=
  match loc with
  | Loc rank _ => rank
  end.

Definition file_of_loc (loc : SquareLocation) :=
  match loc with
  | Loc _ file => file
  end.

Definition location_valid (loc : SquareLocation) : Prop :=
  match loc with Loc r f => r <= 3 /\ f <= 3 end.

Definition valid_locations := 
[Loc 0 0; Loc 0 1; Loc 0 2; Loc 0 3;
Loc 1 0; Loc 1 1; Loc 1 2; Loc 1 3;
Loc 2 0; Loc 2 1; Loc 2 2; Loc 2 3;
Loc 3 0; Loc 3 1; Loc 3 2; Loc 3 3].


Fixpoint find_piece (pp : PiecePlacements) (c : Color) (p : Piece) 
(locs : list SquareLocation) : list SquareLocation :=
  match locs with
  | [] => []
  | (Loc r f)::rlocs => if (eqSq (get_square_by_index pp r f) (Occupied c p)) 
    then (Loc r f)::(find_piece pp c p rlocs)
    else find_piece pp c p rlocs
  end.

Definition find_king (pp : PiecePlacements) (c : Color) := 
  find_piece pp c King valid_locations.

(* Proofs *)

Lemma find_piece_correct : forall pp c p loc locs,
  In loc (find_piece pp c p locs) <-> 
  In loc locs /\ (get_square_by_index pp (rank_of_loc loc) (file_of_loc loc)) 
  = Occupied c p.
Admitted.

Lemma valid_squares_nec : forall loc,
  location_valid loc ->
  In loc valid_locations.
Admitted.

Lemma valid_squares_suf : forall loc,
  In loc valid_locations -> location_valid loc.
Admitted.

Lemma find_king_correct : forall pp c king_rank king_file,
  In (Loc king_rank king_file) (find_king pp c) <-> 
  (location_valid (Loc king_rank king_file)) /\
  (get_square_by_index pp king_rank king_file = 
  Occupied c King).
Proof.
  intros pp c king_rank king_file. split; intros H.
  - unfold find_king in *. apply find_piece_correct in H. HdAnd. split; auto.
    apply valid_squares_suf in H. auto.
  - unfold find_king in *. HdAnd. apply valid_squares_nec in H. 
    apply find_piece_correct. split; auto.
Qed.
