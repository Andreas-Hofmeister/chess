Require Import List.
Require Import Nat.
From Coq Require Export Lia.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.

(** Definitions **)

Inductive MakeFromToMove (before : PiecePlacements) (from to : SquareLocation) 
(after : PiecePlacements) : Prop := 
  | MakeFromToMoveIff :
    location_valid from -> location_valid to -> from <> to ->
    get_square_by_location before from = get_square_by_location after to ->
    get_square_by_location after from = Empty ->
    (forall loc, location_valid loc -> loc <> from -> loc <> to ->
      get_square_by_location before loc = get_square_by_location after loc) ->
    MakeFromToMove before from to after.

Definition make_from_to_move (before : PiecePlacements) 
(from to : SquareLocation) : PiecePlacements :=
  match from, to with
  | Loc from_r from_f, Loc to_r to_f =>
    let from_emptied := set_square_by_index before from_r from_f Empty in
    set_square_by_index from_emptied to_r to_f 
      (get_square_by_index before from_r from_f)
  end.

Definition is_en_passant_step (from to : SquareLocation) (c : Color) :=
  match c,from,to with
  | White, Loc from_r from_f,Loc to_r to_f  => 
    ((from_r =? 4) && (to_r =? 5) && ((to_f =? from_f - 1) || (to_f =? from_f + 1)))%bool
  | Black, Loc from_r from_f,Loc to_r to_f =>
    ((from_r =? 3) && (to_r =? 2) && ((to_f =? from_f - 1) || (to_f =? from_f + 1)))%bool
  end.

Definition en_passant_capture_rank (c : Color) :=
  match c with
  | White => 4
  | Black => 3
  end.

Inductive MakeEnPassantMove (before : PiecePlacements) 
(from to : SquareLocation) (after : PiecePlacements) : Prop :=
  | MakeEnPassantMoveIff : forall c captured_loc,
    is_en_passant_step from to c = true ->
    get_square_by_location before from = get_square_by_location after to ->
    get_square_by_location after from = Empty ->
    captured_loc = Loc (en_passant_capture_rank c) (file_of_loc to) ->
    get_square_by_location after captured_loc = Empty ->
    (forall loc, location_valid loc -> loc <> from -> loc <> to ->
      loc <> captured_loc ->
      get_square_by_location before loc = get_square_by_location after loc) ->
    MakeEnPassantMove before from to after.

Definition remove_en_passant_capture (pp : PiecePlacements)
(from to : SquareLocation) :=
  match from,to with
  | Loc from_r from_f, Loc to_r to_f =>
    if (from_r =? (en_passant_capture_rank White)) 
    then (set_square_by_index pp (en_passant_capture_rank White) to_f
          Empty)
    else if (from_r =? (en_passant_capture_rank Black))
    then (set_square_by_index pp (en_passant_capture_rank Black) to_f
          Empty)
    else pp
  end.
    

Definition make_en_passant_move (before : PiecePlacements)
(from to : SquareLocation) : PiecePlacements :=
  remove_en_passant_capture (make_from_to_move before from to) from to.

(** Proofs **)

Lemma make_from_to_move_sound : forall before from to after,
  location_valid from -> location_valid to -> from <> to ->
  make_from_to_move before from to = after -> 
  MakeFromToMove before from to after.
Proof.
  intros before from to after Hvfrom Hvto Huneq. unfold make_from_to_move. 
  intros H. repeat DHmatch. apply location_valid_iff in Hvfrom as Hvfrom2.
  apply location_valid_iff in Hvto as Hvto2. apply MakeFromToMoveIff; auto.
  - unfold get_square_by_location. rewrite <- H. 
    rewrite get_set_square_by_index_correct; auto.
  - unfold get_square_by_location. rewrite <- H. 
    rewrite get_set_square_by_index_correct2; auto.
    + rewrite get_set_square_by_index_correct; auto.
    + apply neq_Loc. auto.
  - intros loc Hlocv Hlocuneq1 Hlocuneq2. unfold get_square_by_location.
    repeat DGmatch. apply location_valid_iff in Hlocv as Hlocv2. 
    rewrite <- H. rewrite get_set_square_by_index_correct2; 
    auto. rewrite get_set_square_by_index_correct2; auto.
    all: apply neq_Loc; auto.
Qed.

Lemma make_from_to_move_complete : forall before from to after,
  MakeFromToMove before from to after ->
  make_from_to_move before from to = after.
Proof.
  intros before from to after H. inversion H; subst. 
  apply piece_placements_eq_iff. intros. destruct from eqn:?E.
  destruct to eqn:?E. apply location_valid_iff in H0 as Hvfrom.
  apply location_valid_iff in H1 as Hvto. destruct (eqSL loc from) eqn:?E.
  - rewrite eqSL_iff in *. subst. rewrite H4. unfold make_from_to_move.
    repeat DGmatch. unfold get_square_by_location.
    rewrite get_set_square_by_index_correct2; try apply neq_Loc; auto.
    rewrite get_set_square_by_index_correct; auto.
  - destruct (eqSL loc to) eqn:?E.
    + rewrite eqSL_iff in *. subst. rewrite <- H3. unfold make_from_to_move.
      unfold get_square_by_location. rewrite get_set_square_by_index_correct; 
      auto.
    + assert (loc <> from). { intros C. rewrite <- eqSL_iff in *. 
        rewrite C in *. discriminate. }
      assert (loc <> to). { intros C. rewrite <- eqSL_iff in *. 
        rewrite C in *. discriminate. }
      rewrite <- H5; subst; auto. unfold make_from_to_move. 
      destruct loc eqn:?E. apply location_valid_iff in H6 as Hvloc. 
      unfold get_square_by_location. rewrite get_set_square_by_index_correct2;
      try apply neq_Loc; auto. rewrite get_set_square_by_index_correct2;
      try apply neq_Loc; auto. 
Qed.


