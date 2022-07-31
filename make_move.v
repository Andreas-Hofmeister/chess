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
    ((from_r =? 4) && (to_r =? 5) && (difference from_f to_f =? 1))%bool
  | Black, Loc from_r from_f,Loc to_r to_f =>
    ((from_r =? 3) && (to_r =? 2) && (difference from_f to_f =? 1))%bool
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

Definition promotion_rank (c : Color) :=
  match c with
  | White => 7
  | Black => 0
  end.

Inductive MakePromotionMove (before : PiecePlacements) 
(from to : SquareLocation) (piece : Piece) (after : PiecePlacements) : Prop :=
  | MakePromotionMoveIff : forall c,
    from <> to ->
    rank_of_loc to = promotion_rank c ->
    get_square_by_location after from = Empty ->
    get_square_by_location after to = Occupied c piece ->
    (forall loc, location_valid loc -> loc <> from -> loc <> to ->
      get_square_by_location after loc = get_square_by_location before loc) ->
    MakePromotionMove before from to piece after.

Fixpoint pp_from_map (f : SquareLocation -> Square) 
  (locs : list SquareLocation) (pp_acc : PiecePlacements) :=
  match locs with
  | [] => pp_acc
  | (Loc rnk fl)::rest => 
    set_square_by_index (pp_from_map f rest pp_acc) rnk fl (f (Loc rnk fl))
  end.

Definition make_promotion_move_map (before : PiecePlacements)
(from to : SquareLocation) (c : Color) (piece : Piece) :=
  fun loc =>
  if (locations_equal loc from) then Empty else
  if (locations_equal loc to) then (Occupied c piece) 
  else (get_square_by_location before loc).

Definition make_promotion_move (before : PiecePlacements) 
(from to : SquareLocation) (piece : Piece) :=
  if (rank_of_loc to =? promotion_rank White)
  then (pp_from_map (make_promotion_move_map before from to White piece)
          valid_locations empty_pp)
  else if (rank_of_loc to =? promotion_rank Black)
  then (pp_from_map (make_promotion_move_map before from to Black piece)
          valid_locations empty_pp)
  else before.

Inductive MakeCastlingMove (before : PiecePlacements) (c : Color) 
(ct : CastlingType) (after : PiecePlacements) : Prop  :=
  | MakeWhiteKingsideCastlingMove : 
    c = White -> ct = KingSide ->
    get_square_by_location after (Loc 0 4) = Empty ->
    get_square_by_location after (Loc 0 6) = Occupied White King ->
    get_square_by_location after (Loc 0 7) = Empty ->
    get_square_by_location after (Loc 0 5) = Occupied White Rook ->
    (forall loc, loc <> (Loc 0 4) -> loc <> (Loc 0 5) -> loc <> (Loc 0 6) ->
      loc <> (Loc 0 7) -> 
      get_square_by_location after loc = get_square_by_location before loc) ->
    MakeCastlingMove before c ct after
  | MakeWhiteQueensideCastlingMove : 
    c = White -> ct = QueenSide ->
    get_square_by_location after (Loc 0 4) = Empty ->
    get_square_by_location after (Loc 0 2) = Occupied White King ->
    get_square_by_location after (Loc 0 0) = Empty ->
    get_square_by_location after (Loc 0 3) = Occupied White Rook ->
    (forall loc, loc <> (Loc 0 4) -> loc <> (Loc 0 2) -> loc <> (Loc 0 0) ->
      loc <> (Loc 0 3) -> 
      get_square_by_location after loc = get_square_by_location before loc) ->
    MakeCastlingMove before c ct after
  | MakeBlackKingsideCastlingMove : 
    c = Black -> ct = KingSide ->
    get_square_by_location after (Loc 7 4) = Empty ->
    get_square_by_location after (Loc 7 6) = Occupied White King ->
    get_square_by_location after (Loc 7 7) = Empty ->
    get_square_by_location after (Loc 7 5) = Occupied White Rook ->
    (forall loc, loc <> (Loc 7 4) -> loc <> (Loc 7 5) -> loc <> (Loc 7 6) ->
      loc <> (Loc 7 7) -> 
      get_square_by_location after loc = get_square_by_location before loc) ->
    MakeCastlingMove before c ct after
  | MakeBlackQueensideCastlingMove : 
    c = Black -> ct = QueenSide ->
    get_square_by_location after (Loc 7 4) = Empty ->
    get_square_by_location after (Loc 7 2) = Occupied White King ->
    get_square_by_location after (Loc 7 0) = Empty ->
    get_square_by_location after (Loc 7 3) = Occupied White Rook ->
    (forall loc, loc <> (Loc 7 4) -> loc <> (Loc 7 2) -> loc <> (Loc 7 0) ->
      loc <> (Loc 7 3) -> 
      get_square_by_location after loc = get_square_by_location before loc) ->
    MakeCastlingMove before c ct after.

Definition make_white_kingside_castling_move_map (before : PiecePlacements)
:=
  fun loc =>
  if (locations_equal loc (Loc 0 4)) then Empty else
  if (locations_equal loc (Loc 0 6)) then (Occupied White King) else
  if (locations_equal loc (Loc 0 7)) then Empty else
  if (locations_equal loc (Loc 0 5)) then (Occupied White Rook)
  else (get_square_by_location before loc).

Definition make_white_queenside_castling_move_map (before : PiecePlacements)
:=
  fun loc =>
  if (locations_equal loc (Loc 0 4)) then Empty else
  if (locations_equal loc (Loc 0 2)) then (Occupied White King) else
  if (locations_equal loc (Loc 0 0)) then Empty else
  if (locations_equal loc (Loc 0 3)) then (Occupied White Rook)
  else (get_square_by_location before loc).

Definition make_black_kingside_castling_move_map (before : PiecePlacements)
:=
  fun loc =>
  if (locations_equal loc (Loc 7 4)) then Empty else
  if (locations_equal loc (Loc 7 6)) then (Occupied White King) else
  if (locations_equal loc (Loc 7 7)) then Empty else
  if (locations_equal loc (Loc 7 5)) then (Occupied White Rook)
  else (get_square_by_location before loc).

Definition make_black_queenside_castling_move_map (before : PiecePlacements)
:=
  fun loc =>
  if (locations_equal loc (Loc 7 4)) then Empty else
  if (locations_equal loc (Loc 7 2)) then (Occupied White King) else
  if (locations_equal loc (Loc 7 0)) then Empty else
  if (locations_equal loc (Loc 7 3)) then (Occupied White Rook)
  else (get_square_by_location before loc).

Definition make_castling_move (before : PiecePlacements) (c : Color)
(ct : CastlingType) :=
  if (ceq c White) then
    if (ctypeeq ct KingSide) 
    then (pp_from_map (make_white_kingside_castling_move_map before)
          valid_locations empty_pp)
    else (pp_from_map (make_white_queenside_castling_move_map before)
          valid_locations empty_pp)
  else
    if (ctypeeq ct KingSide) 
    then (pp_from_map (make_black_kingside_castling_move_map before)
          valid_locations empty_pp)
    else (pp_from_map (make_black_queenside_castling_move_map before)
          valid_locations empty_pp).

Definition is_from_to_or_capture (move : Move) : bool :=
  match move with
  | FromTo _ _ => true
  | Capture _ _ => true
  | _ => false
  end.

Definition is_pawn_bishop_knight_queen (piece : Piece) : bool :=
  match piece with
  | Queen => true
  | Knight => true
  | Pawn => true
  | Bishop => true
  | _ => false
  end.

Definition initial_queenside_rook_location (c : Color) :=
  match c with
  | White => Loc 0 0
  | Black => Loc 7 0
  end.

Definition initial_kingside_rook_location (c : Color) :=
  match c with
  | White => Loc 0 7
  | Black => Loc 7 7
  end.
Check remove.
Lemma cavl_dec : (forall x y : CastlingAvailability, {x = y} + {x <> y}).
Proof.
  intros x y. destruct x eqn:Ex; destruct y eqn:Ey.

Inductive MakeMove (before : Position) (move : Move) : Position -> Prop
:=
  | MakeSimpleFromToOrCaptureMove : forall pp c pds cavl piece pp_after,
    before = Posn pp c pds cavl ->
    is_from_to_or_capture move = true ->
    get_square_by_location pp (fromOfMove move) = Occupied c piece ->
    is_pawn_bishop_knight_queen piece = true ->
    MakeFromToMove pp (fromOfMove move) (toOfMove move) pp_after ->
    MakeMove before move (Posn pp_after (opponent_of c) None cavl)
  | MakeRookMove : forall,
    before = Posn pp c pds cavl ->
    get_square_by_location pp (fromOfMove move) = Occupied c Rook ->
    (initial_queenside_rook_location c = fromOfMove move /\
     In (Cavl QueenSide c) cavl -> after_cavl = 
    

(** Proofs **)

Lemma pp_from_map_correct : forall locs loc f pp_acc,
  (forall l, In l locs -> location_valid l) -> In loc locs ->
  get_square_by_location (pp_from_map f locs pp_acc) loc = f loc.
Proof.
  induction locs.
  - intros. HinNil.
  - intros loc f pp_acc Hv Hin. inversion Hin; subst.
    + simpl. DGmatch. unfold get_square_by_location. 
      apply get_set_square_by_index_correct. rewrite <- location_valid_iff.
      auto.
    + simpl. DGmatch. destruct (locations_equal loc (Loc rank file)) eqn:Eeq.
      * rewrite locations_equal_iff in Eeq. subst. 
        unfold get_square_by_location. apply get_set_square_by_index_correct. 
        rewrite <- location_valid_iff. auto.
      * assert (Hneq: loc <> (Loc rank file)). { intros C. 
          rewrite <- locations_equal_iff in C. rewrite C in Eeq. discriminate.
        }
        destruct loc eqn:Eloc. apply neq_Loc in Hneq.
        unfold get_square_by_location. 
        assert (Obv: In (Loc rank file) (Loc rank file :: locs)). {
          apply in_eq.
        }
        rewrite get_set_square_by_index_correct2; try lia;
        try rewrite <- location_valid_iff; auto.
        assert (Obv2: forall l, In l locs -> location_valid l). { intros.
          apply Hv. apply in_cons. auto.
        }
        specialize (IHlocs (Loc rank0 file0) f pp_acc Obv2 H) as Hind.
        unfold get_square_by_location in *. auto.
Qed.

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

Lemma make_from_to_move_sound2 : forall before from to,
  location_valid from -> location_valid to -> from <> to ->
  MakeFromToMove before from to (make_from_to_move before from to).
Proof.
  intros. apply make_from_to_move_sound; auto.
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

Lemma remove_en_passant_capture_sound : forall c from to before after,
  location_valid to ->
  is_en_passant_step from to c = true ->
  (remove_en_passant_capture before from to = after ->
  (get_square_by_location after (Loc (en_passant_capture_rank c) 
    (file_of_loc to))) = Empty /\
  (forall loc, location_valid loc -> 
    loc <> (Loc (en_passant_capture_rank c) (file_of_loc to)) ->
    get_square_by_location after loc = get_square_by_location before loc)).
Proof.
  intros c from to before after Hto_v Heps.
  unfold remove_en_passant_capture. destruct c eqn:Hc.
  - unfold is_en_passant_step in Heps. repeat DHmatch. repeat (Hb2p; HdAnd).
    repeat Hb2p. simpl. repeat HdAnd. rewrite Heps. intros H.
    rewrite location_valid_iff in Hto_v. unfold indices_valid in *.
    repeat Hb2p. HdAnd. split.
    + rewrite <- H. apply get_set_square_by_index_correct.
      unfold indices_valid. Gb2p. split; auto.
    + intros loc Hlocv Hlocuneq. unfold get_square_by_location.
      repeat DGmatch. rewrite <- H. apply get_set_square_by_index_correct2.
      * unfold indices_valid. Gb2p. split; auto.
      * rewrite location_valid_iff in Hlocv. auto.
      * apply neq_Loc. auto.
  - unfold is_en_passant_step in Heps. repeat DHmatch. repeat (Hb2p; HdAnd).
    repeat Hb2p. simpl. repeat HdAnd. replace (rank =? 4) with false; 
    try symmetry; try Gb2p; try repeat Hb2p; try lia. rewrite Heps. intros H.
    rewrite location_valid_iff in Hto_v. unfold indices_valid in *.
    repeat Hb2p. HdAnd. simpl in H. split.
    + rewrite <- H. apply get_set_square_by_index_correct.
      unfold indices_valid. Gb2p. split; auto.
    + intros loc Hlocv Hlocuneq. unfold get_square_by_location.
      repeat DGmatch. rewrite <- H. apply get_set_square_by_index_correct2.
      * unfold indices_valid. Gb2p. split; auto.
      * rewrite location_valid_iff in Hlocv. auto.
      * apply neq_Loc. auto.
Qed.

Lemma remove_en_passant_capture_complete : forall c from to before after,
  location_valid to ->
  is_en_passant_step from to c = true ->
  (get_square_by_location after (Loc (en_passant_capture_rank c) 
    (file_of_loc to))) = Empty /\
  (forall loc, location_valid loc -> 
    loc <> (Loc (en_passant_capture_rank c) (file_of_loc to)) ->
    get_square_by_location after loc = get_square_by_location before loc) ->
  remove_en_passant_capture before from to = after.
Proof.
  intros c from to before after Hto_v Heps. intros H.
  assert (Obv: remove_en_passant_capture before from to = 
    remove_en_passant_capture before from to). { auto. }
  specialize (remove_en_passant_capture_sound c from to before 
    (remove_en_passant_capture before from to) Hto_v Heps Obv) as 
    [Hrmeps_removed Hrmeps_rest]. destruct H as [Hremoved Hrest].
  apply piece_placements_eq_iff. intros loc Hlocv.
  destruct (locations_equal loc (Loc (en_passant_capture_rank c) 
    (file_of_loc to))) eqn:ELoceq.
  - rewrite locations_equal_iff in *. subst. rewrite Hrmeps_removed.
    rewrite Hremoved. auto.
  - assert (Hlocneq: loc <> Loc (en_passant_capture_rank c) (file_of_loc to)).
    { intros C. rewrite <- locations_equal_iff in *. rewrite C in *. 
      discriminate.
    }
    rewrite Hrmeps_rest; auto. rewrite Hrest; auto.
Qed.

Lemma to_uneq_en_passant_capture : forall from to c,
  is_en_passant_step from to c = true ->
  to <> Loc (en_passant_capture_rank c) (file_of_loc to).
Proof.
  intros from to c. unfold is_en_passant_step. repeat DGmatch.
  - intros H. repeat (Hb2p; try HdAnd). simpl. intros C. inversion C; subst.
    discriminate.
  - intros H. repeat (Hb2p; try HdAnd). simpl. intros C. inversion C; subst.
    discriminate.
Qed.

Lemma from_uneq_en_passant_capture : forall from to c,
  is_en_passant_step from to c = true ->
  from <> Loc (en_passant_capture_rank c) (file_of_loc to).
Proof.
  intros from to c. unfold is_en_passant_step. repeat DGmatch.
  - intros H. repeat (Hb2p; try HdAnd). simpl. intros C. inversion C; subst.
    unfold difference in *. DHif; Hb2p; lia.
  - intros H. repeat (Hb2p; try HdAnd). simpl. intros C. inversion C; subst.
    unfold difference in *. DHif; Hb2p; lia.
Qed.

Lemma en_passant_step_from_uneq_to : forall from to c,
  is_en_passant_step from to c = true ->
  from <> to.
Proof.
  intros from to c. unfold is_en_passant_step. repeat DGmatch.
  - intros H. repeat (Hb2p; try HdAnd). intros C. inversion C; subst.
    discriminate.
  - intros H. repeat (Hb2p; try HdAnd). intros C. inversion C; subst.
    discriminate.
Qed.

Lemma make_en_passant_move_sound : forall c from to before after,
  location_valid from -> location_valid to ->
  is_en_passant_step from to c = true ->
  make_en_passant_move before from to = after -> 
  MakeEnPassantMove before from to after.
Proof.
  intros c from to before after Hfrom_v Hto_v Heps. unfold make_en_passant_move.
  intros Hrm. 
  specialize (remove_en_passant_capture_sound c from to _ _ Hto_v Heps Hrm)
      as [Hremoved Hrest].
  specialize (en_passant_step_from_uneq_to _ _ _ Heps) as Hfromuneqto.
  assert (Obv: (make_from_to_move before from to) = 
    (make_from_to_move before from to)). { auto. }
  specialize (make_from_to_move_sound _ _ _ _ Hfrom_v Hto_v Hfromuneqto Obv)
      as Hmftsound.
  apply MakeEnPassantMoveIff with (c:=c) 
  (captured_loc:=Loc (en_passant_capture_rank c) (file_of_loc to)); auto.
  - specialize (to_uneq_en_passant_capture _ _ _ Heps) as Htouneq. 
    rewrite Hrest; auto. inversion Hmftsound. auto.
  - specialize (from_uneq_en_passant_capture _ _ _ Heps) as Hfromuneq.
    rewrite Hrest; auto. inversion Hmftsound. auto.
  - intros loc Hlocv Hlocuneqfrom Hlocuneqto Hlocuneqepc.
    rewrite Hrest; auto. inversion Hmftsound; auto.
Qed.

Lemma make_en_passant_move_complete : forall c from to before after,
  location_valid from -> location_valid to ->
  is_en_passant_step from to c = true ->
  MakeEnPassantMove before from to after ->
  make_en_passant_move before from to = after.
Proof.
  intros c from to before after Hfrom_v Hto_v Heps. intros H.
  inversion H. unfold make_en_passant_move. 
  apply remove_en_passant_capture_complete with (c:=c0); auto. rewrite <- H3.
  split; auto. intros loc Hlocvalid Hlocuneqcaploc.
  specialize (en_passant_step_from_uneq_to _ _ _ Heps) as Hfromuneqto.
  specialize (make_from_to_move_sound2 before from to Hfrom_v Hto_v 
    Hfromuneqto) as Hfromtosound.
  inversion Hfromtosound; subst.
  destruct (locations_equal loc from) eqn:Eloceqfrom.
  - rewrite locations_equal_iff in *. subst. rewrite H10. auto.
  - assert (Elocneqfrom: loc <> from). { intros C. 
      rewrite <- locations_equal_iff in C. rewrite C in *. discriminate.
    }
    destruct (locations_equal loc to) eqn:Eloceqto.
    + rewrite locations_equal_iff in *. subst. rewrite <- H9. auto.
    + assert (Elocneqto: loc <> to). { intros C. 
        rewrite <- locations_equal_iff in C. rewrite C in *. discriminate.
      }
      rewrite <- H11; auto. symmetry. apply H5; auto.
Qed.

Lemma make_promotion_move_map_correct : forall before from to c piece,
  (make_promotion_move_map before from to c piece) from = Empty /\
  (make_promotion_move_map before from to c piece) to = Occupied c piece /\
  (forall loc, loc <> from -> loc <> to -> 
    (make_promotion_move_map before from to c piece) loc = 
    (get_square_by_location before loc)).
Admitted.

Lemma make_promotion_move_sound : forall before from to piece c after,
  from <> to ->
  rank_of_loc to = promotion_rank c ->
  make_promotion_move before from to piece = after ->
  MakePromotionMove before from to piece after.
Admitted.

Lemma make_promotion_move_complete : forall before from to piece after,
  MakePromotionMove before from to piece after ->
  make_promotion_move before from to piece = after.
Admitted.

Lemma make_castling_move_sound : forall before c ct after,
  make_castling_move before c ct = after -> MakeCastlingMove before c ct after.
Admitted.

Lemma make_castling_move_complete : forall before c ct after,
  MakeCastlingMove before c ct after -> make_castling_move before c ct = after.
Admitted.


