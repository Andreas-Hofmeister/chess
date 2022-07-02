Require Import List.
Require Import Nat.
From CHESS Require Export movement_basics.
From CHESS Require Export pawn_moves.
From CHESS Require Export rook_moves.
From CHESS Require Export bishop_moves.
From CHESS Require Export knight_moves.
From CHESS Require Export queen_moves.
From CHESS Require Export king_moves.

(* Definition of when a player attacks a square or a piece *)

(** Definitions **)

Inductive APieceCanMakeMove (pos : Position) : Color -> Move -> Prop := 
  | MoveCanBeMadeByPawn : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Pawn ->
    PawnCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByRook : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Rook ->
    RookCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByBishop : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Bishop ->
    BishopCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByKnight : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Knight ->
    KnightCanMakeMove pos from color  move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByQueen : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color Queen ->
    QueenCanMakeMove pos from color move -> APieceCanMakeMove pos color move
  | MoveCanBeMadeByKing : forall color move from,
    from = fromOfMove move -> IsOccupiedBy pos from color King ->
    KingCanMakeMove pos from color move -> APieceCanMakeMove pos color move.

Inductive AttacksEmptySquare (pos : Position) 
: Color -> SquareLocation -> Prop :=
  | AttacksEmptySquare_iff : forall color loc move,
    loc = toOfMove move -> IsMoveToEmptySquare move ->
    APieceCanMakeMove pos color move -> AttacksEmptySquare pos color loc.

Inductive AttacksOccupiedSquare (pos : Position)
  : Color -> SquareLocation -> Prop :=
  | AttacksOccupiedSquare_iff : forall color loc move,
    loc = toOfMove move -> IsCapturingMove move ->
    APieceCanMakeMove pos color move -> AttacksOccupiedSquare pos color loc.

Definition AttacksSquare (pos : Position) (c : Color) (loc : SquareLocation) 
: Prop := 
  AttacksEmptySquare pos c loc \/ AttacksOccupiedSquare pos c loc.

Definition moves_by_player_from_square (pos : Position) (c : Color) 
(loc : SquareLocation) : (list Move) :=
  match pos, loc with
  | Posn pp _ _ _, Loc r f 
    => match get_square_by_index pp r f with
      | Empty => []
      | Occupied sc p => 
        if ceq c sc then match p with
        | Pawn => pawn_moves loc c pos
        | Rook => rook_moves loc c pos
        | Bishop => bishop_moves loc c pos
        | Knight => knight_moves loc c pos
        | Queen => queen_moves loc c pos
        | King => king_moves loc c pos
        end else []
      end
  end.

Definition moves_by_player (pos : Position) (c : Color) : (list Move) :=
  append_forall (fun sq => moves_by_player_from_square pos c sq) 
  valid_locations.

Definition is_move_that_attacks_empty_square (loc : SquareLocation) 
(move : Move) : bool :=
  (is_move_to_empty_square move) && (locations_equal (toOfMove move) loc).

Definition attacks_empty_square (pos : Position) (c : Color) 
(loc : SquareLocation) : bool :=
  exists_in (moves_by_player pos c) (is_move_that_attacks_empty_square loc).

Definition is_move_that_attacks_occupied_square (loc : SquareLocation) 
(move : Move) : bool :=
  (is_capturing_move move) && (locations_equal (toOfMove move) loc).

Definition attacks_occupied_square (pos : Position) (c : Color) 
(loc : SquareLocation) : bool :=
  exists_in (moves_by_player pos c) (is_move_that_attacks_occupied_square loc).

Definition attacks_square (pos : Position) (c : Color) (loc : SquareLocation)
: bool :=
  (attacks_empty_square pos c loc) || (attacks_occupied_square pos c loc).

(** Proofs **)

Lemma a_piece_can_make_move_from_valid : forall pos c move,
  APieceCanMakeMove pos c move -> location_valid (fromOfMove move).
Proof.
  intros pos c move Hcan. inversion Hcan; subst; inversion H1; auto.
  - inversion H; auto.
  - inversion H; auto.
Qed.

Lemma a_piece_can_make_move_to_valid : forall pos c move,
  APieceCanMakeMove pos c move -> location_valid (toOfMove move).
Proof.
  intros pos c move Hcan. inversion Hcan; subst; inversion H1; auto.
  - simpl. subst. simpl. destruct c eqn:?E; simpl; simpl in H3; simpl in H2;
    rewrite H2 in H3; simpl in H3; lia.
  - inversion H; auto.
  - inversion H; auto. 
Qed.

Lemma a_piece_can_make_move_from_occupied : forall pos c move,
  APieceCanMakeMove pos c move -> 
  is_square_empty (fromOfMove move) (get_piece_placements pos) = false.
Proof.
  intros pos c move Hcan. inversion Hcan; subst; inversion H0; subst; simpl;
  unfold is_square_empty_rank_file; rewrite H3; auto.
Qed.

Lemma moves_by_player_from_square_sound : forall pos c loc move,
  location_valid loc ->
  In move (moves_by_player_from_square pos c loc) ->
  APieceCanMakeMove pos c move.
Proof.
  intros pos c loc move Hv Hin. unfold moves_by_player_from_square in *.
  repeat DHmatch; try HinNil; rewrite ceq_eq in *.
  - apply pawn_moves_from in Hin as Hfrom. subst. 
    eapply MoveCanBeMadeByPawn; eauto; rewrite Hfrom.
    + econstructor; eauto.
    + apply pawn_moves_sound. auto.
  - apply rook_moves_from in Hin as Hfrom. subst.
    eapply MoveCanBeMadeByRook; eauto; rewrite Hfrom.
    + econstructor; eauto.
    + apply rook_moves_sound; auto.
  - apply knight_moves_from in Hin as Hfrom. subst.
    eapply MoveCanBeMadeByKnight; eauto; rewrite Hfrom.
    + econstructor; eauto.
    + apply knight_moves_sound; auto.
  - apply bishop_moves_from in Hin as Hfrom. subst.
    eapply MoveCanBeMadeByBishop; eauto; rewrite Hfrom.
    + econstructor; eauto.
    + apply bishop_moves_sound; auto.
  - apply queen_moves_from in Hin as Hfrom. subst.
    eapply MoveCanBeMadeByQueen; eauto; rewrite Hfrom.
    + econstructor; eauto.
    + apply queen_moves_sound; auto.
  - apply king_moves_from in Hin as Hfrom. subst.
    eapply MoveCanBeMadeByKing; eauto; rewrite Hfrom.
    + econstructor; eauto.
    + apply king_moves_sound; auto.
Qed.

Lemma moves_by_player_sound : forall pos c move,
  In move (moves_by_player pos c) -> APieceCanMakeMove pos c move. 
Proof.
  intros pos c move Hin. unfold moves_by_player in Hin. 
  apply in_append_forall_suf in Hin. destruct Hin as [a [Hv Hin]].
  eapply moves_by_player_from_square_sound; eauto. rewrite valid_squares.
  auto.
Qed.

Lemma moves_by_player_complete : forall pos c move,
  APieceCanMakeMove pos c move -> In move (moves_by_player pos c).
Proof.
  intros pos c move Hcan. unfold moves_by_player. 
  unfold moves_by_player_from_square.
  specialize (a_piece_can_make_move_from_valid pos c move Hcan) as Hv.
  specialize (a_piece_can_make_move_from_occupied pos c move Hcan) as Hocc.
  unfold is_square_empty in Hocc. DHmatch. 
  unfold is_square_empty_rank_file in Hocc.
  apply in_append_forall_nec with (a:=fromOfMove move). apply valid_squares.
  rewrite E. auto. inversion Hcan; subst; inversion H0; subst; DGmatch; 
  simpl in *; rewrite H3; rewrite ceq_refl.
  - apply pawn_moves_complete. rewrite H. auto.
  - apply rook_moves_complete. rewrite H. auto.
  - apply bishop_moves_complete. rewrite H. auto.
  - apply knight_moves_complete. rewrite H. auto.
  - apply queen_moves_complete. rewrite H. auto.
  - apply king_moves_complete. rewrite H. auto.
Qed.

Lemma is_move_that_attacks_empty_square_iff : forall loc move,
  is_move_that_attacks_empty_square loc move = true <->
  (loc = toOfMove move /\ IsMoveToEmptySquare move).
Proof.
  intros loc move. split; intros H.
  - unfold is_move_that_attacks_empty_square in *. Hb2p. HdAnd.
    split. rewrite locations_equal_iff in H0. auto. 
    apply is_move_to_empty_square_correct. auto.
  - HdAnd. subst. unfold is_move_that_attacks_empty_square. Gb2p. split.
    apply is_move_to_empty_square_correct. auto. rewrite locations_equal_iff.
    auto.
Qed.

Lemma is_move_that_attacks_occupied_square_iff : forall loc move,
  is_move_that_attacks_occupied_square loc move = true <->
  (loc = toOfMove move /\ IsCapturingMove move).
Proof.
  intros loc move. split; intros H.
  - unfold is_move_that_attacks_occupied_square in *. Hb2p. HdAnd.
    split. rewrite locations_equal_iff in H0. auto. 
    apply is_capturing_move_correct. auto.
  - HdAnd. subst. unfold is_move_that_attacks_occupied_square. Gb2p. split.
    apply is_capturing_move_correct. auto. rewrite locations_equal_iff.
    auto.
Qed.

Lemma attacks_empty_square_correct : forall pos c loc,
  attacks_empty_square pos c loc = true <-> AttacksEmptySquare pos c loc.
Proof.
  intros pos c loc. split; intros H.
  - unfold attacks_empty_square in *. rewrite exists_in_iff in H. 
    destruct H as [x [Hmove HtoEmpty]]. apply moves_by_player_sound in Hmove.
    rewrite is_move_that_attacks_empty_square_iff in *. HdAnd.
    apply AttacksEmptySquare_iff with (move:=x); auto.
  - unfold attacks_empty_square. rewrite exists_in_iff. inversion H; subst.
    exists move. split.
    + apply moves_by_player_complete. auto.
    + rewrite is_move_that_attacks_empty_square_iff. auto.
Qed.

Lemma attacks_occupied_square_correct : forall pos c loc,
  attacks_occupied_square pos c loc = true <-> AttacksOccupiedSquare pos c loc.
Proof.
  intros pos c loc. split; intros H.
  - unfold attacks_occupied_square in *. rewrite exists_in_iff in H. 
    destruct H as [x [Hmove HtoEmpty]]. apply moves_by_player_sound in Hmove.
    rewrite is_move_that_attacks_occupied_square_iff in *. HdAnd.
    apply AttacksOccupiedSquare_iff with (move:=x); auto.
  - unfold attacks_occupied_square. rewrite exists_in_iff. inversion H; subst.
    exists move. split.
    + apply moves_by_player_complete. auto.
    + rewrite is_move_that_attacks_occupied_square_iff. auto.
Qed.

Lemma attacks_square_correct : forall pos c loc,
  attacks_square pos c loc = true <-> AttacksSquare pos c loc.
Proof.
  intros pos c loc. split; intros H.
  - unfold attacks_square in H. Hb2p. 
    rewrite attacks_occupied_square_correct in *. 
    rewrite attacks_empty_square_correct in *. auto.
  - unfold attacks_square. Gb2p.
    rewrite attacks_occupied_square_correct. 
    rewrite attacks_empty_square_correct. auto.
Qed.
