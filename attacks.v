Require Import List.
Require Import Nat.
From CHESS Require Export movement_basics.
From CHESS Require Export pawn_moves.
From CHESS Require Export rook_moves.
From CHESS Require Export bishop_moves.
From CHESS Require Export knight_moves.
From CHESS Require Export queen_moves.
From CHESS Require Export king_moves.

(* Definition of when a piece attacks a square or another piece *)

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

Definition Attacks (pos : Position) (c : Color) (loc : SquareLocation) : Prop
  := AttacksEmptySquare pos c loc \/ AttacksOccupiedSquare pos c loc.

Definition moves_by_player_from_square (pos : Position) (c : Color) 
(loc : SquareLocation) : (list Move) :=
  match pos, loc with
  | Posn pp _ _ , Loc r f 
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

(** Proofs **)

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
  - admit.
  - admit.
  - admit.
Admitted.

Lemma moves_by_player_sound : forall pos c move,
  In move (moves_by_player pos c) -> APieceCanMakeMove pos c move. 
Proof.
  intros pos c move Hin. unfold moves_by_player in Hin. 
  apply in_append_forall_suf in Hin. destruct Hin as [a [Hv Hin]].
Admitted.

