Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.

(*** Definitions ***)

Inductive KingCanMakeMove (pos : Position) : 
  SquareLocation -> Color -> Move -> Prop :=
  | KingCanMove : forall from to pp c pos_c dstep cavl,
    location_valid from -> location_valid to ->
    pos = Posn pp pos_c dstep cavl ->
    SquaresAdjacent from to -> is_square_empty to pp = true ->
    KingCanMakeMove pos from c (FromTo from to)
  | KingCanCapture : forall from to pp c pos_c dstep cavl,
    location_valid from -> location_valid to ->
    pos = Posn pp pos_c dstep cavl ->
    SquaresAdjacent from to -> 
    is_square_occupied_by_enemy_piece to pp c = true ->
    KingCanMakeMove pos from c (Capture from to). 

Definition king_moves_to_empty_square (loc : SquareLocation) (c : Color)
(pos : Position) : (list Move) :=
  match pos with
  | Posn pp _ _ _ => map (fun to => (FromTo loc to)) 
  (filter (fun sq => is_square_empty sq pp) (adjacent_squares loc))
  end.

Definition king_captures (loc : SquareLocation) (c : Color)
(pos : Position) : (list Move) :=
  match pos with
  | Posn pp _ _ _ => map (fun to => (Capture loc to)) 
  (filter (fun sq => is_square_occupied_by_enemy_piece sq pp c) 
  (adjacent_squares loc))
  end.

Definition king_moves (loc : SquareLocation) (c : Color) (pos : Position)
: (list Move) :=
  (king_moves_to_empty_square loc c pos) ++ (king_captures loc c pos).

(*** Proofs ***)

Lemma king_moves_from : forall l c pos move,
  In move (king_moves l c pos) -> fromOfMove move = l.
Proof.
  intros l c pos move Hin. unfold king_moves in *. repeat in_app_to_or.
  - unfold king_moves_to_empty_square in *. repeat DHmatch.
    rewrite in_map_iff in Hin. destruct Hin as [x [Hm _]]. subst. simpl. auto.
  - unfold king_captures in *. repeat DHmatch.
    rewrite in_map_iff in Hin. destruct Hin as [x [Hm _]]. subst. simpl. auto.
Qed.

Lemma king_moves_to_empty_square_sound : forall loc c pos move,
  location_valid loc ->
  In move (king_moves_to_empty_square loc c pos) 
  -> KingCanMakeMove pos loc c move.
Proof.
  intros loc c pos move Hv Hin. unfold king_moves_to_empty_square in *.
  DHmatch. rewrite in_map_iff in Hin. destruct Hin as [x [Hm Hin]].
  rewrite filter_In in *. destruct Hin as [Hin Hempty]. subst.
  eapply KingCanMove; eauto. eapply adjacent_squares_valid. eauto.
  eapply adjacent_squares_correct. eauto.
Qed.

Lemma king_captures_sound : forall loc c pos move,
  location_valid loc ->
  In move (king_captures loc c pos) -> KingCanMakeMove pos loc c move.
Proof.
  intros loc c pos move Hv Hin. unfold king_captures in *.
  DHmatch. rewrite in_map_iff in Hin. destruct Hin as [x [Hm Hin]].
  rewrite filter_In in *. destruct Hin as [Hin Hempty]. subst.
  eapply KingCanCapture; eauto. eapply adjacent_squares_valid. eauto.
  eapply adjacent_squares_correct. eauto.
Qed.

Lemma king_moves_sound : forall loc c pos move,
  location_valid loc -> 
  In move (king_moves loc c pos) -> KingCanMakeMove pos loc c move.
Proof.
  intros loc c pos move Hv Hin. unfold king_moves in *. in_app_to_or. HdOr.
  - apply king_moves_to_empty_square_sound; auto.
  - apply king_captures_sound; auto.
Qed.

Lemma king_moves_complete : forall loc c pos move,
  KingCanMakeMove pos loc c move -> In move (king_moves loc c pos).
Proof.
  intros loc c pos move Hcan. inversion Hcan; subst; unfold king_moves; 
  in_app_to_or.
  - left. simpl. rewrite in_map_iff. exists to. rewrite filter_In. 
    repeat split; auto. apply adjacent_squares_correct; auto.
  - right. simpl. rewrite in_map_iff. exists to. rewrite filter_In.
    repeat split; auto. apply adjacent_squares_correct; auto.
Qed.

