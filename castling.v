Require Import List.
Require Import Nat.
From CHESS Require Export basics.
From CHESS Require Export attacks.
From CHESS Require Export check.

(** Definitions **)

Definition empty_castling_squares (c : Color) (t: CastlingType) :=
  match c,t with
  | White,QueenSide => [Loc 0 1; Loc 0 2; Loc 0 3]
  | White,KingSide => [Loc 0 5; Loc 0 6]
  | Black,QueenSide => [Loc 7 1; Loc 7 2; Loc 7 3]
  | Black,KingSide => [Loc 7 5; Loc 7 6]
  end.

Definition rook_castling_square (c : Color) (t : CastlingType) :=
  match c,t with
  | White,QueenSide => Loc 0 0
  | White,KingSide => Loc 0 7
  | Black,QueenSide => Loc 7 0
  | Black,KingSide => Loc 7 7
  end.

Definition king_castling_square (c : Color) :=
  match c with
  | White => Loc 0 4
  | Black => Loc 7 4
  end.

Inductive CanMakeCastlingMove (pos : Position) : Color -> Move -> Prop :=
  | CanCastleIff : forall pp pos_c dstep cavl c ctype,
    pos = Posn pp pos_c dstep cavl -> In (Cavl ctype c) cavl ->
    (forall l, In l (empty_castling_squares c ctype)
      -> is_square_empty l pp = true) ->
    IsOccupiedBy pos (rook_castling_square c ctype) c Rook ->
    IsOccupiedBy pos (king_castling_square c) c King ->
    ~(IsInCheck pos c) ->
    (forall l, In l (empty_castling_squares c ctype)
      -> ~(AttacksEmptySquare pos (opponent_of c) l)) ->
    CanMakeCastlingMove pos c (Castle c ctype).

Definition can_make_castling_move (pos : Position) (c : Color) 
(ctype : CastlingType) : bool :=
  (andb (exists_in (castling_availabilities pos)
    (fun cavl => (cavleq cavl (Cavl ctype c))))
  (andb (forall_in (empty_castling_squares c ctype)
    (fun loc => is_square_empty loc (get_piece_placements pos)))
  (andb (eqSq (square_at_location pos (rook_castling_square c ctype))
    (Occupied c Rook))
  (andb (eqSq (square_at_location pos (king_castling_square c))
    (Occupied c King))
  (andb (negb (is_in_check pos c))
  (forall_in (empty_castling_squares c ctype)
    (fun loc => (negb (attacks_empty_square pos (opponent_of c) loc))))))))).

(*
Definition castling_moves (pos : Position) (c : Color) :=
  if (andb (exists_in (castling_availabilities pos) 
            (fun cavl => (cavleq cavl (Cavl c 
*)

(** Proofs **)
Lemma forall_in_iff : forall A (l : list A) (f : A -> bool),
  forall_in l f = true <-> (forall x, In x l -> f x = true).
Proof.
  intros A l f. split.
  - induction l.
    + simpl. intros. contradiction.
    + simpl. DGif.
      * intros. discriminate.
      * rewrite Bool.negb_false_iff in *. intros. HdOr; subst; auto.
  - induction l.
    + intros. simpl. auto.
    + intros. simpl. replace (f a) with true.
      * simpl. apply IHl. intros. apply H. apply in_cons. auto.
      * symmetry. apply H. apply in_eq.
Qed.

Lemma can_make_castling_move_sound : forall pos c ctype,
  can_make_castling_move pos c ctype = true -> 
  CanMakeCastlingMove pos c (Castle c ctype).
Proof.
  intros pos c ctype. unfold can_make_castling_move. intros.
  repeat (Hb2p; HdAnd). rewrite exists_in_iff in *. rewrite forall_in_iff in *.
  destruct H as [cavl [HcavlIn HcavlEq]]. rewrite cavleq_iff in *. subst.
  rewrite eqSq_iff in *. rewrite Bool.negb_true_iff in *.
  apply CanCastleIff with (pp:=(get_piece_placements pos))
  (pos_c:=get_to_move pos) (dstep:=get_pawn_double_step pos) 
  (cavl:=(castling_availabilities pos)); auto.
  - destruct pos. simpl. auto.
  - destruct (rook_castling_square c ctype) eqn:?E. eapply IsOccupiedBy_iff; 
    eauto.
  - destruct (king_castling_square c) eqn:?E. eapply IsOccupiedBy_iff; eauto.
  - intros C. apply is_in_check_complete in C. rewrite C in *. discriminate.
  - intros l Hin C. specialize (H4 l Hin) as HC. 
    rewrite Bool.negb_true_iff in HC. 
    rewrite <- attacks_empty_square_correct in C. rewrite C in *. discriminate.
Qed.

Lemma can_make_castling_move_complete : forall pos c ctype,
  CanMakeCastlingMove pos c (Castle c ctype) ->
  can_make_castling_move pos c ctype = true.
Proof.
  intros pos c ctype H. inversion H; subst. unfold can_make_castling_move.
  repeat (Gb2p; split).
  - rewrite exists_in_iff. exists (Cavl ctype c). split; auto. 
    rewrite cavleq_iff. auto.
  - rewrite forall_in_iff. intros. apply H3. auto.
  - rewrite eqSq_iff. inversion H4; subst. unfold square_at_location. auto.
  - rewrite eqSq_iff. inversion H5; subst. unfold square_at_location. auto.
  - rewrite Bool.negb_true_iff. 
    destruct (is_in_check (Posn pp pos_c dstep cavl) c) eqn:?E; auto.
    apply is_in_check_sound in E. contradiction.
  - rewrite forall_in_iff. intros. rewrite Bool.negb_true_iff. 
    destruct (attacks_empty_square (Posn pp pos_c dstep cavl) (opponent_of c) x) eqn:?E;
    auto.
    rewrite attacks_empty_square_correct in E. specialize (H8 x H0) as C.
    contradiction.
Qed.

Lemma can_make_castling_move_correct : forall pos c ctype,
  CanMakeCastlingMove pos c (Castle c ctype) <->
  can_make_castling_move pos c ctype = true.
Proof.
  intros. split. 
  - apply can_make_castling_move_complete.
  - apply can_make_castling_move_sound.
Qed.




