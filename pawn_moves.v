Require Import List.
Require Import Nat.
From CHESS Require Export proof_tactics.
From CHESS Require Export basics.
From CHESS Require Export movement_basics.

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

Inductive PawnCanMakeMove (pos : Position)
: SquareLocation -> Move -> Prop :=
  | PawnCanMoveForward : forall pp c dstep loc sf sr tr,
    pos = Posn pp c dstep -> loc = Loc sr sf ->
    tr = advance_pawn c sr ->
    location_valid loc -> location_valid (Loc tr sf) ->
    get_square_by_index pp tr sf = Empty -> 
    PawnCanMakeMove pos loc (FromTo loc (Loc tr sf))
  | PawnCanCaptureDiagonallyForward : forall pp c dstep loc sf sr tf tr tc p,
    pos = Posn pp c dstep -> loc = Loc sr sf ->
    tr = advance_pawn c sr ->
    (tf = sf + 1 \/ tf = sf - 1) ->
    location_valid loc -> location_valid (Loc tr tf) ->
    get_square_by_index pp tr tf = Occupied tc p -> tc <> c -> 
    PawnCanMakeMove pos loc (Capture loc (Loc tr tf))
  | PawnCanDoubleStep : forall pp c dstep loc sf sr step1r tr,
    pos = Posn pp c dstep -> loc = Loc sr sf ->
    location_valid loc ->
    sr = starting_rank_of_pawn c ->
    step1r = advance_pawn c sr ->
    tr = advance_pawn c step1r ->
    get_square_by_index pp step1r sf = Empty ->
    get_square_by_index pp tr sf = Empty ->
    PawnCanMakeMove pos loc (DoubleStep loc (Loc tr sf))
  | PawnCanCaptureEnPassant : forall pp c dstep loc dstf sf sr tr,
    pos = Posn pp c (Some dstep) -> loc = Loc sr sf ->
    location_valid loc ->
    dstep = (DoubleStepRankFile sr dstf) ->
    (sf = dstf + 1 \/ sf = dstf - 1) ->
    tr = advance_pawn c sr ->
    PawnCanMakeMove pos loc (EnPassant loc (Loc tr dstf)).

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

Lemma pawn_forward_moves_sound : forall move loc pos,
  In move (pawn_forward_moves loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. 
  simpl in H. unfold pawn_forward_moves in H.
  destruct pos eqn:Epos. destruct loc eqn:Eloc.
  destruct (indices_valid (advance_pawn toMove rank) file) eqn:Eiv; 
    try rewrite Bool.andb_false_r in H; simpl in H; try contradiction.
  destruct (indices_valid rank file) eqn:Eiv2; try simpl in H; 
    try contradiction.
  destruct (is_square_empty_rank_file (advance_pawn toMove rank) file pp) eqn:Eempty;
    try simpl in H; try contradiction.
  destruct H as [H | W]; try contradiction.
  subst. rewrite <- location_valid_iff in *. 
  rewrite is_square_empty_rank_file_correct in *.
  eapply PawnCanMoveForward; auto.
Qed.

Lemma pawn_captures_sound : forall move loc pos,
  In move (pawn_captures loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. 
  simpl in H. unfold pawn_captures in H.
  destruct pos eqn:Epos. destruct loc eqn:Eloc.
  destruct (indices_valid rank file) eqn:Hivsrc; try inversion H.
  rewrite <- location_valid_iff in *.
  Ltac tac1 :=
    match goal with
    | H: In _ (if occupied_by_enemy_piece ?r ?f ?pp ?c then _ else _) |- _
          => destruct (occupied_by_enemy_piece r f pp c) eqn: Eoc
    end;
    try inversion H; try inversion H0;
    match goal with
    | H: (occupied_by_enemy_piece ?r ?f ?pp ?c = _) |- _ 
          => apply occupied_by_enemy_piece_correct in H; 
             destruct H as [c2 [piece [Hiv [Hoc Henemy]]]]
    end;
    subst; try rewrite <- location_valid_iff in *; 
    eapply PawnCanCaptureDiagonallyForward; simpl; eauto.
  apply in_app_or in H. destruct H as [H | H]; tac1.
Qed.

Lemma pawn_double_steps_sound : forall move loc pos,
  In move (pawn_double_steps loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros.
  simpl in H. unfold pawn_double_steps in H.
  destruct pos eqn:Epos. destruct loc eqn:Eloc.
  Ltac tac2 := match goal with
  | H : In _ (if ?c then _ else _) |- _ => destruct c eqn:?H
  | H : In _ [] |- _ => inversion H
  end.
  repeat tac2. rewrite <- location_valid_iff in *.
  rewrite Bool.andb_true_iff in *. repeat rewrite is_square_empty_rank_file_correct in *.
  inversion H; inversion H3. subst. destruct H2 as [Hempty1 Hempty2].
  rewrite PeanoNat.Nat.eqb_eq in H1. eapply PawnCanDoubleStep; eauto.
Qed.

Lemma en_passant_moves_sound : forall move loc pos,
  In move (en_passant_moves loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. unfold en_passant_moves in H.
  destruct loc eqn:Eloc.
  repeat tac2.
  destruct pos eqn:Epos.
  destruct pawnDoubleStep eqn:Edstep; try inversion H.
  destruct p eqn:Ep.
  repeat tac2.
  rewrite PeanoNat.Nat.eqb_eq in H1.
  inversion H; inversion H3.
  rewrite Bool.orb_true_iff in H2. repeat rewrite PeanoNat.Nat.eqb_eq in H2.
  rewrite <- location_valid_iff in *.
  simpl. eapply PawnCanCaptureEnPassant; simpl; eauto; simpl; try lia.
Qed.

Lemma pawn_moves_sound : forall move loc pos,
  In move (pawn_moves loc pos) -> 
  PawnCanMakeMove pos loc move.
Proof.
  intros. unfold pawn_moves in H.
  repeat in_app_to_or.
  - apply pawn_forward_moves_sound. auto.
  - apply pawn_captures_sound. auto.
  - apply pawn_double_steps_sound. auto.
  - apply en_passant_moves_sound. auto.
Qed.

Lemma pawn_moves_complete : forall move loc pos,
  PawnCanMakeMove pos loc move -> In move (pawn_moves loc pos).
Proof.
  intros.
  Ltac if_cond_destruct_in_goal := match goal with
  | |- In _ (if ?c then _ else _) => destruct c eqn:?H
  end.
  inversion H; subst; unfold pawn_moves.
  - rewrite in_app_iff. left. simpl.
    rewrite location_valid_iff in *. rewrite H3. rewrite H4. simpl.
    rewrite <- is_square_empty_rank_file_correct in *. rewrite H5. constructor. auto.
  - rewrite in_app_iff. right. rewrite in_app_iff. left.
    rewrite location_valid_iff in *. 
    simpl. rewrite H4. destruct H3 as [Hr | Hl].
    + rewrite in_app_iff. right. subst. if_cond_destruct_in_goal.
      * constructor. auto.
      * rewrite <- Bool.not_true_iff_false in H0. exfalso. apply H0. 
        apply occupied_by_enemy_piece_correct. eexists. eexists. eauto.
    + rewrite in_app_iff. left. subst. if_cond_destruct_in_goal.
      * constructor. auto.
      * rewrite <- Bool.not_true_iff_false in H0. exfalso. apply H0. 
        apply occupied_by_enemy_piece_correct. eexists. eexists. eauto.
  - rewrite in_app_iff. right. rewrite in_app_iff. right. rewrite in_app_iff.
    left.
    simpl. rewrite location_valid_iff in *. rewrite H2.
    rewrite PeanoNat.Nat.eqb_refl. rewrite <- is_square_empty_rank_file_correct in *.
    rewrite H6. rewrite H7. simpl. left. auto.
  - rewrite in_app_iff. right. rewrite in_app_iff. right. rewrite in_app_iff.
    right. simpl. rewrite location_valid_iff in *. rewrite H2. 
    rewrite PeanoNat.Nat.eqb_refl. 
    destruct ((dstf =? sf + 1) || (dstf =? sf - 1))%bool eqn:Edstf.
    + constructor. auto.
    + rewrite Bool.orb_false_iff in Edstf. 
      repeat rewrite PeanoNat.Nat.eqb_neq in Edstf. lia.
Qed.

