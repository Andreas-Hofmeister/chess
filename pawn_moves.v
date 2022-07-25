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

Definition final_rank_of_pawn (c : Color) : nat :=
  match c with
  | White => 7
  | Black => 0
  end.

Definition IsPromotionPiece (p : Piece) : Prop :=
  p = Bishop \/ p = Knight \/ p = Rook \/ p = Queen.

Inductive PawnCanMakeMove (pos : Position)
: SquareLocation -> Color -> Move -> Prop :=
  | PawnCanMoveForward : forall pp c pos_c dstep cavl loc sf sr tr,
    pos = Posn pp pos_c dstep cavl -> loc = Loc sr sf ->
    tr = advance_pawn c sr -> tr <> final_rank_of_pawn c ->
    location_valid loc -> location_valid (Loc tr sf) ->
    get_square_by_index pp tr sf = Empty -> 
    PawnCanMakeMove pos loc c (FromTo loc (Loc tr sf))
  | PawnCanCaptureDiagonallyForward : forall pp c pos_c dstep cavl loc sf sr 
    tf tr tc p,
    pos = Posn pp pos_c dstep cavl -> loc = Loc sr sf ->
    tr = advance_pawn c sr -> tr <> final_rank_of_pawn c ->
    difference sf tf = 1 ->
    location_valid loc -> location_valid (Loc tr tf) ->
    get_square_by_index pp tr tf = Occupied tc p -> tc <> c -> 
    PawnCanMakeMove pos loc c (Capture loc (Loc tr tf))
  | PawnCanDoubleStep : forall pp c pos_c dstep cavl loc sf sr step1r tr,
    pos = Posn pp pos_c dstep cavl -> loc = Loc sr sf ->
    location_valid loc ->
    sr = starting_rank_of_pawn c ->
    step1r = advance_pawn c sr ->
    tr = advance_pawn c step1r ->
    get_square_by_index pp step1r sf = Empty ->
    get_square_by_index pp tr sf = Empty ->
    PawnCanMakeMove pos loc c (DoubleStep loc (Loc tr sf))
  | PawnCanCaptureEnPassant : forall pp c dstep cavl loc dstf sf sr tr,
    pos = Posn pp c (Some dstep) cavl -> loc = Loc sr sf ->
    location_valid loc ->
    location_valid (Loc tr dstf) ->
    dstep = (DoubleStepRankFile sr dstf) ->
    difference sf dstf = 1 ->
    tr = advance_pawn c sr ->
    PawnCanMakeMove pos loc c (EnPassant loc (Loc tr dstf))
  | PawnCanPromoteForward : forall pp c pos_c dstep cavl loc sf sr tr piece,
    pos = Posn pp pos_c dstep cavl -> loc = Loc sr sf ->
    tr = advance_pawn c sr -> tr = final_rank_of_pawn c ->
    location_valid loc -> location_valid (Loc tr sf) ->
    get_square_by_index pp tr sf = Empty ->
    IsPromotionPiece piece ->
    PawnCanMakeMove pos loc c (Promotion loc (Loc tr sf) piece)
  | PawnCanPromoteDiagonally : forall pp c pos_c dstep cavl loc sf sr tf tr tc 
    p piece,
    pos = Posn pp pos_c dstep cavl -> loc = Loc sr sf ->
    tr = advance_pawn c sr -> tr = final_rank_of_pawn c ->
    difference tf sf = 1 ->
    location_valid loc -> location_valid (Loc tr tf) ->
    get_square_by_index pp tr tf = Occupied tc p -> tc <> c -> 
    IsPromotionPiece piece ->
    PawnCanMakeMove pos loc c (PromotionWithCapture loc (Loc tr tf) piece).

Definition pawn_forward_moves (pawn_loc : SquareLocation) (c : Color)
  (pos : Position) : (list Move) :=
  match pos with
  | Posn pp _ _ _ =>
    match pawn_loc with
    | Loc r f => 
      let new_r := advance_pawn c r in
        if andb (indices_valid r f) (indices_valid new_r f) then
          if (andb (is_square_empty_rank_file new_r f pp)
                (negb (new_r =? final_rank_of_pawn c))) 
          then [FromTo pawn_loc (Loc new_r f)]
          else nil
        else nil
    end
  end.

Definition pawn_captures (pawn_loc : SquareLocation) (c : Color) 
  (pos : Position) : (list Move) :=
  match pos with
  | Posn pp _ _ _ =>
    match pawn_loc with
    | Loc r f =>
      if (indices_valid r f) then
        let new_r := advance_pawn c r in
        let left_capture := 
          if (andb (1 <=? f) (occupied_by_enemy_piece new_r (f - 1) pp c))
          then [Capture pawn_loc (Loc new_r (f - 1))] else []
        in
        let right_capture :=
          if (andb (f <=? 6) (occupied_by_enemy_piece new_r (f + 1) pp c))
          then [Capture pawn_loc (Loc new_r (f + 1))] else []
        in if (orb (r =? final_rank_of_pawn c) (new_r =? final_rank_of_pawn c))
          then [] else left_capture ++ right_capture
        else []
    end
  end.

Definition pawn_double_steps (pawn_loc : SquareLocation) (c : Color)
  (pos : Position) :=
  match pos with
  | Posn pp _ _ _ =>
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

Definition en_passant_moves (pawn_loc : SquareLocation) (c : Color)
  (pos : Position) : (list Move) :=
  match pawn_loc with
  | Loc r f =>
    if (indices_valid r f) then
      match pos with
      | Posn pp toMove (Some (DoubleStepRankFile dsr dsf)) _ =>
        if (andb (ceq c toMove)
            (andb (dsr =? r) (indices_valid (advance_pawn toMove r) dsf)))
          then
          if (difference f dsf =? 1) then
            [EnPassant pawn_loc (Loc (advance_pawn toMove r) dsf)]
          else []
        else []
      | _ => []
      end
    else []
  end.

Definition pawn_forward_promotions (pawn_loc : SquareLocation) (c : Color)
  (pos : Position) : (list Move) :=
  match pos with
  | Posn pp _ _ _ =>
    match pawn_loc with
    | Loc r f => 
      let new_r := advance_pawn c r in
        if andb (indices_valid r f) (indices_valid new_r f) then
          if (andb (is_square_empty_rank_file new_r f pp)
                (new_r =? final_rank_of_pawn c))
          then [(Promotion pawn_loc (Loc new_r f) Rook);
                (Promotion pawn_loc (Loc new_r f) Knight);
                (Promotion pawn_loc (Loc new_r f) Bishop);
                (Promotion pawn_loc (Loc new_r f) Queen)]
          else nil
        else nil
    end
  end.

Definition pawn_promotion_captures (pawn_loc : SquareLocation) (c : Color)
  (pos : Position) : (list Move) :=
  match pos with
  | Posn pp _ _ _ =>
    match pawn_loc with
    | Loc r f =>
      if (indices_valid r f) then
        let new_r := advance_pawn c r in
        let left_capture := 
          if (andb (1 <=? f) (occupied_by_enemy_piece new_r (f - 1) pp c))
          then [PromotionWithCapture pawn_loc (Loc new_r (f - 1)) Rook;
                PromotionWithCapture pawn_loc (Loc new_r (f - 1)) Knight;
                PromotionWithCapture pawn_loc (Loc new_r (f - 1)) Bishop;
                PromotionWithCapture pawn_loc (Loc new_r (f - 1)) Queen] 
          else []
        in
        let right_capture :=
          if (occupied_by_enemy_piece new_r (f + 1) pp c) 
          then [PromotionWithCapture pawn_loc (Loc new_r (f + 1)) Rook;
                PromotionWithCapture pawn_loc (Loc new_r (f + 1)) Knight;
                PromotionWithCapture pawn_loc (Loc new_r (f + 1)) Bishop;
                PromotionWithCapture pawn_loc (Loc new_r (f + 1)) Queen] 
          else []
        in if (new_r =? final_rank_of_pawn c) 
          then left_capture ++ right_capture
          else []
        else []
    end
  end.

Definition pawn_moves (pawn_loc : SquareLocation) (c : Color) (pos : Position) 
:=
  (pawn_forward_moves pawn_loc c pos) ++
  (pawn_captures pawn_loc c pos) ++
  (pawn_double_steps pawn_loc c pos) ++
  (en_passant_moves pawn_loc c pos) ++
  (pawn_forward_promotions pawn_loc c pos) ++
  (pawn_promotion_captures pawn_loc c pos).

(* Proofs *)

Lemma pawn_moves_from : forall move loc c pos,
  In move (pawn_moves loc c pos) -> fromOfMove move = loc.
Proof.
  intros move loc c pos Hin. unfold pawn_moves in *. repeat in_app_to_or.
  - unfold pawn_forward_moves in *. repeat DHmatch; try HinNil. inversion Hin;
    try HinNil. subst. simpl. auto.
  - unfold pawn_captures in *. repeat DHmatch; try HinNil; 
    repeat in_app_to_or; inversion Hin; try HinNil; subst; simpl; auto.
  - unfold pawn_double_steps in *. repeat DHmatch; try HinNil. inversion Hin;
    try HinNil. subst. simpl. auto.
  - unfold en_passant_moves in *. repeat DHmatch; try HinNil. inversion Hin;
    try HinNil. subst. simpl. auto.
  - unfold pawn_forward_promotions in *. repeat DHmatch; try HinNil. 
    repeat HinCases; subst; simpl; auto.
  - unfold pawn_promotion_captures in *. repeat DHmatch; try HinNil;
    repeat in_app_to_or; repeat HinCases; subst; simpl; auto.
Qed.

Lemma pawn_forward_moves_sound : forall move loc c pos,
  In move (pawn_forward_moves loc c pos) -> 
  PawnCanMakeMove pos loc c move.
Proof.
  intros. 
  simpl in H. unfold pawn_forward_moves in H. 
  repeat DHmatch; repeat Hb2p; repeat HdAnd; repeat Hb2p; 
  inversion H; subst; repeat rewrite <- location_valid_iff in *; try HinNil.
  rewrite is_square_empty_rank_file_correct in *. eapply PawnCanMoveForward; 
  eauto.
Qed.

Lemma pawn_captures_sound : forall move loc c pos,
  In move (pawn_captures loc c pos) -> 
  PawnCanMakeMove pos loc c move.
Proof.
  intros. 
  simpl in H. unfold pawn_captures in H. repeat DHmatch; try HinNil; 
  in_app_to_or; HdOr; HinCases; try HinNil.
  - repeat Hb2p. repeat HdAnd. repeat Hb2p. 
    unfold occupied_by_enemy_piece in E6. DHif; try discriminate. DHmatch;
    try discriminate. DHif; try discriminate. assert (Henemy: c <> c0).
    { intros C. subst. rewrite ceq_refl in E10. discriminate. }
    rewrite <- location_valid_iff in E8. rewrite <- H.
    eapply PawnCanCaptureDiagonallyForward; eauto.
    + unfold difference. replace (file <? file - 1) with false; try Gb2p; 
      try lia.
    + rewrite location_valid_iff. auto.
  - repeat Hb2p. repeat HdAnd. repeat Hb2p. 
    unfold occupied_by_enemy_piece in E5. DHif; try discriminate. DHmatch;
    try discriminate. DHif; try discriminate. assert (Henemy: c <> c0).
    { intros C. subst. rewrite ceq_refl in E10. discriminate. }
    rewrite <- location_valid_iff in E8. rewrite <- H.
    eapply PawnCanCaptureDiagonallyForward; eauto.
    + unfold difference. replace (file <? file + 1) with true; try Gb2p; 
      try lia.
    + rewrite location_valid_iff. auto.
  - repeat Hb2p. repeat HdAnd. repeat Hb2p. 
    unfold occupied_by_enemy_piece in E5. DHif; try discriminate. DHmatch;
    try discriminate. DHif; try discriminate. assert (Henemy: c <> c0).
    { intros C. subst. rewrite ceq_refl in E9. discriminate. }
    rewrite <- location_valid_iff in E7. rewrite <- H.
    eapply PawnCanCaptureDiagonallyForward; eauto.
    + unfold difference. replace (file <? file - 1) with false; try Gb2p; 
      try lia.
    + rewrite location_valid_iff. auto.
  - repeat Hb2p. repeat HdAnd. repeat Hb2p. 
    unfold occupied_by_enemy_piece in E5. DHif; try discriminate. DHmatch;
    try discriminate. DHif; try discriminate. assert (Henemy: c <> c0).
    { intros C. subst. rewrite ceq_refl in E9. discriminate. }
    rewrite <- location_valid_iff in E7. rewrite <- H.
    eapply PawnCanCaptureDiagonallyForward; eauto.
    + unfold difference. replace (file <? file + 1) with true; try Gb2p; 
      try lia.
    + rewrite location_valid_iff. auto.
Qed.

Lemma pawn_double_steps_sound : forall move loc c pos,
  In move (pawn_double_steps loc c pos) -> 
  PawnCanMakeMove pos loc c move.
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

Lemma en_passant_moves_sound : forall move loc c pos,
  In move (en_passant_moves loc c pos) -> 
  PawnCanMakeMove pos loc c move.
Proof.
  intros. unfold en_passant_moves in H.
  destruct loc eqn:Eloc.
  repeat tac2.
  destruct pos eqn:Epos.
  destruct pawnDoubleStep eqn:Edstep; try inversion H.
  destruct p eqn:Ep.
  repeat tac2.
  repeat Hb2p. destruct H1 as [Hc H1]. 
  repeat Hb2p. destruct H1 as [Hdsr H1].
  repeat Hb2p.
  inversion H; inversion H3.
  repeat rewrite PeanoNat.Nat.eqb_eq in H2.
  rewrite <- location_valid_iff in *.
  simpl. eapply PawnCanCaptureEnPassant; simpl; eauto; simpl; try lia.
  rewrite ceq_eq in Hc. subst. auto. rewrite ceq_eq in Hc. subst. auto.
Qed.

Lemma pawn_forward_promotions_sound : forall move loc c pos,
  In move (pawn_forward_promotions loc c pos) -> 
  PawnCanMakeMove pos loc c move.
Proof.
  intros. 
  simpl in H. unfold pawn_forward_promotions in H. repeat DHmatch; try HinNil.
  repeat HinCases; subst; repeat Hb2p; repeat HdAnd; repeat Hb2p; 
  rewrite <- location_valid_iff in *; 
  repeat rewrite is_square_empty_rank_file_correct in *;
  eapply PawnCanPromoteForward; eauto; unfold IsPromotionPiece; auto.
Qed.

Lemma pawn_promotion_captures_sound : forall move loc c pos,
  In move (pawn_promotion_captures loc c pos) -> 
  PawnCanMakeMove pos loc c move.
Proof.
  intros move loc c pos Hin. unfold pawn_promotion_captures in Hin.
  repeat DHmatch; try HinNil; try simpl in Hin; try contradiction.
  - repeat HdOr; repeat Hb2p; repeat HdAnd;
    apply occupied_by_enemy_piece_correct in E5; 
    apply occupied_by_enemy_piece_correct in E4;
    destruct E5 as [c3 [ep3 [Hval3 [Hgetsq3 Hisenemy3]]]];
    destruct E4 as [c4 [ep4 [Hval4 [Hgetsq4 Hisenemy4]]]];
    rewrite <- location_valid_iff in *; subst; Hb2p;
    try eapply PawnCanPromoteDiagonally; eauto;
    unfold difference; replace (file - 1 <? file) with true; try Gb2p; try lia;
    unfold IsPromotionPiece; auto;
    replace (file + 1 <? file) with false; try Gb2p; try lia.
  - repeat HdOr; repeat Hb2p; repeat HdAnd;
    apply occupied_by_enemy_piece_correct in E5; 
    destruct E5 as [c3 [ep3 [Hval3 [Hgetsq3 Hisenemy3]]]];
    rewrite <- location_valid_iff in *; subst; Hb2p;
    try eapply PawnCanPromoteDiagonally; eauto; unfold difference;
    replace (file - 1 <? file) with true; try Gb2p; try lia;
    unfold IsPromotionPiece; auto.
  - repeat HdOr; repeat Hb2p; repeat HdAnd;
    apply occupied_by_enemy_piece_correct in E4; 
    destruct E4 as [c4 [ep4 [Hval4 [Hgetsq4 Hisenemy4]]]];
    rewrite <- location_valid_iff in *; subst;
    try eapply PawnCanPromoteDiagonally; eauto;
    unfold difference; replace (file + 1 <? file) with false; try Gb2p; 
    try lia; unfold IsPromotionPiece; auto.
Qed.

Lemma pawn_moves_sound : forall move loc c pos,
  In move (pawn_moves loc c pos) -> 
  PawnCanMakeMove pos loc c move.
Proof.
  intros. unfold pawn_moves in H.
  repeat in_app_to_or.
  - apply pawn_forward_moves_sound. auto.
  - apply pawn_captures_sound. auto.
  - apply pawn_double_steps_sound. auto.
  - apply en_passant_moves_sound. auto.
  - apply pawn_forward_promotions_sound. auto.
  - apply pawn_promotion_captures_sound. auto.
Qed.

Lemma not_final_pawn_rank : forall c r,
  advance_pawn c r <> final_rank_of_pawn c ->
  rank_index_valid (advance_pawn c r) = true ->
  r <> final_rank_of_pawn c.
Proof.
  intros c r Hadv_not_final Hadv_valid. destruct c eqn:Ec.
  - simpl. intros C. subst. simpl in *. unfold rank_index_valid in *.
    Hb2p. lia.
  - simpl. intros C. subst. simpl in *. contradiction.
Qed.

Lemma pawn_moves_complete : forall move loc c pos,
  PawnCanMakeMove pos loc c move -> In move (pawn_moves loc c pos).
Proof.
  intros.
  Ltac if_cond_destruct_in_goal := match goal with
  | |- In _ (if ?c then _ else _) => destruct c eqn:?H
  end.
  inversion H; subst; unfold pawn_moves.
  - rewrite in_app_iff. left. simpl.
    rewrite location_valid_iff in *. rewrite H4. rewrite H5. simpl. 
    rewrite <- PeanoNat.Nat.eqb_neq in *. rewrite H3.
    rewrite <- is_square_empty_rank_file_correct in *. rewrite H6. simpl.
    left. constructor.
  - rewrite in_app_iff. right. rewrite in_app_iff. left.
    rewrite location_valid_iff in *.
    simpl. rewrite <- PeanoNat.Nat.eqb_neq in *.
    rewrite H5. rewrite H3. 
    assert (Hr_not_final: sr =? final_rank_of_pawn c = false). { Gb2p. Hb2p. 
      unfold indices_valid in *. repeat Hb2p. repeat HdAnd. 
      apply not_final_pawn_rank; auto.
    }
    rewrite Hr_not_final. replace (false || false)%bool with false; auto.
    rewrite difference_1_iff in H4. 
    assert (Hctc: ceq tc c = false). { rewrite <- ceq_eq in H8. 
        destruct (ceq tc c) eqn:Ectc. try contradiction. auto.
    }
    destruct H4 as [[Hge1 Hdiff] | Hdiff].
    + destruct Hdiff as [Hdiff | Hdiff]. 
      * rewrite in_app_iff. left. destruct sf eqn:Esf; try lia.
        rewrite <- Hdiff. unfold occupied_by_enemy_piece. rewrite H6. 
        rewrite H7. rewrite Hctc. simpl. auto.
      * rewrite in_app_iff. right. assert (Hsf: sf <=? 6 = true). { Gb2p.
          unfold indices_valid in H6. repeat Hb2p. repeat HdAnd.
          unfold file_index_valid in *. unfold rank_index_valid in *.
          repeat Hb2p. lia.
        }
        rewrite Hsf. rewrite <- Hdiff. unfold occupied_by_enemy_piece.
        rewrite H6. rewrite H7. rewrite Hctc. simpl. auto.
    + destruct Hdiff as [Hsf Htf]. subst. rewrite in_app_iff. right.
      replace (0 <=? 6) with true; try Gb2p; try lia.
      replace (0 + 1) with 1; try lia. unfold occupied_by_enemy_piece.
      rewrite H6. rewrite H7. rewrite Hctc. simpl. auto.
  - rewrite in_app_iff. right. rewrite in_app_iff. right. rewrite in_app_iff.
    left.
    simpl. rewrite location_valid_iff in *. rewrite H2.
    rewrite PeanoNat.Nat.eqb_refl. rewrite <- is_square_empty_rank_file_correct in *.
    rewrite H6. rewrite H7. simpl. left. auto.
  - rewrite in_app_iff. right. rewrite in_app_iff. right. rewrite in_app_iff.
    right. rewrite in_app_iff. left. simpl. rewrite location_valid_iff in *. 
    rewrite H2. rewrite H3. rewrite PeanoNat.Nat.eqb_refl. rewrite ceq_refl.
    simpl. rewrite H5. simpl. auto.
  - repeat rewrite in_app_iff. right. right. right. right. left.
    rewrite location_valid_iff in *. 
    rewrite <- is_square_empty_rank_file_correct in *. Hp2b.
    simpl. rewrite H4. rewrite H5. rewrite H6. rewrite H3. simpl.
    unfold IsPromotionPiece in H7. repeat HdOr; subst; auto.
  - repeat rewrite in_app_iff. right. right. right. right. right.
    rewrite location_valid_iff in *. simpl. rewrite H5. rewrite H3. 
    rewrite PeanoNat.Nat.eqb_refl. assert (Hctc: ceq tc c = false). { 
        rewrite <- ceq_eq in H8. 
        destruct (ceq tc c) eqn:Ectc. try contradiction. auto.
    }
    rewrite difference_1_iff in H4. destruct H4 as [[Hge1 Hdiff] | Hdiff].
    + destruct Hdiff as [Hdiff | Hdiff]. destruct sf eqn:Esf.
      * rewrite in_app_iff. right. assert (Htf: tf = 1). { lia. }
        replace (0 + 1) with 1; try lia. unfold occupied_by_enemy_piece.
        rewrite <- H3. rewrite Htf in H6. rewrite H6. rewrite Htf in H7.
        rewrite H7. rewrite Hctc. unfold IsPromotionPiece in *. repeat HdOr; 
        subst; repeat (try apply in_eq; apply in_cons).
      * assert (Hsf: sf = tf - 1). { lia. } 
        assert (Htf: tf = sf + 1). { lia. }
        subst. rewrite in_app_iff. right. unfold occupied_by_enemy_piece.
        rewrite <- H3. rewrite H6. rewrite H7. rewrite Hctc.
        unfold IsPromotionPiece in *. repeat HdOr; subst; 
        repeat (try apply in_eq; apply in_cons).
      * assert (Htf: tf = sf - 1). { lia. } 
        subst. rewrite <- H3. destruct (tf + 1) eqn:Eweird; try lia. subst.
        rewrite in_app_iff. left. unfold occupied_by_enemy_piece. rewrite H6.
        rewrite H7. rewrite Hctc. replace (true && true)%bool with true; auto.
        unfold IsPromotionPiece in *.
        repeat HdOr; subst; repeat (try apply in_eq; apply in_cons).
    + rewrite <- H3. destruct Hdiff as [Htf Hsf]. subst. rewrite in_app_iff. 
      left. replace (1-1) with 0; try lia. unfold occupied_by_enemy_piece. 
      rewrite H6. rewrite H7. rewrite Hctc. 
      replace (true && true)%bool with true; auto. 
      unfold IsPromotionPiece in *. repeat HdOr; subst; 
      repeat (try apply in_eq; apply in_cons).
Qed.
