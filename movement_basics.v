Require Import List.
Require Import Nat.
From CHESS Require Export basics.
Require Import Recdef. (* Must import this to use the Function feature *)

Inductive Move : Type :=
  | FromTo (from : SquareLocation) (to : SquareLocation)
  | Capture (from : SquareLocation) (to : SquareLocation)
  | DoubleStep (from : SquareLocation) (to : SquareLocation)
  | EnPassant (from : SquareLocation) (to : SquareLocation)
  | Promotion (from : SquareLocation) (to : SquareLocation) (piece : Piece)
  | PromotionWithCapture (from : SquareLocation) (to : SquareLocation) 
      (piece : Piece)
  | Castle (c : Color) (castling_type : CastlingType).

Definition fromOfMove (m : Move) : SquareLocation :=
  match m with
  | FromTo from _ => from
  | Capture from _ => from
  | DoubleStep from _ => from
  | EnPassant from _ => from
  | Promotion from _ _ => from
  | PromotionWithCapture from _ _ => from
  | Castle White _ => (Loc 0 4)
  | Castle Black _ => (Loc 7 4)
  end.

Definition toOfMove (m : Move) : SquareLocation :=
  match m with
  | FromTo _ to => to
  | Capture _ to => to
  | DoubleStep _ to => to
  | EnPassant _ to => to
  | Promotion _ to _ => to
  | PromotionWithCapture _ to _ => to
  | Castle White QueenSide => (Loc 0 2)
  | Castle White KingSide => (Loc 0 6)
  | Castle Black QueenSide => (Loc 7 2)
  | Castle Black KingSide => (Loc 7 6)
  end.

Inductive IsMoveToEmptySquare : Move -> Prop :=
  | IsFromTo : forall from to move, 
    move = FromTo from to -> IsMoveToEmptySquare move
  | IsEnPassant : forall from to move,
    move = EnPassant from to -> IsMoveToEmptySquare move
  | IsDoubleStep : forall from to move,
    move = DoubleStep from to -> IsMoveToEmptySquare move
  | IsPromotion : forall from to piece move,
    move = Promotion from to piece -> IsMoveToEmptySquare move.

Definition is_move_to_empty_square (m : Move) : bool :=
  match m with
  | FromTo _ _ => true
  | EnPassant _ _ => true
  | DoubleStep _ _ => true
  | Promotion _ _ _ => true
  | _ => false
  end.

Inductive IsCapturingMove : Move -> Prop :=
  | IsNormalCapture : forall from to move,
    move = Capture from to -> IsCapturingMove move
  | IsPromotionWithCapture : forall from to piece move,
    move = PromotionWithCapture from to piece -> IsCapturingMove move.

Definition is_capturing_move (m : Move) : bool :=
  match m with
  | Capture _ _ => true
  | PromotionWithCapture _ _ _ => true
  | _ => false
  end.

Definition get_double_step_target_rank (dstep : PawnDoubleStep) :=
  match dstep with
  | DoubleStepRankFile r f => r
  end.

Definition get_double_step_file (dstep : PawnDoubleStep) :=
  match dstep with
  | DoubleStepRankFile r f => f
  end.

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
      let rank_step := if r_a <=? r_b then (VStep Up (r_b - r_a))
        else (VStep Down (r_a - r_b)) in
      let file_step := if f_a <=? f_b then (HStep Right (f_b - f_a))
        else (HStep Left (f_a - f_b)) in
      (VectorHV file_step rank_step)
    end
  end.

Definition one_step_along_vector (l : SquareLocation) (v : Vector) :=
  match l with
  | Loc r f => match v with
    | VectorHV (HStep _ 0) (VStep _ 0) => l
    | VectorHV (HStep _ 0) (VStep Up (S _)) => Loc (r + 1) f
    | VectorHV (HStep _ 0) (VStep Down (S _)) => Loc (r - 1) f
    | VectorHV (HStep Left (S _)) (VStep _ 0) => Loc r (f - 1)
    | VectorHV (HStep Right (S _)) (VStep _ 0) => Loc r (f + 1)
    | VectorHV (HStep Right (S _)) (VStep Up (S _)) => Loc (r + 1) (f + 1)
    | VectorHV (HStep Left (S _)) (VStep Up (S _)) => Loc (r + 1) (f - 1)
    | VectorHV (HStep Right (S _)) (VStep Down (S _)) => Loc (r - 1) (f + 1)
    | VectorHV (HStep Left (S _)) (VStep Down (S _)) => Loc (r - 1) (f - 1)
    end
  end.

Definition vector_length (v: Vector) : nat :=
  match v with
  | VectorHV (HStep _ n) (VStep _ m) => n + m
  end.

Definition manhattan_distance (loc1 : SquareLocation) (loc2 : SquareLocation)
:= vector_length (vector_from_a_to_b loc1 loc2).

Definition one_step_along_vector_and_location (l : SquareLocation) (v : Vector) 
  : (Vector * SquareLocation) :=
  match l with
  | Loc r f => match v with
    | VectorHV (HStep dh 0) (VStep dv 0) => 
      (VectorHV (HStep dh 0) (VStep dv 0), l)
    | VectorHV (HStep dh 0) (VStep Up (S m)) => 
      (VectorHV (HStep dh 0) (VStep Up m), Loc (r + 1) f)
    | VectorHV (HStep dh 0) (VStep Down (S m)) => 
      (VectorHV (HStep dh 0) (VStep Down m), Loc (r - 1) f)
    | VectorHV (HStep Left (S n)) (VStep dv 0) => 
      (VectorHV (HStep Left n) (VStep dv 0), Loc r (f - 1))
    | VectorHV (HStep Right (S n)) (VStep dv 0) => 
      (VectorHV (HStep Right n) (VStep dv 0), Loc r (f + 1))
    | VectorHV (HStep Right (S n)) (VStep Up (S m)) => 
      (VectorHV (HStep Right n) (VStep Up m), Loc (r + 1) (f + 1))
    | VectorHV (HStep Left (S n)) (VStep Up (S m)) => 
      (VectorHV (HStep Left n) (VStep Up m), Loc (r + 1) (f - 1))
    | VectorHV (HStep Right (S n)) (VStep Down (S m)) => 
      (VectorHV (HStep Right n) (VStep Down m), Loc (r - 1) (f + 1))
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
  | HStep Left n, Loc r f => Loc r (f - n)
  | HStep Right n, Loc r f => Loc r (f + n)
  end.

Definition apply_vstep (s : VerticalStep) (loc : SquareLocation) 
  : SquareLocation :=
  match s,loc with
  | VStep Up n, Loc r f => Loc (r + n) f
  | VStep Down n, Loc r f => Loc (r - n) f
  end.

Definition apply_vector (v : Vector) (loc : SquareLocation) : SquareLocation :=
  match v with
  | VectorHV hstep vstep => (apply_vstep vstep (apply_hstep hstep loc))
  end.

Definition make_vector_stay_in_bounds (v : Vector) (l : SquareLocation) :=
  match l with
  | Loc rank file =>
    match v with
    | VectorHV (HStep Left n) (VStep Down m) =>
      VectorHV (HStep Left (min n file)) (VStep Down (min m rank))
    | VectorHV (HStep Left n) (VStep Up m) =>
      VectorHV (HStep Left (min n file)) (VStep Up (min m (7 - rank)))
    | VectorHV (HStep Right n) (VStep Down m) =>
      VectorHV (HStep Right (min n (7 - file))) (VStep Down (min m rank))
    | VectorHV (HStep Right n) (VStep Up m) =>
      VectorHV (HStep Right (min n (7 - file))) (VStep Up (min m (7 - rank)))
    end
  end.

Definition are_squares_between_empty (pp : PiecePlacements) 
  (loc1 : SquareLocation) (loc2 : SquareLocation) :=
  let (v, start) := 
    one_step_along_vector_and_location loc1 (vector_from_a_to_b loc1 loc2) in
  are_squares_along_vector_empty pp start v.

(* rfd = rank, file, diagonal, or antidiagonal *)
Function move_to_square_on_rfd (pos : Position) (c : Color)
  (fromL : SquareLocation) (toL : SquareLocation) : option Move :=
  match pos with
  | Posn pp _ _ _ =>
    if ((negb (eqSL fromL toL)) && (are_squares_between_empty pp fromL toL))%bool
    then if is_square_empty toL pp then Some (FromTo fromL toL)
    else if is_square_occupied_by_enemy_piece toL pp c 
      then Some (Capture fromL toL)
      else None
    else None
  end.

Function moves_to_square_on_rfd_list (pos : Position) (c : Color)
  (fromL : SquareLocation) (toL : SquareLocation) : list Move :=
  match (move_to_square_on_rfd pos c fromL toL) with
  | Some move => [move]
  | _ => []
  end.

Fixpoint squares_along_direction_aux (l : SquareLocation) 
  (hd : HorizontalDirection) (vd : VerticalDirection) (steps : nat) :=
  match steps with
  | 0 => []
  | S n =>
    match l with
    | Loc rank file =>
      match hd,vd with
      | Right, Up =>
        let l1 := Loc (rank + 1) (file + 1) in
        l1 :: (squares_along_direction_aux l1 Right Up n)
      | Right, Down =>
        let l1 := Loc (rank - 1) (file + 1) in
        l1 :: (squares_along_direction_aux l1 Right Down n)
      | Left, Up =>
        let l1 := Loc (rank + 1) (file - 1) in
        l1 :: (squares_along_direction_aux l1 Left Up n)
      | Left, Down =>
        let l1 := Loc (rank - 1) (file - 1) in
        l1 :: (squares_along_direction_aux l1 Left Down n)
      end
    end
  end.

Definition squares_along_direction (l : SquareLocation)
  (hd : HorizontalDirection) (vd : VerticalDirection) :=
  match l with Loc rank file =>
    let hsteps := match hd with
    | Left => file
    | Right => (7 - file)
    end
    in
    let vsteps := match vd with
    | Up => (7 - rank)
    | Down => rank
    end
    in
    squares_along_direction_aux l hd vd (min hsteps vsteps)
  end.

Definition are_squares_on_same_diagonal (l1 l2 : SquareLocation) : bool :=
  match (vector_from_a_to_b l1 l2) with
  | VectorHV (HStep Right n) (VStep Up m) => if (n =? m) then true else false
  | VectorHV (HStep Left n) (VStep Down m) => if (n =? m) then true else false
  | _ => false
  end.

Definition are_squares_on_same_antidiagonal (l1 l2 : SquareLocation) : bool :=
  match (vector_from_a_to_b l1 l2) with
  | VectorHV (HStep Right n) (VStep Down m) => if (n =? m) then true else false
  | VectorHV (HStep Left n) (VStep Up m) => if (n =? m) then true else false
  | VectorHV (HStep Right 0) (VStep Up 0) => true
  | VectorHV (HStep Left 0) (VStep Down 0) => true
  | _ => false
  end.

Definition squares_on_same_diagonal (l : SquareLocation) : list SquareLocation
  :=
  (squares_along_direction l Right Up) ++ 
  (squares_along_direction l Left Down).

Definition squares_on_same_antidiagonal (l : SquareLocation) 
  : list SquareLocation :=
  (squares_along_direction l Right Down) ++ 
  (squares_along_direction l Left Up).

Definition does_vector_stay_within_boundaries (v : Vector) (l : SquareLocation) 
  : bool :=
  match l with
  | Loc x y =>
    match v with
    | VectorHV (HStep Left n) (VStep Down m) => ((n <=? y) && (m <=? x))%bool
    | VectorHV (HStep Left n) (VStep Up m) => ((n <=? y) && (x + m <=? 7))%bool
    | VectorHV (HStep Right n) (VStep Down m) => ((m <=? x) && (y + n <=? 7))%bool
    | VectorHV (HStep Right n) (VStep Up m) => ((x + m <=? 7) && (y + n <=? 7))%bool
    end
  end.

Definition vector_stays_within_boundaries (v : Vector) (l : SquareLocation) 
  : Prop :=
  match l with
  | Loc x y =>
    match v with
    | VectorHV (HStep Left n) (VStep Down m) => (n <= y) /\ (m <= x)
    | VectorHV (HStep Left n) (VStep Up m) => (n <= y) /\ (x + m <= 7)
    | VectorHV (HStep Right n) (VStep Down m) => (m <= x) /\ (y + n <= 7)
    | VectorHV (HStep Right n) (VStep Up m) => (x + m <= 7) /\ (y + n <= 7)
    end
  end.


Fixpoint target_squares (from : SquareLocation) (vs : list Vector) :=
  match vs with
  | [] => []
  | v :: rvs => if (does_vector_stay_within_boundaries v from) then
    (apply_vector v from) :: (target_squares from rvs) else
    (target_squares from rvs)
  end.

Inductive SquaresBetweenEmpty (pp : PiecePlacements)
  : SquareLocation -> SquareLocation -> Prop :=
  | NothingOccupiedBetweenAdjacentSquares : forall loc1 loc2, 
    SquaresAdjacent loc1 loc2 -> SquaresBetweenEmpty pp loc1 loc2
  | NothingOccupiedBetweenSingleSquare : forall loc,
    SquaresBetweenEmpty pp loc loc
  | SquaresAlongVectorEmpty : forall loc1 loc2 v first_step,
    vector_from_a_to_b loc1 loc2 = v ->
    (one_step_along_vector loc1 v) = first_step ->
    is_square_empty first_step pp = true ->
    SquaresBetweenEmpty pp first_step loc2 ->
    SquaresBetweenEmpty pp loc1 loc2.

(*****Proofs*****)

Lemma move_to_square_on_rfd_from : forall pos c fromL toL move,
  move_to_square_on_rfd pos c fromL toL = Some move -> fromOfMove move = fromL.
Proof.
  intros pos c fromL toL move Hmove. unfold move_to_square_on_rfd in *.
  repeat DHmatch; inversion Hmove; auto.
Qed.

Lemma moves_to_square_on_rfd_list_from : forall move pos c l a,
  In move (moves_to_square_on_rfd_list pos c l a) -> fromOfMove move = l.
Proof.
  intros move pos c l a Hin. unfold moves_to_square_on_rfd_list in *.
  repeat DHmatch; inversion Hin; subst.
  - apply move_to_square_on_rfd_from with (pos:=pos) (c:=c) (toL:=a). auto.
  - HinNil.
Qed.

Lemma is_move_to_empty_square_correct : forall m,
  IsMoveToEmptySquare m <-> is_move_to_empty_square m = true.
Proof.
  intros m. split.
  - intros. inversion H; subst; simpl; auto.
  - intros. unfold is_move_to_empty_square in *. DHmatch; try discriminate.
    + eapply IsFromTo; eauto.
    + eapply IsDoubleStep; eauto.
    + eapply IsEnPassant; eauto.
    + eapply IsPromotion; eauto.
Qed.

Lemma is_capturing_move_correct : forall m,
  IsCapturingMove m <-> is_capturing_move m = true.
Proof.
  intros m. split.
  - intros H. inversion H; subst; simpl; auto.
  - intros H. unfold is_capturing_move in *. DHmatch; try discriminate.
    + eapply IsNormalCapture; eauto.
    + eapply IsPromotionWithCapture; eauto.
Qed.

Lemma one_step_along_vector_adjacent : forall l l2 v,
  l2 = (one_step_along_vector l v) -> l = l2 \/ SquaresAdjacent l l2.
Proof.
  Ltac split_and_differences := match goal with
  | |- _ /\ _ => repeat split
  | |- difference _ _ <= 1 /\ difference _ _ <= 1 => split
  | |- difference ?x ?x <= 1 => rewrite difference_n_n; lia
  | |- difference ?x (?x - 1) <= 1 => apply difference_n_nm1
  | |- difference ?x (?x + 1) <= 1 => apply difference_n_np1
  end.
  Ltac equality_cases := match goal with
  | |- (Loc _ _ = Loc _ _) \/ _ => left; apply eq_Loc; lia
  end.
  intros. unfold one_step_along_vector in *.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehs.
  destruct d eqn:Ed; destruct n eqn:En; destruct vstep eqn:Evs;
  destruct d0 eqn:Ed0; destruct n0 eqn:En0; auto; simpl; rewrite H;
  repeat split_and_differences; destruct n1 eqn:En1; repeat split_and_differences;
  destruct rank eqn:?E; destruct file eqn:?E; try equality_cases; right; 
  repeat split_and_differences; intros C; inversion C; lia.
Qed.

Lemma one_step_along_vector_and_location_adjacent : forall l v l1 v1,
  one_step_along_vector_and_location l v = (v1, l1) -> 
  l = l1 \/ SquaresAdjacent l l1.
Proof.
  intros. unfold one_step_along_vector_and_location in H. repeat Hdestruct;
  subst; inversion H; auto; destruct rank eqn:?E; destruct file eqn:?E;
  try equality_cases; right; split; unfold difference;
  repeat match goal with
  | |- _ /\ _ => repeat split
  | |- (if ?x <? ?y then _ else _) <= _ => destruct (x <? y) eqn:?H; lia
  end; intros C; inversion C; lia.
Qed.

Lemma one_step_along_vector_and_location_shorter : forall l v v1 l1,
  vector_length v <> 0 ->
  one_step_along_vector_and_location l v = (v1,l1) -> 
  vector_length v1 < vector_length v.
Proof.
  intros.
  unfold one_step_along_vector_and_location in H0.
  destruct l eqn:El.
  destruct v eqn:Ev.
  repeat Hdestruct; inversion H0; subst; simpl in H; try lia; simpl; try lia.
Qed.

Lemma one_step_along_vector_and_location_diagonal : forall l v v1 l1,
  RankFileOrDiagonalVector v ->
  one_step_along_vector_and_location l v = (v1,l1) ->
  RankFileOrDiagonalVector v1.
Proof.
  intros. unfold one_step_along_vector_and_location in H0. 
  destruct l eqn:El. unfold RankFileOrDiagonalVector in H.
  destruct H as [HR | [HF | HD]].
  - inversion HR. subst. repeat Hdestruct; inversion H0; subst; left; 
    constructor.
  - inversion HF. subst. repeat Hdestruct; inversion H0; subst; right; left;
    constructor.
  - inversion HD. subst. repeat Hdestruct; inversion H0; subst; right; right;
    constructor.
Qed.

Lemma vector_length_0_iff : forall d1 n d2 m,
  vector_length (VectorHV (HStep d1 n) (VStep d2 m)) = 0 <-> (n = 0) /\ (m = 0).
Proof.
  intros. simpl. split; intros; lia.
Qed.

Lemma vector_length_not_0_iff : forall d1 n d2 m,
  vector_length (VectorHV (HStep d1 n) (VStep d2 m)) <> 0 <-> 
  (n > 0) \/ (m > 0).
Proof.
  intros. simpl. split; intros; lia.
Qed.

Lemma apply_null_vector : forall v l, 
  vector_length v = 0 -> apply_vector v l = l.
Proof.
  intros. unfold vector_length in H. repeat Hdestruct.
  assert (Hn_is_zero: n = 0). lia.
  assert (H_n0_is_zero: n0 = 0). lia.
  subst. simpl. destruct d0 eqn:Ed0; destruct d eqn:Ed; destruct l eqn:El;
  apply eq_Loc; try lia.
Qed.

Lemma one_step_along_vector_and_location_correct: forall s v v1 s1,
  one_step_along_vector_and_location s v = (v1, s1) ->
  apply_vector v s = apply_vector v1 s1.
Proof.
  intros. unfold one_step_along_vector_and_location in H. repeat Hdestruct;
  inversion H; subst; try reflexivity; simpl; try apply eq_Loc; try lia.
Qed.

Lemma eq_VectorHV: forall dh1 n1 dv1 m1 dh2 n2 dv2 m2,
  dh1 = dh2 -> n1 = n2 -> dv1 = dv2 -> m1 = m2 ->
  VectorHV (HStep dh1 n1) (VStep dv1 m1) = VectorHV (HStep dh2 n2) (VStep dv2 m2).
Proof.
  intros. subst. auto.
Qed.

Lemma one_step_along_vector_and_location_last_step: forall s v v1 s1,
  one_step_along_vector_and_location s v = (v1, s1) ->
  vector_length v <> 0 -> vector_length v1 = 0 ->
  s1 = apply_vector v s.
Proof.
  intros. rewrite (one_step_along_vector_and_location_correct s v v1 s1); auto.
  rewrite apply_null_vector; auto.
Qed.

Lemma vector_from_a_to_b_preserves_diagonal : forall v start,
  vector_stays_within_boundaries v start ->
  RankFileOrDiagonalVector v -> 
  RankFileOrDiagonalVector (vector_from_a_to_b start (apply_vector v start)).
Proof.
  intros v start Hbounds Hvdiag. unfold vector_from_a_to_b.
  destruct start eqn:Estart.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl.
  Ltac simplify_calculations := try inversion Hr; try inversion Hf; 
    try inversion Hd; subst; repeat rewrite PeanoNat.Nat.add_0_r; 
    repeat rewrite PeanoNat.Nat.sub_0_r; repeat rewrite PeanoNat.Nat.sub_diag;
    repeat rewrite PeanoNat.Nat.leb_refl.
  Ltac finish1 := left; constructor.
  Ltac finish2 := right; left; constructor.
  Ltac finish3 := right; right; constructor.
  Ltac finish := try finish1; try finish2; try finish3.
  - simpl in Hbounds. destruct Hvdiag as [Hr | [Hf | Hd]];
    simplify_calculations; finish.
    inversion Hd. subst. replace (rank <=? rank + n0) with true; 
    try symmetry; try rewrite PeanoNat.Nat.leb_le; try lia. 
    replace (rank + n0 - rank) with n0; try lia.
    destruct file eqn:Hfl. simpl. finish.
    destruct (S n <=? S n - n0) eqn:En.
    + replace (S n - n0 - S n) with 0; try lia. finish.
    + rewrite PeanoNat.Nat.leb_gt in En. replace (S n - (S n - n0)) with n0; 
      try lia. finish.
  - simpl in Hbounds. destruct Hbounds as [Hbounds1 Hbounds2].
    destruct Hvdiag as [Hr | [Hf | Hd]]; simplify_calculations; finish.
    destruct n0. simplify_calculations. finish.
    replace (rank <=? rank - S n0) with false; try symmetry; 
    try rewrite PeanoNat.Nat.leb_gt; try lia.
    replace (file <=? file - S n0) with false; try symmetry; 
    try rewrite PeanoNat.Nat.leb_gt; try lia.
    replace (rank - (rank - S n0)) with (S n0); try lia.
    replace (file - (file - S n0)) with (S n0); try lia. finish.
  - simpl in Hbounds. destruct Hvdiag as [Hr | [Hf | Hd]]; 
    simplify_calculations; finish.
    replace (rank <=? rank + n0) with true; try symmetry; 
    try rewrite PeanoNat.Nat.leb_le; try lia.
    replace (file <=? file + n0) with true; try symmetry; 
    try rewrite PeanoNat.Nat.leb_le; try lia.
    replace (rank + n0 - rank) with n0; try lia.
    replace (file + n0 - file) with n0; try lia. finish.
  - simpl in Hbounds. destruct Hvdiag as [Hr | [Hf | Hd]]; 
    simplify_calculations; finish.
    replace (file <=? file + n0) with true; try symmetry; 
    try rewrite PeanoNat.Nat.leb_le; try lia.
    destruct n0. simplify_calculations. finish.
    replace (rank <=? rank - S n0) with false; try symmetry; 
    try rewrite PeanoNat.Nat.leb_gt; try lia.
    replace (file + S n0 - file) with (S n0); try lia.
    replace (rank - (rank - S n0)) with (S n0); try lia. finish.
Qed.

Lemma vector_from_a_to_b_correct : forall l1 l2,
  apply_vector (vector_from_a_to_b l1 l2) l1 = l2.
Proof.
  intros l1 l2.
  destruct l1 eqn:El1.
  destruct l2 eqn:El2.
  simpl. destruct (file <=? file0) eqn:Efl.
  - Hb2p. destruct (rank <=? rank0) eqn:Ernk; Hb2p; simpl; apply eq_Loc; lia.
  - Hb2p. destruct (rank <=? rank0) eqn:Ernk; Hb2p; simpl; apply eq_Loc; lia.
Qed.

Lemma make_vector_stay_in_bounds_stays_in_bounds : forall v l,
  location_valid l ->
  vector_stays_within_boundaries (make_vector_stay_in_bounds v l) l.
Proof.
  intros.
  unfold location_valid in *.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
  - split. apply PeanoNat.Nat.le_min_r. repeat (destruct rank; try lia).
  - split. apply PeanoNat.Nat.le_min_r. apply PeanoNat.Nat.le_min_r.
  - split; repeat DGmatch; simpl; try lia.
  - repeat DGmatch; simpl; try lia.
Qed.

Lemma one_step_stays_in_bounds : forall v l v0 l0,
  vector_stays_within_boundaries v l ->
  one_step_along_vector_and_location l v = (v0, l0) ->
  vector_stays_within_boundaries v0 l0.
Proof.
  intros v l v0 l0 Hbounds Hos.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; inversion Hos; subst; auto.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
  - simpl in Hbounds. Hdestruct; inversion H0; subst; simpl; auto; lia.
Qed.

Lemma  make_vector_stay_in_bounds_eq : forall v l,
  location_valid l -> location_valid (apply_vector v l) ->
  apply_vector v l = apply_vector (make_vector_stay_in_bounds v l) l.
Proof.
  intros.
  unfold location_valid in *.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; simpl in H0; auto.
  - subst. apply eq_Loc; auto. repeat (destruct rank; try lia). lia.
  - subst. apply eq_Loc; auto; lia.
  - subst. apply eq_Loc; auto. repeat (destruct rank; try lia).
    repeat (destruct file; try lia).
  - subst. apply eq_Loc; auto. lia. repeat (destruct file; try lia).
Qed.

Lemma one_step_same : forall start v s v0,
  one_step_along_vector_and_location start v = (v0, s) ->
  one_step_along_vector start v = s.
Proof.
  intros start v s v0 Hosvl.
  destruct start eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; simpl in Hosvl; subst; auto;
  destruct n eqn:En; destruct n0 eqn:En0; inversion Hosvl; auto.
Qed.

Lemma one_step_apply_same : forall start v,
  one_step_along_vector start v =
  one_step_along_vector start (vector_from_a_to_b start 
    (apply_vector v start)).
Proof.
  intros. 
  destruct start eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
  - destruct n eqn:En.
    + simplify_calculations.
      replace (rank <=? rank + n0) with true; try symmetry; 
      try rewrite PeanoNat.Nat.leb_le; try lia.
      replace (rank + n0 - rank) with n0; try lia.
      destruct n0 eqn:En0; auto.
    + destruct n0 eqn:En0; simpl; destruct (file <=? file - S n1) eqn:Efl.
      * rewrite PeanoNat.Nat.leb_le in Efl.
        assert (Hfl2: file = 0). lia. subst. simpl.
        simplify_calculations. auto.
      * subst. rewrite PeanoNat.Nat.leb_gt in Efl.
        destruct (file - (file - S n1)) eqn:Hfl2; try lia.
        simplify_calculations. auto.
      * rewrite PeanoNat.Nat.leb_le in Efl. 
        assert (Hfl2: file = 0). lia. subst. simpl. 
        replace (rank <=? rank + S n2) with true; try symmetry; 
        try rewrite PeanoNat.Nat.leb_le; try lia.
        replace (rank + S n2 - rank) with (S n2); try lia. auto.
      * subst. rewrite PeanoNat.Nat.leb_gt in Efl.
        destruct (file - (file - S n1)) eqn:Hfl2; try lia.
        replace (rank <=? rank + S n2) with true; try symmetry; 
        try rewrite PeanoNat.Nat.leb_le; try lia.
        replace (rank + S n2 - rank) with (S n2); try lia. auto.
  - destruct n eqn:En.
    + simplify_calculations. destruct n0 eqn:En0. simplify_calculations. auto.
      destruct (rank <=? rank - S n) eqn:Ernk.
      * Hb2p. assert (Hrnk2: rank = 0). lia. rewrite Hrnk2. simpl. auto.
      * Hb2p. destruct (rank - (rank - S n)) eqn:Ernk2; try lia. auto.
    + destruct n0 eqn:En0.
      * simplify_calculations. destruct (file <=? file - S n1) eqn:Hfl.
        -- Hb2p. assert (Hfl2: file = 0). lia. rewrite Hfl2. simpl. auto.
        -- Hb2p. destruct (file - (file - S n1)) eqn:Efl2; try lia. auto.
      * destruct (file <=? file - S n1) eqn:Hfl.
        -- Hb2p. assert (Hfl2: file = 0). lia. rewrite Hfl2. simpl.
           destruct (rank <=? rank - S n2) eqn:Hrnk.
           ++ Hb2p. assert (Hrnk2: rank = 0). lia. rewrite Hrnk2. simpl. auto.
           ++ Hb2p. destruct (rank - (rank - S n2)) eqn:Hrnk2; try lia. auto.
        -- Hb2p. destruct (file - (file - S n1)) eqn:Hfl2; try lia.
           destruct (rank <=? rank - S n2) eqn:Hrnk.
           ++ Hb2p. assert (Hrnk2: rank = 0). lia. rewrite Hrnk2. simpl. auto.
           ++ Hb2p. destruct (rank - (rank - S n2)) eqn:Hrnk2; try lia. auto.
  - destruct n eqn:En.
    + simplify_calculations. destruct n0 eqn:En0. simplify_calculations. auto.
      replace (rank <=? rank + S n) with true; try Gb2p; try lia.
      replace (rank + S n - rank) with (S n); try lia. auto.
    + destruct n0 eqn:En0. 
      * simplify_calculations. auto.
        replace (file <=? file + S n1) with true; try Gb2p; try lia.
        replace (file + S n1 - file) with (S n1); try lia. auto.
      * replace (file <=? file + S n1) with true; try Gb2p; try lia.
        replace (file + S n1 - file) with (S n1); try lia. auto.
        replace (rank <=? rank + S n2) with true; try Gb2p; try lia.
        replace (rank + S n2 - rank) with (S n2); try lia. auto.
  - destruct n eqn:En.
    + simplify_calculations. destruct n0 eqn:En0. simplify_calculations. auto.
      destruct (rank <=? rank - S n) eqn:Hrnk.
      * Hb2p. assert (Hrnk2: rank = 0). lia. rewrite Hrnk2. simpl. auto.
      * Hb2p. destruct (rank - (rank - S n)) eqn:Hrnk2; try lia. auto.
    + destruct n0 eqn:En0. 
      * simplify_calculations. auto.
        replace (file <=? file + S n1) with true; try Gb2p; try lia.
        replace (file + S n1 - file) with (S n1); try lia. auto.
      * replace (file <=? file + S n1) with true; try Gb2p; try lia.
        replace (file + S n1 - file) with (S n1); try lia. auto.
        destruct (rank <=? rank - S n2) eqn:Hrnk.
        -- Hb2p. assert (Hrnk2: rank = 0). lia. rewrite Hrnk2. simpl. auto.
        -- Hb2p. destruct (rank - (rank - S n2)) eqn:Hrnk2; try lia. auto.
Qed.

Lemma are_squares_along_vector_empty_sound_aux : forall n,
  forall pp v start,
  n = vector_length v ->
  are_squares_along_vector_empty pp start v = true ->
  (vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))).
Proof.
  induction n using strong_induction.
  intros pp v start Hvlength Hemptyv. 
  rewrite are_squares_along_vector_empty_equation in Hemptyv. 
  destruct n eqn:En. left. auto.
  replace (vector_length v =? 0) with false in Hemptyv; try symmetry;
  try rewrite PeanoNat.Nat.eqb_neq; try lia.
  assert (Hvnot0: vector_length v <> 0). lia.
  right.
  destruct (one_step_along_vector_and_location start v) eqn:Eos.
  destruct (is_square_empty start pp) eqn:Eisempty; try discriminate.
  split; auto.
  assert (Hvlv0: vector_length v0 < S n0). { rewrite Hvlength.
    eapply one_step_along_vector_and_location_shorter; eauto.
  }
  assert (Hduh: vector_length v0 = vector_length v0). { auto. }
  specialize (H (vector_length v0) Hvlv0 pp v0 s Hduh Hemptyv) as Hind.
  destruct Hind as [Hind | Hind].
  - specialize (one_step_along_vector_and_location_last_step start v v0 s Eos 
      Hvnot0 Hind) as Hlaststep. subst.
    specialize (one_step_along_vector_and_location_adjacent _ _ _ _ Eos) 
      as Hadj.
    destruct Hadj as [Hequal | Hadj].
    + rewrite <- Hequal. apply NothingOccupiedBetweenSingleSquare.
    + constructor. auto.
  - eapply SquaresAlongVectorEmpty; eauto.
    + rewrite <- one_step_apply_same. replace (one_step_along_vector start v) with s.
      apply Hind. symmetry. apply (one_step_same start v s v0). auto.
    + rewrite <- one_step_apply_same. rewrite (one_step_same start v s v0); auto.
      erewrite one_step_along_vector_and_location_correct. apply Hind. auto.
Qed.

Lemma are_squares_along_vector_empty_sound : forall pp v start,
  are_squares_along_vector_empty pp start v = true ->
  (vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))).
Proof.
  intros.
  apply are_squares_along_vector_empty_sound_aux with (n:=vector_length v).
  auto. auto.
Qed.

Lemma one_step_along_short_vector : forall v l v0 l0,
  vector_stays_within_boundaries v l ->
  one_step_along_vector_and_location l v = (v0,l0) ->
  SquaresAdjacent l (apply_vector v l) ->
  vector_length v0 = 0.
Proof.
  intros v l v0 l0 Hbounds Hos Hadj.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
  - simpl in Hos. simpl in Hadj. Hdestruct; unfold difference in Hadj; 
    destruct Hadj as [Hadj1 [Hadj2a Hadj2b]].
    + inversion Hos. subst. simpl. auto.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. lia.
    + HreplaceInIf. inversion Hos. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
  - simpl in Hos. simpl in Hadj. Hdestruct; 
    destruct Hadj as [Hadj1 [Hadj2a Hadj2b]]; unfold difference in *.
    + inversion Hos. simpl. auto.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
  - simpl in Hos. simpl in Hadj. Hdestruct; 
    destruct Hadj as [Hadj1 [Hadj2a Hadj2b]]; unfold difference in *.
    + inversion Hos. simpl. auto.
    + HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
  - simpl in Hos. simpl in Hadj. Hdestruct; 
    destruct Hadj as [Hadj1 [Hadj2a Hadj2b]]; unfold difference in *.
    + inversion Hos. simpl. auto.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
    + repeat HreplaceInIf. inversion Hos. subst. simpl. simpl in Hbounds. lia.
Qed.

Lemma apply_vector_idem: forall v l,
  vector_stays_within_boundaries v l -> apply_vector v l = l -> 
  vector_length v = 0.
Proof.
  intros v l Hbounds Hidem.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto; subst;
  simpl in Hidem; simpl in Hbounds; inversion Hidem; lia.
Qed.

Lemma are_squares_along_vector_empty_complete_aux : forall n,
  forall pp v start,
  (vector_length v) = n ->
  vector_stays_within_boundaries v start ->
  ((vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))) ->
  are_squares_along_vector_empty pp start v = true).
Proof.
  induction n using strong_induction.
  intros pp v start Hvl Hbounds [Hv0 | [Hfstempty Hrestempty]]; 
  rewrite are_squares_along_vector_empty_equation. Hp2b. rewrite Hv0. auto.
  destruct (vector_length v =? 0) eqn:Evl; auto. Hb2p.
  destruct (one_step_along_vector_and_location start v) eqn:Eos.
  rewrite Hfstempty. apply H with (k:=vector_length v0). rewrite <- Hvl.
  eapply one_step_along_vector_and_location_shorter; eauto. auto.
  apply (one_step_stays_in_bounds v start v0 s Hbounds Eos).
  inversion Hrestempty.
  - subst. left. eapply one_step_along_short_vector; eauto.
  - exfalso. apply Evl. eapply apply_vector_idem; eauto.
  - assert (Hfst_s: first_step = s). { subst. rewrite <- one_step_apply_same.
      eapply one_step_same. apply Eos.
    }
    right. rewrite Hfst_s in H2. split; auto. rewrite Hfst_s in H3.
    rewrite <- (one_step_along_vector_and_location_correct _ _ _ _ Eos). auto.
Qed.

Lemma are_squares_along_vector_empty_complete : forall pp v start,
  vector_stays_within_boundaries v start ->
  ((vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))) ->
  are_squares_along_vector_empty pp start v = true).
Proof.
  intros.
  apply are_squares_along_vector_empty_complete_aux with (n:=vector_length v);
  auto.
Qed.

Lemma vector_from_a_to_b_in_bounds : forall l1 l2,
  location_valid l1 -> location_valid l2 ->
  vector_stays_within_boundaries (vector_from_a_to_b l1 l2) l1.
Proof.
  intros l1 l2.
  unfold location_valid in *.
  destruct l1 eqn:El1.
  destruct l2 eqn:El2.
  simpl. destruct (rank <=? rank0) eqn:Ernk;
  repeat DGmatch; repeat DHif; repeat Hb2p; intros; try inversion E; try lia.
Qed.

Lemma are_squares_along_vector_empty_correct : forall pp v start,
  vector_stays_within_boundaries v start ->
  ((vector_length v) = 0 \/ 
  (is_square_empty start pp = true /\ 
    (SquaresBetweenEmpty pp start (apply_vector v start))) <->
  are_squares_along_vector_empty pp start v = true).
Proof.
  intros. split.
  - apply are_squares_along_vector_empty_complete. auto.
  - apply are_squares_along_vector_empty_sound.
Qed.

Lemma vector_from_a_to_b_zero_iff : forall l1 l2, 
  vector_length (vector_from_a_to_b l1 l2) = 0 <-> l1 = l2.
Proof.
  intros l1 l2. split.
  - intros Hlen0. rewrite <- (vector_from_a_to_b_correct l1 l2).
    symmetry. apply apply_null_vector. auto.
  - intros Heq. rewrite Heq. destruct l2 eqn:El2. simpl.
    replace (rank <=? rank) with true; try Gb2p; try lia.
    replace (file <=? file) with true; try Gb2p; try lia.
Qed.

Lemma are_squares_between_empty_sound : forall pp l1 l2,
  are_squares_between_empty pp l1 l2 = true -> SquaresBetweenEmpty pp l1 l2.
Proof.
  intros pp l1 l2 Htrue.
  unfold are_squares_between_empty in *.
  destruct (one_step_along_vector_and_location l1 (vector_from_a_to_b l1 l2))
    eqn:Eos.
  apply are_squares_along_vector_empty_sound in Htrue.
  destruct (vector_length (vector_from_a_to_b l1 l2)) eqn:El1l2len.
  - rewrite vector_from_a_to_b_zero_iff in El1l2len. rewrite El1l2len.
    apply NothingOccupiedBetweenSingleSquare.
  - destruct Htrue as [Hv0 | Halong].
    + assert (HsIsl2: s = l2). { rewrite <- (vector_from_a_to_b_correct l1 l2).
        rewrite (one_step_along_vector_and_location_correct _ _ _ _ Eos).
        rewrite apply_null_vector; auto.
      }
      destruct (one_step_along_vector_and_location_adjacent _ _ _ _ Eos) as
        [Hsame | Hadj]. subst. apply NothingOccupiedBetweenSingleSquare.
      subst. constructor; auto.
    + destruct Halong as [Hfstempty Hrestempty].
      apply (SquaresAlongVectorEmpty pp l1 l2 (vector_from_a_to_b l1 l2) s);
      auto.
      * eapply one_step_same; eauto.
      * rewrite <- (vector_from_a_to_b_correct l1 l2).
        rewrite (one_step_along_vector_and_location_correct _ _ _ _ Eos). auto.
Qed.

Lemma one_step_along_zero : forall v l,
  vector_length v = 0 ->
  one_step_along_vector_and_location l v = (v, l).
Proof.
  intros v l Hlen.
  destruct l eqn:El.
  destruct v eqn:Ev.
  destruct hstep eqn:Ehstep.
  destruct vstep eqn:Evstep.
  rewrite vector_length_0_iff in Hlen. destruct Hlen as [Hlen1 Hlen2]. subst.
  simpl. destruct d eqn:Ed; destruct d0 eqn:Ed0; simpl; auto.
Qed.

Lemma are_squares_between_empty_complete : forall pp l1 l2,
  location_valid l1 -> location_valid l2 ->
  SquaresBetweenEmpty pp l1 l2 -> are_squares_between_empty pp l1 l2 = true.
Proof.
  intros pp l1 l2 Hv1 Hv2 Hempty. unfold are_squares_between_empty.
  destruct (one_step_along_vector_and_location l1 (vector_from_a_to_b l1 l2))
    eqn:Eos.
  inversion Hempty.
  - subst. assert (Hv0: vector_length v = 0). { 
      apply (one_step_along_short_vector (vector_from_a_to_b l1 l2) l1 v s);
      auto. apply vector_from_a_to_b_in_bounds; auto.
      rewrite (vector_from_a_to_b_correct l1 l2). auto.
    }
    rewrite are_squares_along_vector_empty_equation. Hp2b. rewrite Hv0. auto.
  - subst. assert (Hl1l2zero: vector_length (vector_from_a_to_b l2 l2) = 0).
    { apply vector_from_a_to_b_zero_iff. auto. }
    assert (Hosidem : one_step_along_vector_and_location l2 (vector_from_a_to_b l2 l2)
      = (vector_from_a_to_b l2 l2, l2)). { apply one_step_along_zero. auto. }
    rewrite Eos in Hosidem. inversion Hosidem. subst.
    rewrite are_squares_along_vector_empty_equation. Hp2b. rewrite Hl1l2zero.
    auto.
  - subst. apply are_squares_along_vector_empty_complete.
    + eapply one_step_stays_in_bounds. apply vector_from_a_to_b_in_bounds. apply Hv1.
      apply Hv2. apply Eos.
    + right. split. rewrite (one_step_same _ _ _ _ Eos) in H1. auto.
      rewrite (one_step_same _ _ _ _ Eos) in H2. 
      rewrite <- (one_step_along_vector_and_location_correct _ _ _ _ Eos).
      rewrite vector_from_a_to_b_correct. auto.
Qed.

Lemma are_squares_between_empty_correct : forall pp l1 l2,
  location_valid l1 -> location_valid l2 ->
  SquaresBetweenEmpty pp l1 l2 <-> are_squares_between_empty pp l1 l2 = true.
Proof.
  intros. split.
  - intros. apply are_squares_between_empty_complete; auto.
  - intros. apply are_squares_between_empty_sound; auto.
Qed.

Lemma are_squares_on_same_diagonal_trans : forall l1 l2 l3,
  are_squares_on_same_diagonal l1 l2 = true ->
  are_squares_on_same_diagonal l2 l3 = true ->
  are_squares_on_same_diagonal l1 l3 = true.
Proof.
  intros l1 l2 l3 Hl1l2 Hl2l3. destruct l1 eqn:Hl1. destruct l2 eqn:Hl2.
  destruct l3 eqn:Hl3. unfold are_squares_on_same_diagonal in *. simpl in *.
  repeat diagonal_destruct.
Qed.

Lemma are_squares_on_same_antidiagonal_trans : forall l1 l2 l3,
  are_squares_on_same_antidiagonal l1 l2 = true ->
  are_squares_on_same_antidiagonal l2 l3 = true ->
  are_squares_on_same_antidiagonal l1 l3 = true.
Proof.
  intros l1 l2 l3 Hl1l2 Hl2l3. destruct l1 eqn:Hl1. destruct l2 eqn:Hl2.
  destruct l3 eqn:Hl3. unfold are_squares_on_same_antidiagonal in *. 
  simpl in *. repeat diagonal_destruct.
Qed.

Lemma squares_along_direction_aux_soundRU : forall s l1 l2,
  In l2 (squares_along_direction_aux l1 Right Up s) -> 
  (are_squares_on_same_diagonal l1 l2) = true.
Proof.
  induction s.
  - intros l1 l2 Hin. simpl in Hin. contradiction.
  - intros l1 l2 Hin. destruct l1 eqn:El1. destruct l2 eqn:El2.
    assert (Honestep: are_squares_on_same_diagonal (Loc rank file) 
      (Loc (rank + 1) (file + 1)) = true). { 
      unfold are_squares_on_same_diagonal. simpl. 
      repeat rewrite n_leb_n_plus_1. repeat rewrite n_plus_m_minus_n.
      simpl. auto.
    }
    simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin. subst. auto.
    + specialize (IHs _ _ Hin) as IHss. 
      eapply are_squares_on_same_diagonal_trans. apply Honestep. apply IHss.
Qed.

Lemma are_squares_on_same_diagonal_one_stepLD : forall rank file,
  rank >= 1 -> file >= 1 ->
  are_squares_on_same_diagonal (Loc rank file) (Loc (rank - 1) (file - 1)) 
    = true.
Proof.
  intros rank file Hrnk Hfl.
  unfold are_squares_on_same_diagonal. simpl.
  replace (file <=? file - 1) with false; try Gb2p; try lia.
  replace (rank <=? rank - 1) with false; try Gb2p; try lia.
  repeat rewrite n_minus_n_minus_m; simpl; auto; lia. 
Qed.

Lemma are_squares_on_same_antidiagonal_one_stepLU : forall rank file,
  file >= 1 ->
  are_squares_on_same_antidiagonal (Loc rank file) (Loc (rank + 1) (file - 1))
    = true.
Proof.
  intros rank file Hfl.
  unfold are_squares_on_same_antidiagonal. simpl.
  replace (file <=? file - 1) with false; try Gb2p; try lia.
  rewrite n_leb_n_plus_1.
  repeat rewrite n_minus_n_minus_m; try lia. rewrite n_plus_m_minus_n. simpl.
  auto.
Qed.

Lemma are_squares_on_same_antidiagonal_one_stepRD : forall rank file,
  rank >= 1 ->
  are_squares_on_same_antidiagonal (Loc rank file) (Loc (rank - 1) (file + 1))
    = true.
Proof.
  intros rank file Hrnk.
  unfold are_squares_on_same_antidiagonal. simpl.
  rewrite n_leb_n_plus_1.
  replace (rank <=? rank - 1) with false; try Gb2p; try lia.
  rewrite n_plus_m_minus_n. simpl. rewrite n_minus_n_minus_m; try lia.
Qed.

Lemma squares_along_direction_aux_soundLD : forall s rank file l2,
  s <= rank -> s <= file ->
  In l2 (squares_along_direction_aux (Loc rank file) Left Down s) -> 
  (are_squares_on_same_diagonal (Loc rank file) l2) = true.
Proof.
  induction s; intros rank file l2 Hsleqr Hsleqf Hin. 
  - simpl in Hin. contradiction.
  - destruct l2 eqn:El2.
    simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin. subst. apply are_squares_on_same_diagonal_one_stepLD; lia.
    + assert (Hsleqr2: s <= rank - 1). lia. 
      assert (Hsleql2: s <= file - 1). lia.
      specialize (IHs _ _ _ Hsleqr2 Hsleql2 Hin) as IHss.
      eapply are_squares_on_same_diagonal_trans.
      apply are_squares_on_same_diagonal_one_stepLD; try lia. auto.
Qed.

Lemma squares_along_direction_aux_soundLU : forall s rank file l2,
  s <= file ->
  In l2 (squares_along_direction_aux (Loc rank file) Left Up s) -> 
  (are_squares_on_same_antidiagonal (Loc rank file) l2) = true.
Proof.
  induction s; intros rank file l2 Hsleqf Hin. 
  - simpl in Hin. contradiction.
  - destruct l2 eqn:El2.
    simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin. subst. apply are_squares_on_same_antidiagonal_one_stepLU;
      lia.
    + assert (Hsleql2: s <= file - 1). lia.
      specialize (IHs _ _ _ Hsleql2 Hin) as IHss.
      eapply are_squares_on_same_antidiagonal_trans.
      apply are_squares_on_same_antidiagonal_one_stepLU; try lia. auto.
Qed.

Lemma squares_along_direction_aux_soundRD : forall s rank file l2,
  s <= rank ->
  In l2 (squares_along_direction_aux (Loc rank file) Right Down s) -> 
  (are_squares_on_same_antidiagonal (Loc rank file) l2) = true.
Proof.
  induction s; intros rank file l2 Hsleqr Hin. 
  - simpl in Hin. contradiction.
  - destruct l2 eqn:El2.
    simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin. subst. apply are_squares_on_same_antidiagonal_one_stepRD;
      lia.
    + assert (Hsleqr2: s <= rank - 1). lia. 
      specialize (IHs _ _ _ Hsleqr2 Hin) as IHss.
      eapply are_squares_on_same_antidiagonal_trans.
      apply are_squares_on_same_antidiagonal_one_stepRD; try lia. auto.
Qed.

Lemma squares_along_direction_soundRU : forall l1 l2,
  In l2 (squares_along_direction l1 Right Up) -> 
  (are_squares_on_same_diagonal l1 l2) = true.
Proof.
  intros l1 l2 Hin.
  destruct l1 eqn:Hl1. destruct l2 eqn:Hl2.
  unfold squares_along_direction in Hin. 
  eapply squares_along_direction_aux_soundRU. apply Hin.
Qed.

Lemma squares_along_direction_soundLD : forall l1 l2,
  In l2 (squares_along_direction l1 Left Down) -> 
  (are_squares_on_same_diagonal l1 l2) = true.
Proof.
  intros l1 l2 Hin.
  destruct l1 eqn:Hl1. destruct l2 eqn:Hl2.
  unfold squares_along_direction in Hin.
  apply squares_along_direction_aux_soundLD with (s:=(min file rank)); try lia.
  auto.
Qed.

Lemma squares_along_direction_soundRD : forall l1 l2,
  In l2 (squares_along_direction l1 Right Down) -> 
  (are_squares_on_same_antidiagonal l1 l2) = true.
Proof.
  intros l1 l2 Hin.
  destruct l1 eqn:Hl1. destruct l2 eqn:Hl2.
  unfold squares_along_direction in Hin.
  apply squares_along_direction_aux_soundRD with (s:=(min (7 - file) rank)); 
  try lia. auto.
Qed.

Lemma squares_along_direction_soundLU : forall l1 l2,
  In l2 (squares_along_direction l1 Left Up) -> 
  (are_squares_on_same_antidiagonal l1 l2) = true.
Proof.
  intros l1 l2 Hin.
  destruct l1 eqn:Hl1. destruct l2 eqn:Hl2.
  unfold squares_along_direction in Hin.
  apply squares_along_direction_aux_soundLU with (s:=(min file (7-rank))); 
  try lia. auto.
Qed.

Lemma squares_on_same_diagonal_sound : forall l1 l2,
  In l2 (squares_on_same_diagonal l1) -> 
  (are_squares_on_same_diagonal l1 l2) = true.
Proof.
  intros l1 l2 Hin.
  unfold squares_on_same_diagonal in Hin. in_app_to_or.
  destruct Hin as [Hin | Hin].
  - apply squares_along_direction_soundRU. auto.
  - apply squares_along_direction_soundLD. auto.
Qed.

Lemma squares_on_same_antidiagonal_sound : forall l1 l2,
  In l2 (squares_on_same_antidiagonal l1) -> 
  (are_squares_on_same_antidiagonal l1 l2) = true.
Proof.
  intros l1 l2 Hin.
  unfold squares_on_same_antidiagonal in Hin. in_app_to_or.
  destruct Hin as [Hin | Hin].
  - apply squares_along_direction_soundRD. auto.
  - apply squares_along_direction_soundLU. auto.
Qed.

Lemma squares_along_direction_aux_completeRU: forall d s rank file rank1 file1,
  rank <= 7 -> file <= 7 -> rank1 <= 7 -> file1 <= 7 ->
  file <= file1 -> rank <= rank1 -> d = file1 - file -> d = rank1 - rank ->
  d >= 1 -> s >= d -> 
  In (Loc rank1 file1) (squares_along_direction_aux (Loc rank file) Right Up s).
Proof.
  induction d. intros. lia.
  intros s rank file rank1 file1 Hrb Hfb Hr1b Hf1b Hff1 Hrr1 Hd1 Hd2 Hdge1
    Hs.
  destruct s eqn:Es; try lia. simpl.
  destruct (rank + 1 =? rank1) eqn:Erp1r1; Hb2p. left. apply eq_Loc; lia.
  right. apply IHd; try lia.
Qed.

Lemma squares_along_direction_aux_completeLD: forall d s rank file rank1 file1,
  rank <= 7 -> file <= 7 -> rank1 <= 7 -> file1 <= 7 ->
  file1 < file -> rank1 < rank -> d = file - file1 -> d = rank - rank1 ->
  d >= 1 -> s >= d -> 
  In (Loc rank1 file1) (squares_along_direction_aux (Loc rank file) Left Down s).
Proof.
  induction d. intros. lia.
  intros s rank file rank1 file1 Hrb Hfb Hr1b Hf1b Hff1 Hrr1 Hd1 Hd2 Hdge1
    Hs.
  destruct s eqn:Es; try lia. simpl.
  destruct (rank - 1 =? rank1) eqn:Erp1r1; Hb2p. left. apply eq_Loc; lia.
  right. apply IHd; try lia.
Qed.

Lemma squares_along_direction_aux_completeRD: forall d s rank file rank1 file1,
  rank <= 7 -> file <= 7 -> rank1 <= 7 -> file1 <= 7 ->
  file <= file1 -> rank1 < rank -> d = file1 - file -> d = rank - rank1 ->
  d >= 1 -> s >= d -> 
  In (Loc rank1 file1) (squares_along_direction_aux (Loc rank file) Right Down s).
Proof.
  induction d. intros. lia.
  intros s rank file rank1 file1 Hrb Hfb Hr1b Hf1b Hff1 Hrr1 Hd1 Hd2 Hdge1
    Hs.
  destruct s eqn:Es; try lia. simpl.
  destruct (rank - 1 =? rank1) eqn:Erp1r1; Hb2p. left. apply eq_Loc; lia.
  right. apply IHd; try lia.
Qed.

Lemma squares_along_direction_aux_completeLU: forall d s rank file rank1 file1,
  rank <= 7 -> file <= 7 -> rank1 <= 7 -> file1 <= 7 ->
  file1 < file -> rank <= rank1 -> d = file - file1 -> d = rank1 - rank ->
  d >= 1 -> s >= d -> 
  In (Loc rank1 file1) (squares_along_direction_aux (Loc rank file) Left Up s).
Proof.
  induction d. intros. lia.
  intros s rank file rank1 file1 Hrb Hfb Hr1b Hf1b Hff1 Hrr1 Hd1 Hd2 Hdge1
    Hs.
  destruct s eqn:Es; try lia. simpl.
  destruct (rank + 1 =? rank1) eqn:Erp1r1; Hb2p. left. apply eq_Loc; lia.
  right. apply IHd; try lia.
Qed.

Lemma squares_on_same_diagonal_complete : forall l1 l2,
  location_valid l1 -> location_valid l2 -> l1 <> l2 -> 
  (are_squares_on_same_diagonal l1 l2) = true ->
  In l2 (squares_on_same_diagonal l1).
Proof.
  intros l1 l2 Hv1 Hv2 Huneq Hason.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst.
  unfold are_squares_on_same_diagonal in *. simpl in *.
  repeat diagonal_destruct; unfold squares_on_same_diagonal; in_app_to_or.
  - left. eapply squares_along_direction_aux_completeRU; eauto; try lia.
    destruct (file0 =? file) eqn:Ef0f; Hb2p; try lia. exfalso. apply Huneq. 
    apply eq_Loc; auto; lia.
  - right. eapply squares_along_direction_aux_completeLD; eauto; try lia.
Qed.

Lemma squares_on_same_antidiagonal_complete : forall l1 l2,
  location_valid l1 -> location_valid l2 -> l1 <> l2 -> 
  (are_squares_on_same_antidiagonal l1 l2) = true ->
  In l2 (squares_on_same_antidiagonal l1).
Proof.
  intros l1 l2 Hv1 Hv2 Huneq Hason.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst.
  unfold are_squares_on_same_antidiagonal in *. simpl in *.
  unfold squares_on_same_antidiagonal. repeat diagonal_destruct; in_app_to_or.
  - exfalso. apply Huneq. apply eq_Loc; lia.
  - left. eapply squares_along_direction_aux_completeRD; eauto; try lia.
  - right. eapply squares_along_direction_aux_completeLU; eauto; try lia.
Qed.

Lemma squares_along_direction_aux_validRU : forall s rank file rank0 file0,
  In (Loc rank0 file0) (squares_along_direction_aux (Loc rank file) Right Up s)
  -> rank0 <= rank + s /\ file0 <= file + s.
Proof.
  induction s; intros rank file rank0 file0 Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin; destruct Hin as [Hin | Hin]; try inversion Hin; subst; 
    try lia; specialize (IHs _ _ _ _ Hin) as Hin2; lia.
Qed.

Lemma squares_along_direction_aux_validRD : forall s rank file rank0 file0,
  In (Loc rank0 file0) (squares_along_direction_aux (Loc rank file) Right Down s)
  -> rank0 <= rank /\ file0 <= file + s.
Proof.
  induction s; intros rank file rank0 file0 Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin; destruct Hin as [Hin | Hin]; try inversion Hin; subst; 
    try lia; specialize (IHs _ _ _ _ Hin) as Hin2; lia.
Qed.

Lemma squares_along_direction_aux_validLU : forall s rank file rank0 file0,
  In (Loc rank0 file0) (squares_along_direction_aux (Loc rank file) Left Up s)
  -> rank0 <= rank + s /\ file0 <= file.
Proof.
  induction s; intros rank file rank0 file0 Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin; destruct Hin as [Hin | Hin]; try inversion Hin; subst; 
    try lia; specialize (IHs _ _ _ _ Hin) as Hin2; lia.
Qed.

Lemma squares_along_direction_aux_validLD : forall s rank file rank0 file0,
  In (Loc rank0 file0) (squares_along_direction_aux (Loc rank file) Left Down s)
  -> rank0 <= rank /\ file0 <= file.
Proof.
  induction s; intros rank file rank0 file0 Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin; destruct Hin as [Hin | Hin]; try inversion Hin; subst; 
    try lia; specialize (IHs _ _ _ _ Hin) as Hin2; lia.
Qed.

Lemma squares_along_direction_valid : forall l1 l2 hd vd,
  location_valid l1 -> In l2 (squares_along_direction l1 hd vd) ->
  location_valid l2.
Proof.
  intros l1 l2 hd vd Hv Hin.
  unfold squares_along_direction in *.
  unfold location_valid in Hv.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst. simpl.
  destruct hd eqn:Ehd; destruct vd eqn:Evd; subst.
  - specialize (squares_along_direction_aux_validLU _ _ _ _ _ Hin) as Hin2.
    lia.
  - specialize (squares_along_direction_aux_validLD _ _ _ _ _ Hin) as Hin2.
    lia.
  - specialize (squares_along_direction_aux_validRU _ _ _ _ _ Hin) as Hin2.
    lia.
  - specialize (squares_along_direction_aux_validRD _ _ _ _ _ Hin) as Hin2.
    lia.
Qed.

Lemma squares_on_same_diagonal_valid : forall l1 l2,
  location_valid l1 -> In l2 (squares_on_same_diagonal l1) -> 
  location_valid l2.
Proof.
  intros l1 l2 Hvalid Hin.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst.
  unfold squares_on_same_diagonal in Hin. in_app_to_or.
  destruct Hin as [Hin | Hin]; eapply squares_along_direction_valid; eauto.
Qed.

Lemma squares_on_same_antidiagonal_valid : forall l1 l2,
  location_valid l1 -> In l2 (squares_on_same_antidiagonal l1) -> 
  location_valid l2.
Proof.
  intros l1 l2 Hvalid Hin.
  destruct l1 eqn:El1. destruct l2 eqn:El2. subst.
  unfold squares_on_same_antidiagonal in Hin. in_app_to_or.
  destruct Hin as [Hin | Hin]; eapply squares_along_direction_valid; eauto.
Qed.

Lemma does_vector_stay_within_boundaries_correct : forall from v,
  location_valid from ->
  does_vector_stay_within_boundaries v from = true ->
  location_valid (apply_vector v from).
Proof.
  intros. unfold location_valid in *. destruct v. destruct hstep. 
  destruct vstep. simpl in *; destruct d0; destruct d; destruct from; 
  simpl in H0; Hb2p; HdAnd; repeat Hb2p; lia.
Qed.

Lemma does_vector_stay_within_boundaries_iff : forall from v,
  does_vector_stay_within_boundaries v from = true <->
  vector_stays_within_boundaries v from.
Proof.
  intros from v. split; intros H.
  - unfold vector_stays_within_boundaries. repeat DGmatch; simpl in *; Hb2p; 
    destruct H as [H1 H2]; repeat Hb2p; auto.
  - unfold vector_stays_within_boundaries in *. repeat DHmatch; simpl in *;
    Gb2p; split; Gb2p; lia; Gb2p; lia.
Qed.

Lemma in_target_squares : forall from to vs,
  location_valid from -> location_valid to -> 
  In (vector_from_a_to_b from to) vs ->
  In to (target_squares from vs).
Proof.
  intros from to. induction vs; intros Hvf Hvt Hin. HinNil.
  inversion Hin; subst.
  - simpl. 
    replace (does_vector_stay_within_boundaries (vector_from_a_to_b from to) from)
    with true.
    + rewrite vector_from_a_to_b_correct. apply in_eq.
    + symmetry. rewrite does_vector_stay_within_boundaries_iff.
      apply vector_from_a_to_b_in_bounds; auto.
  - simpl. DGif; try apply in_cons; apply IHvs; auto.
Qed.
