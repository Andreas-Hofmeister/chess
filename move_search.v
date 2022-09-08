Require Import List.
Require Import Nat.
From CHESS Require Export legal_moves.

Inductive Integer : Set :=
  | PosInt (n : nat)
  | NegInt (n : nat).

Definition inteq (a b : Integer) : bool :=
  match a,b with
  | PosInt p, PosInt q => (p =? q)
  | NegInt p, NegInt q => (p =? q)
  | PosInt p, NegInt q => if (andb (p =? 0) (q =? 0)) then true else false
  | NegInt p, PosInt q => if (andb (p =? 0) (q =? 0)) then true else false
  end.

Definition intleq (a b : Integer) : bool :=
  match a,b with
  | PosInt p, PosInt q => (p <=? q)
  | NegInt p, NegInt q => (q <=? p)
  | PosInt p, NegInt q => false
  | NegInt p, PosInt q => true
  end.

Definition intneg (a : Integer) : Integer :=
  match a with
  | PosInt p => NegInt p
  | NegInt p => PosInt p
  end.

Definition intadd (a b : Integer) : Integer :=
  match a, b with
  | PosInt p, PosInt q => PosInt (p + q)
  | NegInt p, NegInt q => NegInt (p + q)
  | PosInt p, NegInt q => if (p <=? q) then NegInt (q - p) else PosInt (p - q)
  | NegInt p, PosInt q => if (p <=? q) then PosInt (q - p) else NegInt (p - q)
  end.

Definition intsub (a b : Integer) : Integer :=
  intadd a (intneg b).

Definition intmult (a b : Integer) : Integer :=
  match a,b with
  | PosInt p, PosInt q => PosInt (p * q)
  | PosInt p, NegInt q => NegInt (p * q)
  | NegInt p, PosInt q => NegInt (p * q)
  | NegInt p, NegInt q => PosInt (p * q)
  end.

Definition intabs (a : Integer) : nat :=
  match a with
  | PosInt p => p
  | NegInt p => p
  end.

(* value of a piece in tenth of a pawn *)
Definition value_of_piece (p : Piece) : nat :=
  match p with
  | Queen => 90
  | Rook => 50
  | Bishop => 30
  | Knight => 30
  | Pawn => 10
  | King => 0
  end.

Definition value_of_square (sq : Square) (c : Color) : nat :=
  match sq with
  | Empty => 0
  | Occupied sc p => if (ceq sc c) then value_of_piece p else 0
  end.

Definition value_of_material (pp : PiecePlacements) (c : Color) : nat :=
  let f := (fun acc loc => 
    acc + (value_of_square (get_square_by_location pp loc) c)) in
  fold_left f valid_locations 0.

Definition material_balance_of_position (pp : PiecePlacements) : Integer :=
  intadd (PosInt (value_of_material pp White)) 
    (NegInt (value_of_material pp Black)).

Definition value_for_player (v : nat) (c : Color) :=
  match c with
  | White => PosInt v
  | Black => NegInt v
  end.

Inductive PositionEvaluation : Set :=
  | NormalEvaluation (v : Integer)
  | Checkmate (c :  Color)
  | Stalemate.

Definition position_evaluation_leq (ev1 ev2 : PositionEvaluation) : bool :=
  match ev1, ev2 with
  | NormalEvaluation v1, NormalEvaluation v2 => (intleq v1 v2)
  | NormalEvaluation v, Checkmate c => if (ceq c White) then true else false
  | NormalEvaluation v, Stalemate =>
    (intleq v (PosInt 0))
  | Checkmate c, _ => if (ceq c Black) then true else false
  | Stalemate, NormalEvaluation v => (intleq (PosInt 0) v)
  | Stalemate, Checkmate c => if (ceq c White) then true else false
  | Stalemate, Stalemate => true
  end.

(* Bigger numbers mean white has a greater advantage *)
Definition evaluate_position (pos : Position) : PositionEvaluation :=
  let number_of_legal_moves := length (legal_moves pos) in
  if (eqb 0 number_of_legal_moves) then
    if (is_in_check pos (get_to_move pos)) 
    then (Checkmate (get_to_move pos)) else Stalemate
  else 
    NormalEvaluation (material_balance_of_position (get_piece_placements pos)).

Fixpoint find_optimal_element {A B : Type} (l : list A) (eval : A -> B)
  (better : B -> B -> bool) (best_element_so_far : A) (best_value_so_far : B) 
  : A :=
  match l with
  | [] => best_element_so_far
  | a::rest => let new_value := (eval a) in
    if (better new_value best_value_so_far) 
    then (find_optimal_element rest eval better a new_value)
    else (find_optimal_element rest eval better best_element_so_far 
      best_value_so_far)
  end.

Inductive MoveEvaluation : Set :=
  | NormalMoveEva (m : Move) (v : Integer)
  | CheckmateMoveEva (m : Move) (in_moves : nat) (c : Color)
  | NoMoveEva (v : PositionEvaluation).

Definition move_evaluation_leq (ev1 ev2 : MoveEvaluation) : bool :=
    match ev1, ev2 with
    | NormalMoveEva _ v1, NormalMoveEva _ v2 => (intleq v1 v2)
    | NormalMoveEva _ v, CheckmateMoveEva _ in_moves c =>
      if (ceq c White) then true else false
    | NormalMoveEva _ v, NoMoveEva pv => 
      position_evaluation_leq (NormalEvaluation v) pv
    | CheckmateMoveEva _ _ c, NormalMoveEva _ v =>
      if (ceq c Black) then true else false
    | CheckmateMoveEva _ n1 c1, CheckmateMoveEva _ n2 c2 =>
      match c1,c2 with
      | White, White => n2 <=? n1
      | White, Black => false
      | Black, White => true
      | Black, Black => n1 <=? n2
      end
    | CheckmateMoveEva _ _ c, NoMoveEva v =>
      position_evaluation_leq (Checkmate c) v
    | NoMoveEva pv, NormalMoveEva _ v => 
      position_evaluation_leq pv (NormalEvaluation v)
    | NoMoveEva v, CheckmateMoveEva _ _ c =>
      position_evaluation_leq v (Checkmate c)
    | NoMoveEva v1, NoMoveEva v2 =>
      position_evaluation_leq v1 v2
    end.

Definition value_of_normal_evaluation (ev : MoveEvaluation) :=
  match ev with
  | NormalMoveEva _ v => v
  | _ => (PosInt 0)
  end.

Definition discounted_evaluation (m : Move) (ev : MoveEvaluation) :=
  match ev with
  | NormalMoveEva _ v => NormalMoveEva m v
  | CheckmateMoveEva _ in_moves c => CheckmateMoveEva m (in_moves + 1) c
  | NoMoveEva pv => match pv with
    | NormalEvaluation v => NormalMoveEva m v
    | Checkmate c => CheckmateMoveEva m 1 c
    | Stalemate => NormalMoveEva m (PosInt 0)
    end
  end.

Definition moves_worth_considering (pos : Position) :=
  legal_moves pos.

Definition minimal_evaluation (l : list MoveEvaluation) :=
  match l with
  | [] => NoMoveEva (NormalEvaluation (PosInt 0))
  | h::tl =>
    find_optimal_element l (fun ev => ev) move_evaluation_leq h h
  end.

Definition maximal_evaluation (l : list MoveEvaluation) :=
  let cmp := (fun v1 v2 => (negb (move_evaluation_leq v1 v2))) in
  match l with
  | [] => NoMoveEva (NormalEvaluation (PosInt 0))
  | h::tl =>
    find_optimal_element l (fun ev => ev) cmp h h
  end.

Definition evaluation_function_for_player (c : Color) :=
  match c with
  | White => maximal_evaluation
  | Black => minimal_evaluation
  end.

Fixpoint evaluate_moves (depth : nat) (pos : Position) 
  : (list MoveEvaluation) :=
  let moves_to_consider := (moves_worth_considering pos) in
  if (eqb 0 (length moves_to_consider)) 
  then [NoMoveEva (evaluate_position pos)]
  else
  match depth with
  | 0 => [NoMoveEva (evaluate_position pos)]
  | S d =>
    let player := (get_to_move pos) in
    let opponent := (opponent_of player) in
    let min_or_max := evaluation_function_for_player opponent in
    let evaluate_move := (fun move => (discounted_evaluation move
              (min_or_max (evaluate_moves d (make_move pos move))))) in
    (map evaluate_move moves_to_consider)
  end.

(*
Definition testpos1 := (make_move initial_position (DoubleStep (Loc 1 4) (Loc 3 4))).
Compute (evaluate_moves 2 testpos1).
Definition testpos2 := (make_move testpos1 (DoubleStep (Loc 6 5) (Loc 4 5))).
Compute (evaluate_moves 1 testpos2).
Compute (evaluate_moves 0 initial_position).
*)


Definition test2filea := Squares
Empty
Empty
Empty
(Occupied Black Pawn)
Empty
Empty
Empty
Empty.

Definition test2fileb := Squares
(Occupied White King)
Empty
Empty
Empty
Empty
Empty
Empty
Empty.

Definition test2filed := Squares
Empty
Empty
(Occupied Black Rook)
Empty
Empty
Empty
Empty
Empty.

Definition test2filee := Squares
Empty
(Occupied Black Rook)
Empty
Empty
Empty
Empty
Empty
Empty.

Definition test2filef := Squares
Empty
Empty
Empty
(Occupied Black Pawn)
Empty
Empty
Empty
Empty.

Definition test2fileg := Squares
Empty
Empty
Empty
Empty
Empty
Empty
Empty
(Occupied Black King).

Definition test2fileh := test2filef.

Definition emptyfile := Squares
Empty
Empty
Empty
Empty
Empty
Empty
Empty
Empty.

Definition test2pp := Files test2filea test2fileb emptyfile test2filed
test2filee test2filef test2fileg test2fileh.

Definition test2pos := Posn test2pp Black None [].

Compute (legal_moves test2pos).

Definition test2checkmatemove := FromTo (Loc 2 3) (Loc 0 3).

Definition test2pos2 := (make_move test2pos test2checkmatemove).

Compute (legal_moves test2pos2).

Compute (is_checkmate test2pos2).

Compute (evaluate_moves 3 test2pos).



