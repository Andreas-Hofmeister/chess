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

(* Bigger numbers mean white has a greater advantage *)
Definition evaluate_position (pos : Position) : Integer :=
  if (is_checkmate pos) 
  then value_for_player 999 (opponent_of (get_to_move pos))
  else material_balance_of_position (get_piece_placements pos).

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
  | Eva (m : Move) (v : Integer)
  | NoMoveEva (v : Integer).

Definition value_of_evaluation (ev : MoveEvaluation) :=
  match ev with
  | Eva _ v => v
  | NoMoveEva v => v
  end.

Definition moves_worth_considering (pos : Position) :=
  legal_moves pos.

Definition minimal_evaluation (l : list MoveEvaluation) :=
  match l with
  | [] => NoMoveEva (PosInt 0)
  | h::tl =>
    find_optimal_element l (fun ev => (value_of_evaluation ev))
    (fun v1 v2 => (intleq v1 v2)) h (value_of_evaluation h)
  end.

Definition maximal_evaluation (l : list MoveEvaluation) :=
  match l with
  | [] => NoMoveEva (PosInt 0)
  | h::tl =>
    find_optimal_element l (fun ev => (value_of_evaluation ev))
    (fun v1 v2 => (intleq v2 v1)) h (value_of_evaluation h)
  end.

Definition evaluation_function_for_player (c : Color) :=
  match c with
  | White => maximal_evaluation
  | Black => minimal_evaluation
  end.

Fixpoint evaluate_moves (depth : nat) (pos : Position) 
  : (list MoveEvaluation) :=
  match depth with
  | 0 => [NoMoveEva (evaluate_position pos)]
  | S d =>
    let player := (get_to_move pos) in
    let opponent := (opponent_of player) in
    let min_or_max := evaluation_function_for_player opponent in
    let evaluate_move := (fun move =>
      Eva move (value_of_evaluation 
              (min_or_max (evaluate_moves d (make_move pos move))))) in
    (map evaluate_move (moves_worth_considering pos))
  end.
(*
Definition testpos1 := (make_move initial_position (DoubleStep (Loc 1 4) (Loc 3 4))).
Compute (evaluate_moves 2 testpos1).
Definition testpos2 := (make_move testpos1 (DoubleStep (Loc 6 5) (Loc 4 5))).
Compute (evaluate_moves 1 testpos2).
Compute (evaluate_moves 0 initial_position).
*)
