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
  | King => 1040
  end.
