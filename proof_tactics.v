Require Import Nat.
From Coq Require Export Lia.

Ltac dall := match goal with
| H : match ?x with _ => _ end = _ |- _ => destruct x eqn:?H
| |- match ?x with _ => _ end = _ => destruct x eqn:?H
| |- _ = match ?x with _ => _ end => destruct x eqn:?H
end.

Ltac Hb2p := match goal with
  | H : (_ <=? _) = true |- _ => rewrite PeanoNat.Nat.leb_le in H
  | H : (_ <=? _) = false |- _ => rewrite PeanoNat.Nat.leb_gt in H
  | H : (_ =? _) = false |- _ => rewrite PeanoNat.Nat.eqb_neq in H
  end.

Ltac Gb2p := match goal with
  | |- (_ <=? _) = true => rewrite PeanoNat.Nat.leb_le
  | |- (_ <? _) = true => rewrite PeanoNat.Nat.ltb_lt
  | |- (_ <=? _) = false => rewrite PeanoNat.Nat.leb_gt
  | |- (_ <? _) = false => rewrite PeanoNat.Nat.ltb_ge
  | |- true = (_ <=? _) => symmetry; rewrite PeanoNat.Nat.leb_le
  | |- true = (_ <? _) => symmetry; rewrite PeanoNat.Nat.ltb_lt
  | |- false = (_ <=? _) => symmetry; rewrite PeanoNat.Nat.leb_gt
  | |- false = (_ <? _) => symmetry; rewrite PeanoNat.Nat.ltb_ge
  | |- (_ =? _) = false => rewrite PeanoNat.Nat.eqb_neq
  end.

Ltac Hp2b := match goal with
  | H : (_ <= _) |- _ => rewrite <- PeanoNat.Nat.leb_le in H
  | H : (_ > _) |- _ => rewrite <- PeanoNat.Nat.leb_gt in H
  | H : (_ = _) |- _ => rewrite <- PeanoNat.Nat.eqb_eq in H
  end.

Ltac Hdestruct :=
repeat match goal with 
  | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?H 
end.
