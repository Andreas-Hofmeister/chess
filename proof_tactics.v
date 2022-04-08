Require Import Nat.
From Coq Require Export Lia.
Require Import List.

Ltac dall := match goal with
| H : match ?x with _ => _ end = _ |- _ => destruct x eqn:?H
| |- match ?x with _ => _ end = _ => destruct x eqn:?H
| |- _ = match ?x with _ => _ end => destruct x eqn:?H
end.

Ltac Hb2p := match goal with
  | H : (_ <=? _) = true |- _ => rewrite PeanoNat.Nat.leb_le in H
  | H : (_ <=? _) = false |- _ => rewrite PeanoNat.Nat.leb_gt in H
  | H : (_ =? _) = false |- _ => rewrite PeanoNat.Nat.eqb_neq in H
  | H : (_ =? _) = true |- _ => rewrite PeanoNat.Nat.eqb_eq in H
  | H : (_ && _)%bool = true |- _ => rewrite Bool.andb_true_iff in H
  | H : (_ && _)%bool = false |- _ => rewrite Bool.andb_false_iff in H
  end.

Ltac Gb2p := match goal with
  | |- (_ <=? _) = true => rewrite PeanoNat.Nat.leb_le
  | |- (_ <? _) = true => rewrite PeanoNat.Nat.ltb_lt
  | |- (_ <=? _) = false => rewrite PeanoNat.Nat.leb_gt
  | |- (_ <? _) = false => rewrite PeanoNat.Nat.ltb_ge
  | |- true = (_ <=? _) => symmetry; rewrite PeanoNat.Nat.leb_le
  | |- true = (_ <? _) => symmetry; rewrite PeanoNat.Nat.ltb_lt
  | |- true = (_ =? _) => symmetry; rewrite PeanoNat.Nat.eqb_eq
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

Ltac HreplaceInIf := match goal with
  | H : (if (?x <? ?y - ?z) then _ else _) <= _ |- _ =>
    replace (x <? y - z) with false in H; try Gb2p; try lia
  | H : (if (?x <? ?y + S ?z) then _ else _) <= _ |- _ =>
    replace (x <? y + S z) with true in H; try Gb2p; try lia
  end.

Ltac in_app_to_or := match goal with
  | H : In _ (_ ++ _) |- _ => apply in_app_or in H
  | H : In _ _ \/ In _ _ |- _ => destruct H as [H | H]
  end.

