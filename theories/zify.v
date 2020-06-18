From Coq Require Import ZArith ZifyClasses Zify ZifyInst ZifyBool.
From Coq Require Export Lia.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import order binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac zify ::=
  unfold is_true in *; do ?rewrite -> unfold_in in *;
  zify_op; (iter_specs applySpec); zify_post_hook.

Module MathcompZifyInstances.

Import Order.Theory.

Local Delimit Scope Z_scope with Z.

Instance Op_isZero : UnOp isZero :=
  { TUOp := isZero; TUOpInj := fun => erefl }.
Add UnOp Op_isZero.

Instance Op_isLeZero : UnOp isLeZero :=
  { TUOp := isLeZero; TUOpInj := fun => erefl }.
Add UnOp Op_isLeZero.

(******************************************************************************)
(* bool                                                                       *)
(******************************************************************************)

Instance Op_addb : BinOp addb :=
  { TBOp := fun x y => (Z.max (x - y) (y - x))%Z;
    TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_addb.

Instance Op_eqb : BinOp eqb :=
  { TBOp := fun x y => isZero (x - y)%Z; TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_eqb.

Instance Op_eq_op_bool : BinOp (@eq_op bool_eqType) := Op_eqb.
Add BinOp Op_eq_op_bool.

Instance Op_Z_of_bool : UnOp Z_of_bool :=
  { TUOp := id; TUOpInj := fun => erefl }.
Add UnOp Op_Z_of_bool.

Instance Op_bool_le : BinOp (<=%O : bool -> bool -> bool) :=
  { TBOp := fun x y => Z.max (1 - x)%Z y; TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_bool_le.

Instance Op_bool_le' : BinOp (>=^d%O : rel bool^d) := Op_bool_le.
Add BinOp Op_bool_le'.

Instance Op_bool_ge : BinOp (>=%O : bool -> bool -> bool) :=
  { TBOp := fun x y => Z.max x (1 - y)%Z; TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_bool_ge.

Instance Op_bool_ge' : BinOp (<=^d%O : rel bool^d) := Op_bool_ge.
Add BinOp Op_bool_ge'.

Instance Op_bool_lt : BinOp (<%O : bool -> bool -> bool) :=
  { TBOp := fun x y => Z.min (1 - x)%Z y; TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_bool_lt.

Instance Op_bool_lt' : BinOp (>^d%O : rel bool^d) := Op_bool_lt.
Add BinOp Op_bool_lt'.

Instance Op_bool_gt : BinOp (>%O : bool -> bool -> bool) :=
  { TBOp := fun x y => Z.min x (1 - y)%Z; TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_bool_gt.

Instance Op_bool_gt' : BinOp (<^d%O : rel bool^d) := Op_bool_gt.
Add BinOp Op_bool_gt'.

Instance Op_bool_min : BinOp (Order.meet : bool -> bool -> bool) := Op_andb.
Add BinOp Op_bool_min.

Instance Op_bool_min' : BinOp (Order.join : bool^d -> _) := Op_andb.
Add BinOp Op_bool_min'.

Instance Op_bool_max : BinOp (Order.join : bool -> bool -> bool) := Op_orb.
Add BinOp Op_bool_max.

Instance Op_bool_max' : BinOp (Order.meet : bool^d -> _) := Op_orb.
Add BinOp Op_bool_max'.

Instance Op_bool_bottom : CstOp (0%O : bool) := Op_false.
Add CstOp Op_bool_bottom.

Instance Op_bool_bottom' : CstOp (1%O : bool^d) := Op_false.
Add CstOp Op_bool_bottom'.

Instance Op_bool_top : CstOp (1%O : bool) := Op_true.
Add CstOp Op_bool_top.

Instance Op_bool_top' : CstOp (0%O : bool^d) := Op_true.
Add CstOp Op_bool_top'.

Instance Op_bool_sub : BinOp (Order.sub : bool -> bool -> bool) :=
  { TBOp := fun x y => Z.min x (1 - y)%Z; TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_bool_sub.

Instance Op_bool_compl : UnOp (Order.compl : bool -> bool) := Op_negb.
Add UnOp Op_bool_compl.

(******************************************************************************)
(* nat                                                                        *)
(******************************************************************************)

Instance Op_eqn : BinOp eqn := Op_nat_eqb.
Add BinOp Op_eqn.

Instance Op_eq_op_nat : BinOp (@eq_op nat_eqType) := Op_eqn.
Add BinOp Op_eq_op_nat.

Instance Op_addn_rec : BinOp addn_rec := Op_plus.
Add BinOp Op_addn_rec.

Instance Op_addn : BinOp addn := Op_plus.
Add BinOp Op_addn.

Instance Op_subn_rec : BinOp subn_rec := Op_sub.
Add BinOp Op_subn_rec.

Instance Op_subn : BinOp subn := Op_sub.
Add BinOp Op_subn.

Instance Op_muln_rec : BinOp muln_rec := Op_mul.
Add BinOp Op_muln_rec.

Instance Op_muln : BinOp muln := Op_mul.
Add BinOp Op_muln.

Lemma nat_lebE n m : (n <= m) = Nat.leb n m.
Proof. by elim: n m => [|n ih []]. Qed.

Instance Op_leq : BinOp leq :=
  { TBOp := fun x y => isLeZero (x - y)%Z;
    TBOpInj := ltac:(move=> ? ?; rewrite nat_lebE /=; lia) }.
Add BinOp Op_leq.

Instance Op_geq : BinOp (geq : nat -> nat -> bool) :=
  { TBOp := fun x y => isLeZero (y - x)%Z;
    TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_geq.

Instance Op_ltn : BinOp (ltn : nat -> nat -> bool) :=
  { TBOp := fun x y => isLeZero (x + 1 - y)%Z; TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_ltn.

Instance Op_gtn : BinOp (gtn : nat -> nat -> bool) :=
  { TBOp := fun x y => isLeZero (y + 1 - x); TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_gtn.

Instance Op_minn : BinOp minn :=
  { TBOp := Z.min; TBOpInj := ltac:(move=> ? ? /=; case: leqP; lia) }.
Add BinOp Op_minn.

Instance Op_maxn : BinOp maxn :=
  { TBOp := Z.max; TBOpInj := ltac:(move=> ? ? /=; case: leqP; lia) }.
Add BinOp Op_maxn.

Instance Op_nat_of_bool : UnOp nat_of_bool :=
  { TUOp := id; TUOpInj := ltac:(by case) }.
Add UnOp Op_nat_of_bool.

Instance Op_double : UnOp double :=
  { TUOp := Z.mul 2; TUOpInj := ltac:(move=> ?; rewrite [inj]/= -muln2; lia) }.
Add UnOp Op_double.

Lemma Op_expn_subproof n m : Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite expnS; lia. Qed.

Instance Op_expn_rec : BinOp expn_rec :=
  { TBOp := Z.pow; TBOpInj := Op_expn_subproof }.
Add BinOp Op_expn_rec.

Instance Op_expn : BinOp expn := Op_expn_rec.
Add BinOp Op_expn.

(* missing: *)
(* Print fact_rec. *)
(* Print factorial. *)

Instance Op_nat_le : BinOp (<=%O : rel nat) := Op_leq.
Add BinOp Op_nat_le.

Instance Op_nat_le' : BinOp (>=^d%O : rel nat^d) := Op_leq.
Add BinOp Op_nat_le'.

Instance Op_nat_ge : BinOp (>=%O : rel nat) := Op_geq.
Add BinOp Op_nat_ge.

Instance Op_nat_ge' : BinOp (<=^d%O : rel nat^d) := Op_geq.
Add BinOp Op_nat_ge'.

Instance Op_nat_lt : BinOp (<%O : rel nat) := Op_ltn.
Add BinOp Op_nat_lt.

Instance Op_nat_lt' : BinOp (>^d%O : rel nat^d) := Op_ltn.
Add BinOp Op_nat_lt'.

Instance Op_nat_gt : BinOp (>%O : rel nat) := Op_gtn.
Add BinOp Op_nat_gt.

Instance Op_nat_gt' : BinOp (<^d%O : rel nat^d) := Op_gtn.
Add BinOp Op_nat_gt'.

Instance Op_nat_min : BinOp (Order.meet : nat -> _) := Op_minn.
Add BinOp Op_nat_min.

Instance Op_nat_min' : BinOp (Order.join : nat^d -> _) := Op_minn.
Add BinOp Op_nat_min'.

Instance Op_nat_max : BinOp (Order.join : nat -> _) := Op_maxn.
Add BinOp Op_nat_max.

Instance Op_nat_max' : BinOp (Order.meet : nat^d -> _) := Op_maxn.
Add BinOp Op_nat_max'.

Instance Op_nat_bottom : CstOp (0%O : nat) := Op_O.
Add CstOp Op_nat_bottom.

End MathcompZifyInstances.

Module Export Exports.
Import MathcompZifyInstances.
Add UnOp Op_isZero.
Add UnOp Op_isLeZero.
Add BinOp Op_addb.
Add BinOp Op_eqb.
Add BinOp Op_eq_op_bool.
Add UnOp Op_Z_of_bool.
Add BinOp Op_eqn.
Add BinOp Op_eq_op_nat.
Add BinOp Op_addn_rec.
Add BinOp Op_addn.
Add BinOp Op_subn_rec.
Add BinOp Op_subn.
Add BinOp Op_muln_rec.
Add BinOp Op_muln.
Add BinOp Op_leq.
Add BinOp Op_geq.
Add BinOp Op_ltn.
Add BinOp Op_gtn.
Add BinOp Op_minn.
Add BinOp Op_maxn.
Add UnOp Op_nat_of_bool.
Add UnOp Op_double.
Add BinOp Op_expn_rec.
Add BinOp Op_expn.
Add BinOp Op_nat_le.
Add BinOp Op_nat_le'.
Add BinOp Op_nat_ge.
Add BinOp Op_nat_ge'.
Add BinOp Op_nat_lt.
Add BinOp Op_nat_lt'.
Add BinOp Op_nat_gt.
Add BinOp Op_nat_gt'.
Add BinOp Op_nat_min.
Add BinOp Op_nat_min'.
Add BinOp Op_nat_max.
Add BinOp Op_nat_max'.
Add CstOp Op_nat_bottom.
End Exports.
