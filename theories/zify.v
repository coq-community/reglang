From Coq Require Import ZArith ZifyClasses Zify ZifyBool.
From Coq Require Export Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac zify ::=
  unfold is_true in *; do ?rewrite -> unfold_in in *;
  zify_op; (iter_specs applySpec); zify_post_hook.

Module MathcompZifyInstances.

Local Delimit Scope Z_scope with Z.

Canonical Inj_nat_Z. (* Z_of_bool =? inj _ *)
Canonical Inj_bool_Z. (* Z.of_nat =? inj _ *)

(* missing instances in ZifyBool.v *)
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
  { TBOp := fun x y => isZero (x - y)%Z;
    TBOpInj := ltac:(by case=> [][]) }.
Add BinOp Op_eqb.

Instance Op_eq_op_bool : BinOp (@eq_op bool_eqType) := Op_eqb.
Add BinOp Op_eq_op_bool.

Instance Op_Z_of_bool : UnOp Z_of_bool :=
  { TUOp := id; TUOpInj := fun => erefl }.
Add UnOp Op_Z_of_bool.

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
Proof. by elim: n m => // n ih [|m] //=; rewrite -ih. Qed.

Instance Op_leq : BinOp leq :=
  { TBOp := fun x y => isLeZero (x - y)%Z;
    TBOpInj := ltac:(move=> *; rewrite nat_lebE /=; lia) }.
Add BinOp Op_leq.

Instance Op_geq : BinOp geq :=
  { TBOp := fun x y => isLeZero (y - x)%Z;
    TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_geq.

Instance Op_ltn : BinOp ltn :=
  { TBOp := fun x y => isLeZero (x + 1 - y)%Z; TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_ltn.

Instance Op_gtn : BinOp gtn :=
  { TBOp := fun x y => isLeZero (y + 1 - x); TBOpInj := ltac:(simpl; lia) }.
Add BinOp Op_gtn.

Lemma Op_minn_subproof n m :
  Z.of_nat (minn n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. rewrite /minn /=; case: leqP; lia. Qed.

Instance Op_minn : BinOp minn :=
  {| TBOp := Z.min; TBOpInj := Op_minn_subproof |}.
Add BinOp Op_minn.

Lemma Op_maxn_subproof n m :
  Z.of_nat (maxn n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. rewrite /maxn /=; case: leqP; lia. Qed.

Instance Op_maxn : BinOp maxn :=
  {| TBOp := Z.max; TBOpInj := Op_maxn_subproof |}.
Add BinOp Op_maxn.

Lemma Z_of_nat_of_boolE (b : bool) : Z.of_nat b = Z_of_bool b.
Proof. by case: b. Qed.

Instance Op_nat_of_bool : UnOp nat_of_bool :=
  {| TUOp := id; TUOpInj := Z_of_nat_of_boolE |}.
Add UnOp Op_nat_of_bool.

Lemma Op_double_subproof n : Z.of_nat n.*2 = (2 * (Z.of_nat n))%Z.
Proof. rewrite -muln2; lia. Qed.

Instance Op_double : UnOp double :=
  {| TUOp := Z.mul 2; TUOpInj := Op_double_subproof |}.
Add UnOp Op_double.

Lemma Op_expn_subproof n m : Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite expnS; lia. Qed.

Instance Op_expn_rec : BinOp expn_rec :=
  {| TBOp := Z.pow; TBOpInj := Op_expn_subproof |}.
Add BinOp Op_expn_rec.

Instance Op_expn : BinOp expn := Op_expn_rec.
Add BinOp Op_expn.

(* missing: *)
(* Print fact_rec. *)
(* Print factorial. *)

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
End Exports.
