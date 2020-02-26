From Coq Require Import ZArith ZifyClasses Zify ZifyBool.
From Coq Require Export Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import binomial ssralg countalg ssrnum ssrint rat intdiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac zify ::=
  unfold is_true in *; do ?rewrite -> unfold_in in *;
  zify_op; (iter_specs applySpec); zify_post_hook.

Module MathcompZifyInstances.

Import GRing.Theory Num.Theory.

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

(******************************************************************************)
(* ssrint                                                                     *)
(******************************************************************************)

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun => True) (fun => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

Instance Op_Z_of_int : UnOp Z_of_int :=
  { TUOp := id : Z -> Z; TUOpInj := ltac:(by []) }.
Add UnOp Op_Z_of_int.

Instance Op_Posz : UnOp Posz := mkuop _ _ _ Posz _ _ id (fun => erefl).
Add UnOp Op_Posz.

Lemma Op_Negz_subproof n : Z_of_int (Negz n) = (- (Z.of_nat n + 1))%Z.
Proof. simpl; lia. Qed.

Instance Op_Negz : UnOp Negz :=
  {| TUOp := fun x => (- (x + 1))%Z; TUOpInj := Op_Negz_subproof |}.
Add UnOp Op_Negz.

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. split=> [->|] //; case: n m => ?[]? /= ?; f_equal; lia. Qed.

Instance Op_eq_int : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_eq_int_subproof }.
Add BinRel Op_eq_int.

Lemma Op_eq_op_int_subproof (n m : int) :
  Z_of_bool (n == m) = isZero (Z_of_int n - Z_of_int m).
Proof. case: n m => ?[]? //; rewrite /eq_op [LHS]/= /eq_op [LHS]/=; lia. Qed.

Instance Op_eq_op_int : BinOp (@eq_op int_eqType) :=
  (* { TBOp := fun x y => isZero (x - y); TBOpInj := Op_eq_op_int_subproof }. *)
  mkbop int int bool Z (@eq_op _) Inj_int_Z Inj_int_Z Inj_bool_Z
        (fun x y : Z => isZero (Z.sub x y)) Op_eq_op_int_subproof.
Add BinOp Op_eq_op_int.

Instance Op_0_int : CstOp 0%R :=
  {| TCst := 0%Z; TCstInj := erefl (Z_of_int 0%R) |}.
Add CstOp Op_0_int.

Lemma Op_addz_subproof n m :
  Z_of_int (intZmod.addz n m) = (Z_of_int n + Z_of_int m)%Z.
Proof. case: n m => ?[]?; rewrite /intZmod.addz; try case: leqP; lia. Qed.

Instance Op_addz : BinOp intZmod.addz :=
  {| TBOp := Z.add; TBOpInj := Op_addz_subproof |}.
Add BinOp Op_addz.

Instance Op_add_int : BinOp +%R := Op_addz.
Add BinOp Op_add_int.

Lemma Op_oppz_subproof n : Z_of_int (intZmod.oppz n) = (- Z_of_int n)%Z.
Proof. case: n=> [[|?]|?]; rewrite /intZmod.oppz; lia. Qed.

Instance Op_oppz : UnOp intZmod.oppz :=
  {| TUOp := Z.opp; TUOpInj := Op_oppz_subproof |}.
Add UnOp Op_oppz.

Instance Op_opp_int : UnOp (@GRing.opp _) := Op_oppz.
Add UnOp Op_opp_int.

Instance Op_1_int : CstOp 1%R :=
  {| TCst := 1%Z; TCstInj := (erefl _ : Z_of_int 1%R = 1%Z) |}.
Add CstOp Op_1_int.

Lemma Op_mulz_subproof n m :
  Z_of_int (intRing.mulz n m) = (Z_of_int n * Z_of_int m)%Z.
Proof. case: n m => ?[]?; rewrite /intRing.mulz; lia. Qed.

Instance Op_mulz : BinOp intRing.mulz :=
  {| TBOp := Z.mul; TBOpInj := Op_mulz_subproof |}.
Add BinOp Op_mulz.

Instance Op_mulr_int : BinOp *%R := Op_mulz.
Add BinOp Op_mulr_int.

Lemma Op_int_intmul_subproof n m :
  Z_of_int (n *~ m) = (Z_of_int n * Z_of_int m)%Z.
Proof. rewrite mulrzz; lia. Qed.

Instance Op_int_intmul : BinOp *~%R%R :=
  (* {| TBOp := Z.mul; TBOpInj := Op_int_intmul_subproof |}. *)
  mkbop int int int Z (@intmul _) Inj_int_Z Inj_int_Z
        Inj_int_Z Z.mul Op_int_intmul_subproof.
Add BinOp Op_int_intmul.

Lemma Op_int_natmul_subproof n m :
  Z_of_int (n *+ m) = (Z_of_int n * Z_of_nat m)%Z.
Proof. rewrite pmulrn mulrzz; lia. Qed.

Instance Op_int_natmul : BinOp (@GRing.natmul _) :=
  (* {| TBOp := Z.mul; TBOpInj := Op_int_natmul_subproof |}. *)
  mkbop int nat int Z (@GRing.natmul _) Inj_int_Z Inj_nat_Z
        Inj_int_Z Z.mul Op_int_natmul_subproof.
Add BinOp Op_int_natmul.

Lemma Op_int_scale_subproof (n : int) (m : int^o) :
  Z_of_int (n *: m) = (Z_of_int n * Z_of_int m)%Z.
Proof. rewrite /GRing.scale /=; lia. Qed.

Instance Op_int_scale : BinOp (@GRing.scale _ [lmodType int of int^o]) :=
  (* {| TBOp := Z.mul; TBOpInj := Op_int_scale_subproof |}. *)
  mkbop int int int Z (@GRing.scale _ (GRing.regular_lmodType int_Ring))
        Inj_int_Z Inj_int_Z Inj_int_Z Z.mul Op_int_scale_subproof.
Add BinOp Op_int_scale.

Lemma Op_int_exp_subproof n m :
  Z_of_int (n ^+ m) = (Z_of_int n ^ Z.of_nat m)%Z.
Proof. rewrite -Zpower_nat_Z; elim: m => //= m <-; rewrite exprS; lia. Qed.

Instance Op_int_exp : BinOp (@GRing.exp _) :=
  {| TBOp := Z.pow; TBOpInj := Op_int_exp_subproof |}.
Add BinOp Op_int_exp.

Instance Op_invz : UnOp intUnitRing.invz :=
  {| TUOp := id; TUOpInj := fun => erefl |}.
Add UnOp Op_invz.

Instance Op_int_inv : UnOp GRing.inv := Op_invz.
Add UnOp Op_int_inv.

Lemma Op_absz_subproof n : Z.of_nat (absz n) = Z.abs (Z_of_int n).
Proof. case: n => ? /=; lia. Qed.

Instance Op_absz : UnOp absz :=
  { TUOp := Z.abs; TUOpInj := Op_absz_subproof }.
Add UnOp Op_absz.

Lemma Op_int_normr_subproof (n : int) : Z_of_int `|n|%R = Z.abs (Z_of_int n).
Proof. rewrite /Num.norm /=; lia. Qed.

Instance Op_int_normr : UnOp Num.norm :=
  { TUOp := Z.abs; TUOpInj := Op_int_normr_subproof }.
Add UnOp Op_int_normr.

Lemma Op_lez_subproof n m :
  Z_of_bool (intOrdered.lez n m) = isLeZero (Z_of_int n - Z_of_int m).
Proof. case: n m => ?[]?; rewrite [LHS]/=; lia. Qed.

Instance Op_lez : BinOp intOrdered.lez :=
  {| TBOp := fun x y => isLeZero (x - y)%Z; TBOpInj := Op_lez_subproof |}.
Add BinOp Op_lez.

Instance Op_int_ler : BinOp Num.le := Op_lez.
Add BinOp Op_int_ler.

Lemma Op_ltz_subproof n m :
  Z_of_bool (intOrdered.ltz n m) = isLeZero (Z_of_int n + 1 - Z_of_int m).
Proof. case: n m => ?[]?; rewrite [LHS]/=; lia. Qed.

Instance Op_ltz : BinOp intOrdered.ltz :=
  {| TBOp := fun x y => isLeZero (x + 1 - y)%Z; TBOpInj := Op_ltz_subproof |}.
Add BinOp Op_ltz.

Instance Op_int_ltr : BinOp Num.lt := Op_ltz.
Add BinOp Op_int_ltr.

(* missing: *)
(* Print Num.Def.lerif. *)

Lemma Op_int_sgr_subproof n : Z_of_int (Num.sg n) = Z.sgn (Z_of_int n).
Proof. by case: n => [[]|n] //=; rewrite addn1. Qed.

Instance Op_int_sgr : UnOp Num.sg :=
  {| TUOp := Z.sgn; TUOpInj := Op_int_sgr_subproof |}.
Add UnOp Op_int_sgr.

Lemma Op_int_min_subproof n m :
  Z_of_int (Num.min n m) = Z.min (Z_of_int n) (Z_of_int m).
Proof. case: minrP; lia. Qed.

Instance Op_int_min : BinOp Num.min :=
  {| TBOp := Z.min; TBOpInj := Op_int_min_subproof |}.
Add BinOp Op_int_min.

Lemma Op_int_max_subproof n m :
  Z_of_int (Num.max n m) = Z.max (Z_of_int n) (Z_of_int m).
Proof. case: maxrP; lia. Qed.

Instance Op_int_max : BinOp Num.max :=
  {| TBOp := Z.max; TBOpInj := Op_int_max_subproof |}.
Add BinOp Op_int_max.

(******************************************************************************)
(* int <-> Z                                                                  *)
(******************************************************************************)

Definition int_of_Z (n : Z) :=
  match n with
  | Z0 => Posz 0
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => Negz (Pos.to_nat p).-1
  end.

Lemma int_of_ZK : cancel int_of_Z Z_of_int.
Proof. case=> //= p; lia. Qed.

Instance Op_int_of_Z : UnOp int_of_Z :=
  { TUOp := id : Z -> Z; TUOpInj := int_of_ZK }.
Add UnOp Op_int_of_Z.

Lemma Z_of_intK : cancel Z_of_int int_of_Z.
Proof. move=> ?; lia. Qed.

(******************************************************************************)
(* intdiv                                                                     *)
(******************************************************************************)

Definition Z_ssrdiv (n m : Z) : Z := Z_of_int (divz (int_of_Z n) (int_of_Z m)).
Definition Z_ssrmod (n m : Z) : Z := Z_of_int (modz (int_of_Z n) (int_of_Z m)).

Lemma Op_Z_ssrdiv_subproof n m : inj (Z_ssrdiv n m) = Z_ssrdiv (inj n) (inj m).
Proof. by []. Qed.

Instance Op_Z_ssrdiv : BinOp Z_ssrdiv :=
  {| TBOp := Z_ssrdiv; TBOpInj := Op_Z_ssrdiv_subproof |}.
Add BinOp Op_Z_ssrdiv.

Lemma Op_divz_subproof n m :
  Z_of_int (divz n m) = Z_ssrdiv (Z_of_int n) (Z_of_int m).
Proof. by rewrite /Z_ssrdiv !Z_of_intK. Qed.

Instance Op_divz : BinOp divz :=
  {| TBOp := Z_ssrdiv; TBOpInj := Op_divz_subproof |}.
Add BinOp Op_divz.

Lemma Op_modz_subproof n m :
  Z_of_int (modz n m) = Z_ssrmod (Z_of_int n) (Z_of_int m).
Proof. by rewrite /Z_ssrmod !Z_of_intK. Qed.

Instance Op_modz : BinOp modz :=
  {| TBOp := Z_ssrmod; TBOpInj := Op_modz_subproof |}.
Add BinOp Op_modz.

Lemma Z_ssrdiv_spec_subproof n m :
  (0 < m -> Z_ssrdiv n m * m <= n < (Z_ssrdiv n m + 1) * m)%Z /\
  (m < 0 -> Z_ssrdiv n m * m <= n < (Z_ssrdiv n m - 1) * m)%Z /\
  (m = 0 -> Z_ssrdiv n m = 0)%Z.
Proof.
suff: let n := int_of_Z n in
      let m := int_of_Z m in
      [/\ 0 < m -> divz n m * m <= n < (divz n m + 1) * m,
          m < 0 -> divz n m * m <= n < (divz n m - 1) * m
        & m = 0 -> divz n m = 0]%R
  by case=> hpos hneg h0; split => [{hneg h0}|{hpos}]; lia.
move: (int_of_Z n) (int_of_Z m) => {}n {}m /=; split => hm.
- rewrite -(addr0 (_ * m)%R) mulrDl mul1r {2 3}(divz_eq n m).
  rewrite ler_add2l ltr_add2l ltz_pmod // modz_ge0; lia.
- rewrite -(addr0 (divz _ _ * _)%R) mulrDl mulN1r {2 3}(divz_eq n m).
  rewrite ler_add2l ltr_add2l -modzN ltz_pmod ?modz_ge0; lia.
- by rewrite hm divz0.
Qed.

Instance Z_ssrdiv_spec : BinOpSpec Z_ssrdiv :=
  {| BPred := fun n m r => (0 < m -> r * m <= n < (r + 1) * m)%Z /\
                           (m < 0 -> r * m <= n < (r - 1) * m)%Z /\
                           (m = 0 -> r = 0)%Z;
     BSpec := Z_ssrdiv_spec_subproof |}.
Add Spec Z_ssrdiv_spec.

Lemma Z_ssrmod_spec_subproof n m :
  (n = Z_ssrdiv n m * m + Z_ssrmod n m /\
   (0 < m -> 0 <= Z_ssrmod n m < m) /\ (m < 0 -> 0 <= Z_ssrmod n m < - m) /\
   (m = 0 -> Z_ssrmod n m = n))%Z.
Proof.
have: let n := int_of_Z n in
      let m := int_of_Z m in
      [/\ n = divz n m * m + modz n m,
          0 < m -> 0 <= modz n m < m, m < 0 -> 0 <= modz n m < - m
        & m = 0 -> modz n m = n]%R
  by rewrite /= -divz_eq /modz; split; lia.
case=> hn hpos hneg h0;
  split => [{hpos hneg h0}|{hn}]; last split => [{hneg h0}|{hpos}]; lia.
Qed.

Instance Z_ssrmod_spec : BinOpSpec Z_ssrmod :=
  {| BPred := (fun n m r =>
                 n = Z_ssrdiv n m * m + r /\
                 (0 < m -> 0 <= r < m) /\ (m < 0 -> 0 <= r < - m) /\
                 (m = 0 -> r = n))%Z;
     BSpec := Z_ssrmod_spec_subproof |}.
Add Spec Z_ssrmod_spec.
Add Spec Z_ssrdiv_spec. (* workaround *)

Lemma Op_dvdz_subproof n m :
  Z_of_bool (dvdz n m) = isZero (Z_ssrmod (Z_of_int m) (Z_of_int n)).
Proof. have ->: dvdz n m = (modz m n == 0%R); [exact/dvdz_mod0P/eqP | lia]. Qed.

Instance Op_dvdz : BinOp dvdz :=
  {| TBOp := fun x y => isZero (Z_ssrmod y x); TBOpInj := Op_dvdz_subproof |}.
Add BinOp Op_dvdz.

(******************************************************************************)
(* natdiv                                                                     *)
(******************************************************************************)

Lemma Op_divn_subproof n m :
  Z.of_nat (n %/ m) = Z_ssrdiv (Z.of_nat n) (Z.of_nat m).
Proof.
rewrite /Z_ssrdiv -!/(Z_of_int (Posz _)) !Z_of_intK /divz /=.
by case: m => //= m; rewrite mul1n.
Qed.

Instance Op_divn : BinOp divn :=
  {| TBOp := Z_ssrdiv; TBOpInj := Op_divn_subproof |}.
Add BinOp Op_divn.

Lemma Op_modn_subproof n m :
  Z.of_nat (n %% m) = Z_ssrmod (Z_of_int n) (Z_of_int m).
Proof. by rewrite /Z_ssrmod !Z_of_intK modz_nat. Qed.

Instance Op_modn : BinOp modn :=
  {| TBOp := Z_ssrmod; TBOpInj := Op_modn_subproof |}.
Add BinOp Op_modn.

Lemma Op_dvdn_subproof n m :
  Z_of_bool (n %| m) = isZero (Z_ssrmod (Z.of_nat m) (Z.of_nat n)).
Proof. rewrite /dvdn; lia. Qed.

Instance Op_dvdn : BinOp dvdn :=
  {| TBOp := fun x y => isZero (Z_ssrmod y x); TBOpInj := Op_dvdn_subproof |}.
Add BinOp Op_dvdn.

Lemma Op_odd_subproof n : Z_of_bool (odd n) = Z_ssrmod (Z_of_nat n) 2.
Proof. rewrite -Z_of_nat_of_boolE -modn2; lia. Qed.

Instance Op_odd : UnOp odd :=
  {| TUOp := fun x => Z_ssrmod x 2; TUOpInj := Op_odd_subproof |}.
Add UnOp Op_odd.

Lemma Op_half_subproof n : Z.of_nat n./2 = Z_ssrdiv (Z.of_nat n) 2.
Proof. rewrite -divn2; lia. Qed.

Instance Op_half : UnOp half :=
  {| TUOp := fun x => Z_ssrdiv x 2; TUOpInj := Op_half_subproof |}.
Add UnOp Op_half.

Lemma Op_uphalf_subproof n :
  Z.of_nat (uphalf n) = Z_ssrdiv (Z.of_nat n + 1)%Z 2.
Proof. rewrite uphalf_half; lia. Qed.

Instance Op_uphalf : UnOp uphalf :=
  {| TUOp := fun x => Z_ssrdiv (x + 1)%Z 2;
     TUOpInj := Op_uphalf_subproof |}.
Add UnOp Op_uphalf.

(******************************************************************************)
(* gcd, lcm, and coprime                                                      *)
(******************************************************************************)

Lemma Op_gcdn_subproof n m :
  Z.of_nat (gcdn n m) = Z.gcd (Z.of_nat n) (Z.of_nat m).
Proof.
apply/esym/Z.gcd_unique; first by case: gcdn.
- case/dvdnP: (dvdn_gcdl n m) => k {2}->; exists (Z.of_nat k); lia.
- case/dvdnP: (dvdn_gcdr n m) => k {2}->; exists (Z.of_nat k); lia.
- move=> k [n' Hkn] [m' Hkm].
  suff/dvdnP [k' ->]: Z.abs_nat k %| gcdn n m
    by apply/Znumtheory.Zdivide_Zabs_l; exists (Z.of_nat k'); lia.
  rewrite dvdn_gcd; apply/andP; split; apply/dvdnP;
    [exists (Z.abs_nat n') | exists (Z.abs_nat m')]; nia.
Qed.

Instance Op_gcdn : BinOp gcdn :=
  {| TBOp := Z.gcd; TBOpInj := Op_gcdn_subproof |}.
Add BinOp Op_gcdn.

Lemma Op_lcmn_subproof n m :
  Z.of_nat (lcmn n m) = Z.lcm (Z.of_nat n) (Z.of_nat m).
Proof.
case: n m => [|n][|m]; rewrite ?lcmn0 // /lcmn /Z.lcm -Op_gcdn_subproof.
case/dvdnP: (dvdn_gcdr n.+1 m.+1) => k {1 3}->.
rewrite mulnA mulnK ?gcdn_gt0 // !Nat2Z.inj_mul Z_div_mult_full //; first nia.
by case: (gcdn _ _) (gcdn_gt0 n.+1 m.+1).
Qed.

Instance Op_lcmn : BinOp lcmn :=
  {| TBOp := Z.lcm; TBOpInj := Op_lcmn_subproof |}.
Add BinOp Op_lcmn.

Lemma Op_coprime_subproof n m :
  Z_of_bool (coprime n m) = isZero (Z.gcd (Z.of_nat n) (Z.of_nat m) - 1)%Z.
Proof. rewrite /coprime; lia. Qed.

Instance Op_coprime : BinOp coprime :=
  {| TBOp := fun x y => isZero (Z.gcd x y - 1);
     TBOpInj := Op_coprime_subproof |}.
Add BinOp Op_coprime.

Lemma Op_gcdz_subproof n m :
  Z_of_int (gcdz n m) = Z.gcd (Z_of_int n) (Z_of_int m).
Proof.
by rewrite /gcdz /= Op_gcdn_subproof; case: n m => n[]m;
  rewrite ![absz _]/= -?(addn1 n) -?(addn1 m) /= ?Z.gcd_opp_l ?Z.gcd_opp_r.
Qed.

Instance Op_gcdz : BinOp gcdz :=
  {| TBOp := Z.gcd; TBOpInj := Op_gcdz_subproof |}.
Add BinOp Op_gcdz.

Lemma Op_coprimez_subproof n m :
  Z_of_bool (coprimez n m) = isZero (Z.gcd (Z_of_int n) (Z_of_int m) - 1)%Z.
Proof. rewrite /coprimez; lia. Qed.

Instance Op_coprimez : BinOp coprimez :=
  {| TBOp := fun x y => isZero (Z.gcd x y - 1);
     TBOpInj := Op_coprimez_subproof |}.
Add BinOp Op_coprimez.

(* missing: definitions in prime and binomial *)

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
Add InjTyp Inj_int_Z.
Add UnOp Op_Z_of_int.
Add UnOp Op_Posz.
Add UnOp Op_Negz.
Add BinRel Op_eq_int.
Add BinOp Op_eq_op_int.
Add CstOp Op_0_int.
Add BinOp Op_addz.
Add BinOp Op_add_int.
Add UnOp Op_oppz.
Add UnOp Op_opp_int.
Add CstOp Op_1_int.
Add BinOp Op_mulz.
Add BinOp Op_mulr_int.
Add BinOp Op_int_intmul.
Add BinOp Op_int_natmul.
Add BinOp Op_int_scale.
Add BinOp Op_int_exp.
Add UnOp Op_invz.
Add UnOp Op_int_inv.
Add UnOp Op_absz.
Add UnOp Op_int_normr.
Add BinOp Op_lez.
Add BinOp Op_int_ler.
Add BinOp Op_ltz.
Add BinOp Op_int_ltr.
Add UnOp Op_int_sgr.
Add BinOp Op_int_min.
Add BinOp Op_int_max.
Add UnOp Op_int_of_Z.
Add BinOp Op_Z_ssrdiv.
Add BinOp Op_divz.
Add BinOp Op_modz.
Add BinOp Op_modz.
Add Spec Z_ssrmod_spec.
Add Spec Z_ssrdiv_spec.
Add BinOp Op_dvdz.
Add BinOp Op_divn.
Add BinOp Op_modn.
Add BinOp Op_dvdn.
Add UnOp Op_odd.
Add UnOp Op_half.
Add UnOp Op_uphalf.
Add BinOp Op_gcdn.
Add BinOp Op_lcmn.
Add BinOp Op_coprime.
Add BinOp Op_gcdz.
Add BinOp Op_coprimez.
End Exports.
