(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import misc.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Languages in Type Theory 

This file mainly defines aliases for (decidable) languages. It also
shows that decidable languages are closed under the primitive regular
operations (e.g., concatenation and interation). This will allow us to
assign decidable languages to regular expressions. We allow for
infinite (but discrete) alphabets. *)
 
(** The definitions of [conc] and [star] as well as the proofs of
[starP] and [concP] are taken from from regexp.v in:

Thierry Coquand, Vincent Siles, A Decision Procedure for Regular
Expression Equivalence in Type Theory (DOI:
10.1007/978-3-642-25379-9_11). See also:
https://github.com/coq-community/regexp-Brzozowski *)

Section Basics.
  Variables char : eqType.
  Definition word := seq char.
  Definition lang := word -> Prop.
  Definition dlang := pred word.

  Canonical Structure word_eqType := [eqType of word].
  Identity Coercion pred_of_dlang : dlang >-> pred.
End Basics. 

Section HomDef.
  Variables (char char' : finType) (h : seq char -> seq char').

  Definition image (L : word char -> Prop) v := exists w, L w /\ h w = v.

  Lemma image_ext L1 L2  w :
    (forall v, L1 v <-> L2 v) -> (image L1 w <-> image L2 w).
  Proof. by move => H; split; move => [v] [] /H; exists v. Qed.

  Definition preimage (L : word char' -> Prop) v :=  L (h v).

  Definition homomorphism := forall w1 w2, h (w1 ++ w2) = h w1 ++ h w2.
  Hypothesis h_hom : homomorphism.
  Local Set Default Proof Using "h_hom".  

  Lemma h0 : h [::] = [::].
  Proof.
    apply: size0nil. apply/eqP.
    by rewrite -(eqn_add2r (size (h [::]))) -size_cat -h_hom /=.
  Qed.

  Lemma h_seq w : h w = flatten [seq h [:: a] | a <- w].
  Proof. elim: w => [|a w IHw] /= ; by rewrite ?h0 // -cat1s h_hom IHw. Qed.

  Lemma h_flatten vv : h (flatten vv) = flatten (map h vv).
  Proof.
    elim: vv => //= [|v vv IHvv]; first exact: h0.
    by rewrite h_hom IHvv.
  Qed.

End HomDef.

(** ** Closure Properties for Decidable Languages *)

Section DecidableLanguages.

Variable char : eqType.
Implicit Types (x y z : char) (u v w : word char) (L : dlang char).

Definition void : dlang char := pred0.

Definition eps : dlang char := pred1 [::].

Definition dot : dlang char := [pred w | size w == 1].

Definition atom x : dlang char := pred1 [:: x].

Definition compl L : dlang char := predC L.

Definition prod L1 L2 : dlang char := [pred w in L1 | w \in L2].

Definition plus L1 L2 : dlang char := [pred w | (w \in L1) || (w \in L2)].

Definition residual x L : dlang char := [pred w | x :: w \in L].

(** For the concatenation of two decidable languages, we use finite
types. Note that we need to use [L1] and [L2] applicatively in order
for the termination check for [star] to succeed. *)

Definition conc (L1 L2: dlang char) : dlang char :=
  fun v => [exists i : 'I_(size v).+1, L1 (take i v) && L2 (drop i v)].

(** The iteration (Kleene star) operator is defined using resisdual
languages. Termination of star relies in the fact that conc applies
its second argument only to [drop i v] which is "structurally less
than or equal" to [v] *)

Definition star L : dlang char :=
  fix star v := if v is x :: v' then conc (residual x L) star v' else true.

Lemma in_dot u : (u \in dot) = (size u == 1).
Proof. by []. Qed.

Lemma in_compl L v : (v \in compl L) = (v \notin L).
Proof. by []. Qed.

Lemma compl_invol L : compl (compl L) =i L.
Proof. by move => w; rewrite inE /= /compl /= negbK. Qed.

Lemma in_prod L1 L2 v : (v \in prod L1 L2) = (v \in L1) && (v \in L2).
Proof. by rewrite inE. Qed.

Lemma plusP r s w :
  reflect (w \in r \/ w \in s) (w \in plus r s).
Proof. rewrite !inE. exact: orP. Qed.

Lemma in_residual x L u : (u \in residual x L) = (x :: u \in L).
Proof. by []. Qed.

Lemma concP {L1 L2 : dlang char} {w : word char} :
  reflect (exists w1 w2, w = w1 ++ w2 /\ w1 \in L1 /\ w2 \in L2) (w \in conc L1 L2).
Proof. apply: (iffP existsP) => [[n] /andP [H1 H2] | [w1] [w2] [e [H1 H2]]].
  - exists (take n w). exists (drop n w). by rewrite cat_take_drop -topredE.
  - have lt_w1: size w1 < (size w).+1 by rewrite e size_cat ltnS leq_addr.
    exists (Ordinal lt_w1); subst.
    rewrite take_size_cat // drop_size_cat //. exact/andP.
Qed.

Lemma conc_cat w1 w2 L1 L2 : w1 \in L1 -> w2 \in L2 -> w1 ++ w2 \in conc L1 L2.
Proof. move => H1 H2. apply/concP. exists w1. by exists w2. Qed.

Lemma conc_eq (l1: dlang char) l2 l3 l4:
  l1 =i l2 -> l3 =i l4 -> conc l1 l3 =i conc l2 l4.
Proof.
  move => H1 H2 w. apply: eq_existsb => n. 
  by rewrite (_ : l1 =1 l2) // (_ : l3 =1 l4).
Qed.

Lemma starP : forall {L v},
  reflect (exists2 vv, all [predD L & eps] vv & v = flatten vv) (v \in star L).
Proof.
move=> L v;
  elim: {v}_.+1 {-2}v (ltnSn (size v)) => // n IHn [|x v] /= le_v_n.
  by left; exists [::].
apply: (iffP concP) => [[u] [v'] [def_v [Lxu starLv']] | [[|[|y u] vv] //=]].
  case/IHn: starLv' => [|vv Lvv def_v'].
    by rewrite -ltnS (leq_trans _ le_v_n) // def_v size_cat !ltnS leq_addl.
  by exists ((x :: u) :: vv); [exact/andP | rewrite def_v def_v'].
case/andP=> Lyu Lvv [def_x def_v]; exists u. exists (flatten vv).
subst. split => //; split => //. apply/IHn; last by exists vv.
by rewrite -ltnS (leq_trans _ le_v_n) // size_cat !ltnS leq_addl.
Qed.

Lemma star_cat w1 w2 L : w1 \in L -> w2 \in (star L) -> w1 ++ w2 \in star L.
Proof.
  case: w1 => [|a w1] // H1 /starP [vv Ha Hf]. apply/starP.
  by exists ((a::w1) :: vv); rewrite ?Hf //= H1.
Qed.

Lemma starI (L : dlang char) vv :
  (forall v, v \in vv -> v \in L) -> flatten vv \in star L.
Proof.
  elim: vv => /= [//| v vv IHvv /all1s [H1 H2]].
  exact: star_cat _ (IHvv _).
Qed.

Lemma star_eq (l1 : dlang char) l2 : l1 =i l2 -> star l1 =i star l2.
Proof.
  move => H1 w. apply/starP/starP; move => [] vv H3 H4; exists vv => //;
  erewrite eq_all; try eexact H3; move => x /=; by rewrite ?H1 // -?H1.
Qed.

Lemma star_id (l : dlang char) : star (star l) =i star l.
Proof.
  move => u. rewrite -!topredE /=. apply/starP/starP => [[vs h1 h2]|].
    elim: vs u h1 h2 => [|hd tl Ih] u h1 h2; first by exists [::].
    move: h1 => /= h1. case/andP: h1; case/andP => hhd1 hhd2 htl.
    case: (Ih (flatten tl)) => //= [xs x1 x2].
    case/starP: hhd2 => hds j1 j2.
    exists (hds ++ xs); first by rewrite all_cat; apply/andP.
    by rewrite h2 j2 /= x2 flatten_cat.
  move => [hs h1 h2]. exists hs => //. apply/allP => x x1.
  move/allP: h1 => h1. case/andP: (h1 x x1) => /= h3 h4.
  rewrite h3 /=. apply/starP. exists [:: x] => /=; first by rewrite h3 h4.
  by rewrite cats0.
Qed.

End DecidableLanguages.
