(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import setoid_leq misc languages dfa nfa.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Regular Expressions

This file contains the definition of regular expressions and the proof
that regular expressions have the same expressive power as finite
automata. *)

Section RegExp.
Variable char : eqType.

Inductive regexp :=
 | Void
 | Eps
 | Atom of char
 | Star of regexp
 | Plus of regexp & regexp
 | Conc of regexp & regexp.

Lemma eq_regexp_dec (e1 e2 : regexp) : {e1 = e2} + {e1 <> e2}.
Proof. decide equality; apply: eq_comparable. Qed.

HB.instance Definition _ := hasDecEq.Build regexp (compareP eq_regexp_dec).
End RegExp.

Arguments void : clear implicits.
Arguments eps : clear implicits.
Prenex Implicits Plus.
Arguments plusP {char r s w}.

Notation "'Void'" := (@Void _).
Notation "'Eps'" := (@Eps _).

(** We assign a decidable language to every regular expression *)

Fixpoint re_lang (char: eqType) (e : regexp char) : dlang char :=
  match e with
  | Void => void char
  | Eps => eps char
  | Atom x => atom x
  | Star e1 => star (re_lang e1)
  | Plus e1 e2 => plus (re_lang e1) (re_lang e2)
  | Conc e1 e2 => conc (re_lang e1) (re_lang e2)
  end.

Canonical Structure regexp_predType (char: eqType) := PredType (@re_lang char).

(** We instantiate Ssreflects Canonical Big Operators *)
Notation "\sigma_( i <- r )  F" := (\big[Plus/Void]_(i <- r) F) (at level 50).
Notation "\sigma_( i | P )  F" := (\big[Plus/Void]_(i | P) F) (at level 50).

Lemma big_plus_seqP (T char : eqType) (r : seq T) w (F : T -> regexp char) :
  reflect (exists2 x, x \in r & w \in F x) (w \in \sigma_(i <- r) F i).
Proof.
  elim: r w => [|r rs IHrs] w. rewrite big_nil; by constructor => [[x]].
  rewrite big_cons; apply: (iffP plusP) => [[H|H]|[x]].
  - exists r => //; by rewrite mem_head.
  - case/IHrs : H => x Hx ?. exists x => //. by rewrite in_cons Hx orbT.
  - rewrite in_cons; case/orP => [/eqP -> |]; auto => ? ?.
    right. apply/IHrs. by exists x.
Qed.

Lemma big_plusP (T char: finType) (P:pred T) w (F : T -> regexp char) :
  reflect (exists2 i, P i  & w \in F i) (w \in \sigma_(i | P i) F i).
Proof.
  rewrite -big_filter. apply: (iffP (big_plus_seqP _ _ _)) => [[x]|[x] H1 H2].
  - rewrite mem_filter => /andP [? ?]; by exists x.
  - by exists x; rewrite // mem_filter H1 mem_index_enum.
Qed.

Fixpoint re_size (char: eqType) (e : regexp char) :=
  match e with
  | Star s => (re_size s).+1
  | Plus s t => ((re_size s)+(re_size t)).+1
  | Conc s t => ((re_size s)+(re_size t)).+1
  | _ => 1
  end.

Lemma big_plus_size (T char : eqType) (r : seq T) (F : T -> regexp char) m :
  (forall i, i \in r -> re_size (F i) <= m) -> re_size (\sigma_(i <- r) F i) <= (size r * m.+1).+1.
Proof.
  elim: r => [|e r IH /forall_cons [A B]]; first by rewrite big_nil.
  rewrite big_cons /= ltnS mulSn addSn -addnS leq_add //. exact: IH.
Qed.

(** ** Regular Expressions to Finite Automata *)
Section DFAofRE.
Variable (char : finType).

Fixpoint re_to_nfa (r : regexp char): nfa char :=
  match r with
  | Void => dfa_to_nfa (dfa_void _)
  | Eps => nfa_eps _
  | Atom a => nfa_char a
  | Star s => nfa_star (re_to_nfa s)
  | Plus s t => nfa_plus (re_to_nfa s) (re_to_nfa t)
  | Conc s t => nfa_conc (re_to_nfa s) (re_to_nfa t)
  end.

Lemma re_to_nfa_correct (r : regexp char) : nfa_lang (re_to_nfa r) =i r.
Proof.
  elim: r => [||a|s IHs |s IHs t IHt |s IHs t IHt] w //=.
  - by rewrite -dfa_to_nfa_correct inE /dfa_accept inE.
  - exact: nfa_eps_correct.
  - exact: nfa_char_correct.
  - rewrite nfa_star_correct. exact: star_eq.
  - by rewrite nfa_plus_correct /plus inE IHs IHt.
  - rewrite nfa_conc_correct. exact: conc_eq.
Qed.

Lemma re_to_nfa_size e : #|re_to_nfa e| <= 2 * re_size e.
Proof.
  elim: e; rewrite /= ?card_unit ?card_bool => //.
  - move => e IH. by rewrite card_option (leqRW IH) mulnS add2n.
  - move => e1 IH1 e2 IH2.
    by rewrite card_sum (leqRW IH1) (leqRW IH2) mulnS mulnDr add2n ltnW.
  - move => e1 IH1 e2 IH2.
    by rewrite card_sum (leqRW IH1) (leqRW IH2) mulnS mulnDr add2n ltnW.
Qed.

Definition re_to_dfa := @nfa_to_dfa _ \o re_to_nfa.

Lemma re_to_dfa_correct (r : regexp char) : dfa_lang (re_to_dfa r) =i r.
Proof. move => w. by rewrite -nfa_to_dfa_correct re_to_nfa_correct. Qed.

Lemma re_to_dfa_size e : #|re_to_dfa e| <= 2^(2 * re_size e).
Proof. by rewrite card_set leq_pexp2l // re_to_nfa_size. Qed.

(** Decidability of regular expression equivalence *)

Definition re_equiv r s := dfa_equiv (re_to_dfa r) (re_to_dfa s).

Lemma re_equiv_correct r s : reflect (r =i s) (re_equiv r s).
Proof.
  apply: (iffP (dfa_equiv_correct _ _)) => H w;
    move/(_ w) : H; by rewrite !re_to_dfa_correct.
Qed.

End DFAofRE.

(** ** Finite Automata to Regular Expressions (Kleene Construction) *)

Section KleeneAlgorithm.
  Variable char : finType.
  Variable A : dfa char.

  (** We first define the transition languages between states. The
  trasition languages are defined such that [w \in L^X q p] iff for
  all nonempty strict prefixes [v] of [w], [delta q v \in X]. *)

  Definition L (X : {set A}) (p q : A) x :=
    (delta p x == q) && [forall (i : 'I_(size x) | 0 < i), delta p (take i x) \in X].
  Notation "'L^' X" := (L X) (at level 8,format "'L^' X").

  Lemma dfa_L x y w : w \in L^setT x y = (delta x w == y).
  Proof.
    rewrite unfold_in. case: (_ == _) => //=.
    apply/forall_inP => ? ?. by rewrite inE.
  Qed.

  Lemma LP {X : {set A}} {p q : A} {x} :
    reflect (delta p x = q /\ forall i, (0 < i) -> (i < size x) -> delta p (take i x) \in X)
            (x \in L^X p q).
  Proof.
    apply: (iffP andP); case => /eqP ? H; split => //.
    - move => i I1 I2. exact: (forall_inP H (Ordinal I2)).
    - apply/forall_inP => [[i I1 /= I2]]; auto.
  Qed.

  Lemma L_monotone (X : {set A}) (x y z : A): {subset L^X x y <= L^(z |: X) x y}.
  Proof.
    move => w. rewrite !unfold_in. case: (_ == _) => //. apply: sub_forall => i /=.
    case: (_ < _) => //= H. by rewrite inE H orbT.
  Qed.

  Lemma L_nil X x y : reflect (x = y) ([::] \in L^X x y).
  Proof. apply: (iffP LP) => //=. by case. Qed.

  Lemma L_set0 p q w :
    L^set0 q p w -> p = q /\ w = [::] \/ exists2 a, w = [::a] & p = dfa_trans q a.
  Proof.
    case/LP => <-. case: w => [|a [|b w]] H ; [by left|by right;exists a|].
    move: (H 1). do 2 case/(_ _)/Wrap => //. by rewrite inE.
  Qed.

  Lemma L_split X p q z w : w \in L (z |: X) p q ->
    w \in L^X p q \/
    exists w1 w2, [/\ w = w1 ++ w2, size w2 < size w, w1 \in L^X p z & w2 \in L^(z |: X) z q].
  Proof.
    case/LP => H1 H2.
    case: (find_minn_bound (fun i => (0 < i) && (delta p (take i w) == z)) (size w)).
    - case => i [lt_w /andP [i_gt0 /eqP delta_z] min_i]; right.
      exists (take i w); exists (drop i w).
      have ? : 0 < size w by exact: ltn_trans lt_w.
      rewrite cat_take_drop size_drop -{2}[size w]subn0 ltn_sub2l //; split => //.
      + apply/LP. split => // j J1 J2.
        have lt_i_j : j < i. apply: leq_trans J2 _. by rewrite size_take lt_w.
        have/(H2 _ J1) : j < size w. exact: ltn_trans lt_w.
        case/setU1P => [H|]; last by rewrite take_takel 1?ltnW.
        move: (min_i _ lt_i_j). by rewrite negb_and J1 H eqxx.
      + apply/LP. rewrite -H1 -{2}[w](cat_take_drop i) delta_cat delta_z.
        split => // j J1 J2. rewrite -{1}delta_z -delta_cat -takeD.
        apply: H2; first by rewrite addn_gt0 J1 orbT.
        by rewrite -[w](cat_take_drop i) size_cat size_take lt_w ltn_add2l.
    - move => H; left. apply/LP. split => // i I1 I2. apply: contraTT (H2 _ I1 I2) => C.
      rewrite inE negb_or C inE andbT. apply: contraNN (H _ I2) => ->. by rewrite I1.
  Qed.

  Lemma L_cat (X : {set A}) x y z w1 w2 :
    z \in X -> w1 \in L^X x z -> w2 \in L^X z y -> w1++w2 \in L^X x y.
  Proof.
    move => Hz /LP [H11 H12] /LP [H21 H22]. apply/LP.
    split; first by rewrite delta_cat H11 H21.
    move => i i_gt0 H. rewrite take_cat. case: (boolP (i < _)); first exact: H12.
    rewrite delta_cat H11 -leqNgt => le_w1.
    case: (posnP (i - size w1)) => [->|Hi]; first by rewrite take0.
    apply: H22 => //. by rewrite -(ltn_add2l (size w1)) subnKC // -size_cat.
  Qed.

  Lemma L_catL X x y z w1 w2 :
    w1 \in L^X x z -> w2 \in L^(z |: X) z y -> w1++w2 \in L^(z |: X) x y.
  Proof. move/(L_monotone z). apply: L_cat. exact: setU11. Qed.

  Lemma L_catR X x y z w1 w2 :
    w1 \in L^(z |: X) x z -> w2 \in L^X z y -> w1++w2 \in L^(z |: X) x y.
  Proof. move => H /(L_monotone z). apply: L_cat H. exact: setU11. Qed.

  Lemma L_star (X : {set A}) z w : w \in star (L^X z z) -> w \in L^(z |: X) z z.
  Proof.
    move/starP => [vv Hvv ->]. elim: vv Hvv => [_|r vv IHvv]; first exact/L_nil.
    move => /= /andP [/andP [_ H1] H2]. exact: L_catL H1 (IHvv H2).
  Qed.

  (** Main Lemma - L satisfies a recursive equation that can be used
  to construct a regular expression *)

  Lemma L_rec (X : {set A}) x y z :
    L^(z |: X) x y =i plus (conc (L^X x z) (conc (star (L^X z z)) (L^X z y))) (L^X x y).
  Proof.
    move => w. apply/idP/idP.
    - move: w x y. apply: (size_induction (measure := size)) => w IHw x y.
      move/L_split => [|[w1 [w2 [Hw' H1 Hw1 Hw2]]]].
      + rewrite inE => ->. by rewrite orbT.
      + move: (IHw w2 H1 z y Hw2) Hw' => H4 -> {IHw H1}.
        rewrite inE (conc_cat Hw1 _) //.
        case/plusP : H4 => H; last by rewrite -[w2]cat0s conc_cat //.
        move/concP : H => [w21] [w22] [W1 [W2]] /concP [w221] [w222] [W3 [W4 W5]]; subst.
        by rewrite catA conc_cat // star_cat.
    - case/plusP ; last exact: L_monotone.
      move/concP => [w1] [w2] [-> [Hw1]] /concP [w3] [w4] [-> [Hw3 Hw4]].
      by rewrite (L_catL Hw1) // (L_catR _ Hw4) // L_star.
  Qed.

  (** Construction of the regular expression *)

  Definition edges (x y : A) := \big[Plus/Void]_(a | dfa_trans x a == y) Atom a.

  Definition edgesP x y w :
    reflect (exists2 a, w = [::a] & dfa_trans x a = y) (w \in edges x y).
  Proof. apply: (iffP (big_plusP _ _ _)) => [|] [a] /eqP ? /eqP ?; by exists a. Qed.

  Definition R0 x y := Plus (if x == y then Eps else Void) (edges x y).

  Lemma mem_R0 w x y :
    reflect (w = [::] /\ x=y \/ exists2 a, w = [::a] & dfa_trans x a = y)
            (w \in R0 x y).
  Proof.
    apply: (iffP plusP).
    - case => [| /edgesP]; auto. case e : (x == y) => // /eqP.
      by rewrite (eqP e); auto.
    - case => [[-> ->]|/edgesP];auto. by rewrite eqxx; auto.
  Qed.

  Fixpoint R (X : seq A) (x y : A) :=
    if X isn't z :: X' then R0 x y else
      Plus (Conc (R X' x z) (Conc (Star (R X' z z)) (R X' z y))) (R X' x y).

  Notation "'R^' X" := (R X) (at level 8, format "'R^' X").

  Lemma L_R (X : seq A) x y : L^[set z in X] x y =i R^X x y.
  Proof.
    elim: X x y => [|z X' IH] x y w.
    - rewrite (_ : [set z in [::]] = set0) //=.
      apply/idP/mem_R0.
      + move/L_set0 => [[-> ->]|[a -> ->]]; by eauto.
      + move => [[-> ->]|[a -> <-]]; apply/LP => /=; split => // [[|i]] //.
    - rewrite set_cons /= (L_rec _ _) -2!topredE /= /plus /= IH.
      f_equal.
      apply: conc_eq; first exact: IH.
      apply: conc_eq; last exact: IH.
      apply: star_eq. exact: IH.
  Qed.

  Definition dfa_to_re : regexp char := \sigma_(x | x \in dfa_fin A) R^(enum A) (dfa_s A) x.

  Lemma dfa_to_re_correct : dfa_lang A =i dfa_to_re.
  Proof.
    move => w. apply/idP/big_plusP => [H|[x Hx]].
    - exists (delta_s A w) => //. by rewrite -L_R set_enum dfa_L.
    - by rewrite -L_R set_enum dfa_L inE /dfa_accept => /eqP ->.
  Qed.

  (** ** Size Bound for Kleene Theorem *)

  Let c := (2 * #|char|).+3.

  Lemma R0_size x y : re_size (R0 x y) <= c.
  Proof.
    rewrite /= [X in X + _](_ : _ = 1); last by case (_ == _).
    rewrite add1n !ltnS. rewrite /edges -big_filter.
    apply: leq_trans (big_plus_size (m := 1) _) _ => [//|].
    rewrite size_filter ltnS mulnC leq_mul2l /=.
    apply: leq_trans (count_size _ _) _. by rewrite /index_enum -enumT cardE.
  Qed.

  Fixpoint R_size_rec (n : nat) := if n is n'.+1 then 4 * R_size_rec n' + 4 else c.

  Lemma R_size x : re_size (R^(enum A) (dfa_s A) x) <= R_size_rec #|A| .
  Proof.
    rewrite cardE. elim: (enum A) (dfa_s A) x => [|r s IH] p q.
    - exact: R0_size.
    - rewrite /= 6!(addSn,addnS) addn4 !ltnS !(leqRW (IH _ _)).
      by rewrite !mulSn mul0n addn0 !addnA.
  Qed.

  Lemma R_size_low (n : nat) : 3 <= R_size_rec n.
  Proof. elim: n => // n IH. by rewrite (leqRW IH) /= -(leqRW (leq_addr _ _)) leq_pmull. Qed.

  Lemma R_size_high n : R_size_rec n <= c * 4^(2 * n).
  Proof.
    elim: n => //= [|n IH].
    - by rewrite mulnS muln0 addn0.
    - rewrite [in X in _^X]mulnS expnD mulnA [c * _]mulnC -mulnA.
      rewrite -(leqRW IH) -[4^2]/((1+3) * 4) -mulnA mulnDl mul1n leq_add //.
      by rewrite -(leqRW (R_size_low _)).
  Qed.

  Lemma dfa_to_re_size : re_size dfa_to_re <= (#|A| * (c * 4 ^ (2 * #|A|)).+1).+1.
  Proof.
    rewrite /dfa_to_re -big_filter (leqRW (big_plus_size (m := R_size_rec #|A|)_)).
    - rewrite -(leqRW (R_size_high _)) size_filter (leqRW (count_size _ _)).
      by rewrite ltnS /index_enum -enumT cardE.
    - move => q _. exact: R_size.
  Qed.

End KleeneAlgorithm.

Lemma regularP (char : finType) (L : lang char) :
  regular L <-T->  { e : regexp char | forall x, L x <-> x \in e}.
Proof.
  split => [[A HA]|[e He]].
  - exists (dfa_to_re A) => x. by rewrite -dfa_to_re_correct.
  - exists (re_to_dfa e) => x. by rewrite re_to_dfa_correct.
Qed.

(** Closure of Regular Expressions under intersection and complement *)

Definition Inter (char : finType) (r s : regexp char) :=
  dfa_to_re (dfa_op andb (re_to_dfa r) (re_to_dfa s)).

Lemma Inter_correct (char : finType) (r s : regexp char) w :
  w \in Inter r s = (w \in r) && (w \in s).
Proof. by rewrite /Inter -dfa_to_re_correct dfa_op_correct !re_to_dfa_correct. Qed.

Definition Neg (char : finType) (r : regexp char) :=
  dfa_to_re (dfa_compl (re_to_dfa r)).

Lemma Neg_correct (char : finType) (r : regexp char) w :
  w \in Neg r = (w \notin r).
Proof. by rewrite /Neg -dfa_to_re_correct dfa_compl_correct !re_to_dfa_correct. Qed.

(** ** Regular expression for images of homomorphimsms *)

Prenex Implicits Conc.
Definition String (char : finType) (w : word char) :=
  foldr Conc Eps [seq Atom a | a <- w].

Lemma StringE (char : finType) (w : word char) : String w =i pred1 w.
Proof.
  elim: w => [|a v IHv] w //=. rewrite inE /String /=. apply/concP/eqP.
  - move => [w1] [w2] [e []]. set r := foldr _ _ _.
    rewrite -/(re_lang r) inE e => /eqP -> H /=.
    rewrite IHv inE in H. by rewrite (eqP H).
  - move => e. exists [:: a]; exists v; split => //; split.
    by rewrite inE. by rewrite IHv inE eqxx.
Qed.

Section Image.
  Variables (char char' : finType) (h : seq char -> seq char').
  Hypothesis h_hom : homomorphism h.

  Fixpoint re_image (e : regexp char) : regexp char' :=
    match e with
    | Void => Void
    | Eps => Eps
    | Atom a => String (h [:: a])
    | Star e => Star (re_image e)
    | Plus e1 e2 => Plus (re_image e1) (re_image e2)
    | Conc e1 e2 => Conc (re_image e1) (re_image e2)
    end.

  Lemma re_imageP e v : reflect (image h (re_lang e) v) (v \in re_image e).
  Proof using h_hom.
    elim: e v => [||a|e IHe|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2] v /=.
    - rewrite inE; constructor. move => [u]. by case.
    - rewrite inE; apply: (iffP eqP) => [-> |[w] [] /eqP -> <-]; last exact: h0.
      exists [::]; by rewrite ?h0.
    - rewrite StringE. apply: (iffP eqP) => [->|[w /=]].
      + exists [::a] => //. by rewrite /atom inE.
      + by rewrite /atom inE => [[]] /eqP -> <-.
    - apply: (iffP idP) => [/starP [vv] /allP Hvv dev_v|].
        have {IHe} Hvv v' : v' \in vv -> image h (re_lang e) v'.
          by move => /Hvv /= /andP [_ /IHe].
        subst v. elim: vv Hvv => [|v vv IHvv] Hvv /=; first by exists [::]; rewrite ?h0.
        case: (Hvv v (mem_head _ _)) => w [Hw1 Hw2].
        case/forall_cons: Hvv => Hv /IHvv [ww [Hww1 Hww2]].
        exists (w++ww); split; by [exact: star_cat | rewrite h_hom Hw2 Hww2].
      + case => w [] /starP [ww] /allP Hww1 -> <-. rewrite h_flatten //.
        apply: starI => v' /mapP [w' /Hww1 /= /andP [_ Hw' ->]].
        apply/IHe. by exists w'.
    - apply: (iffP orP).
       + case => [/IHe1 | /IHe2] [w] [] H <-.
           exists w => //. by rewrite /plus inE (_ : w \in re_lang e1).
         exists w => //. by rewrite /plus inE (_ : w \in re_lang e2) ?orbT.
       + case => w []. case/orP => H <-; [left; apply/IHe1 |right; apply/IHe2]; by exists w.
    - apply: (iffP idP).
      + case/concP => v1 [v2] [e] [/IHe1 [w [Hw1 Hw2]] /IHe2 [w' [Hw1' Hw2']]].
        exists (w++w'); split; first exact: conc_cat.
        by rewrite h_hom e Hw2 Hw2'.
      + case => w [] /concP [w1] [w2] [-> [H1 H2 <-]]. rewrite h_hom.
        apply: conc_cat; [apply/IHe1|apply/IHe2]. by exists w1. by exists w2.
  Qed.

End Image.

Lemma im_regular (char char' : finType) (h : word char -> word char') L :
  homomorphism h -> regular L -> regular (image h L).
Proof.
  move => hom_h /regularP [e He]. apply/regularP. exists (@re_image _ _ h e) => w.
  transitivity (image h (re_lang e) w); first exact: image_ext.
  exact: rwP (re_imageP _ _ _).
Qed.


(** ** Regular Expression for word reversal *)

Fixpoint Rev (char : finType) (e : regexp char) :=
  match e with
  | Star e => Star (Rev e)
  | Plus e1 e2 => Plus (Rev e1) (Rev e2)
  | Conc e1 e2 => Conc (Rev e2) (Rev e1)
  | _ => e
  end.

Lemma Rev_correct (char : finType) (e : regexp char) w :
  w \in Rev e = (rev w \in e).
Proof.
  elim: e w => [||a|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2] w //.
  - rewrite !inE. apply/eqP/idP; first by move->.
    elim/last_ind: w => //= s a _. by rewrite rev_rcons.
  - rewrite !inE. apply/eqP/eqP; first by move->.
    do 2 elim/last_ind: w => //= w ? _. by rewrite !rev_rcons.
  - rewrite /=; apply/idP/idP; case/starP => vv /allP /= H.
    + move->. rewrite rev_flatten. apply: starI => v'.
      rewrite mem_rev => /mapP [v V1 ->]. rewrite -IH. by case/andP: (H _ V1).
    + rewrite -{2}[w]revK => ->. rewrite rev_flatten. apply: starI => v'.
      rewrite mem_rev => /mapP [v V1 ->]. rewrite IH revK. by case/andP: (H _ V1).
  - by rewrite /= !inE -!/(re_lang _) IH1 IH2.
  - rewrite /=. apply/concP/concP => [] [w1] [w2]; rewrite -!/(re_lang _).
    + move => [-> [A B]]. exists (rev w2), (rev w1). by rewrite rev_cat -IH1 -IH2.
    + rewrite -{2}[w]revK. move => [-> [A B]]. exists (rev w2), (rev w1).
      by rewrite rev_cat IH1 IH2 !revK.
Qed.

Lemma regular_rev (char : finType) (L : lang char) :
  regular L -> regular (fun x => L (rev x)).
Proof. case/regularP => e H. apply/regularP. exists (Rev e) => x. by rewrite Rev_correct. Qed.
