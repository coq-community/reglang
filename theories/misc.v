(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Preliminaries

This file contains a number of auxiliary lemmas that do not mention
any of the representations of regular languages and may thus also be
useful in other contexts *)

(** ** Generic Lemmas not in MathComp *)

(** Logic *)

Notation "P =p Q" := (forall x, P x <-> Q x) (at level 30).

Lemma dec_iff P Q : decidable P -> Q <-> P -> decidable Q.
Proof. firstorder. Qed.

Lemma eqb_iff (b1 b2 : bool) : (b1 <-> b2) <-> (b1 = b2).
Proof. split => [[A B]|->//]. exact/idP/idP. Qed.

(* equivalence of type inhabitation *)
CoInductive iffT T1 T2 := IffT of (T1 -> T2) & (T2 -> T1).
Notation "T1 <-T-> T2" := (iffT T1 T2) (at level 30).

Definition iffT_LR T1 T2 : iffT T1 T2 -> T1 -> T2. by case. Qed.
Definition iffT_RL T1 T2 : iffT T1 T2 -> T2 -> T1. by case. Qed.

Hint View for move/ iffT_LR|2 iffT_RL|2.
Hint View for apply/ iffT_LR|2 iffT_RL|2.

(** Arithmetic *)

Lemma size_induction {X : Type} (measure : X -> nat) (p : X ->Prop) :
  ( forall x, ( forall y, measure y < measure x -> p y) -> p x) -> forall x, p x.
Proof.
  move => A x. apply: (A). elim: (measure x) => // n IHn y Hy.
  apply: A => z Hz. apply: IHn. exact: leq_trans Hz Hy.
Qed.

(** Sequences - seq.v *)

Lemma nth_cons T (x0:T) x (s : seq T) n : nth x0 (x::s) n.+1 = nth x0 s n.
Proof. done. Qed.

Lemma take_take T (s : seq T) n m  : n < m -> take n (take m s) = take n s.
Proof. elim: m n s => // n IHn [|m] [|a s] //= ?. by rewrite IHn. Qed.

Lemma take_addn (T : Type) (s : seq T) n m : take (n + m) s = take n s ++ take m (drop n s).
Proof.
  elim: n m s => [|n IH] [|m] [|a s] //; first by rewrite take0 addn0 cats0.
  by rewrite drop_cons addSn !take_cons /= IH.
Qed.

Lemma index_take (T : eqType) (a : T) n (s : seq T) : 
  a \in take n s -> index a (take n s) = index a s.
Proof. move => H. by rewrite -{2}[s](cat_take_drop n) index_cat H. Qed.

Lemma flatten_rcons T ss (s:seq T) : flatten (rcons ss s) = flatten ss ++ s.
Proof. by rewrite -cats1 flatten_cat /= cats0. Qed.

Lemma rev_flatten T (ss : seq (seq T)) :
  rev (flatten ss) = flatten (rev (map rev ss)).
Proof.
elim: ss => //= s ss IHss.
by rewrite rev_cons flatten_rcons -IHss rev_cat.
Qed.

Hint Resolve mem_head : core.

Lemma all1s {T : eqType} {a : T} {s} {P : T -> Prop} :
  (forall b, b \in a :: s -> P b) <-> P a /\ (forall b, b \in s -> P b).
Proof.
  split => [A|[A B] b /predU1P [->//|]]; last exact: B.
  split => [|b B]; apply: A => //. by rewrite !inE B orbT.
Qed.

Lemma ex1s {T : eqType} {a : T} {s} {P : T -> Prop} :
  (exists2 x : T, x \in a :: s & P x) <-> P a \/ (exists2 x : T, x \in s & P x).
Proof.
  split => [[x] /predU1P [->|]|]; firstorder. exists x => //. by rewrite inE H orbT. 
Qed.

Lemma orS (b1 b2 : bool) : b1 || b2 -> {b1} + {b2}.
Proof. by case: b1 => /= [_|H]; [left|right]. Qed.

Lemma all1sT {T : eqType} {a : T} {s} {P : T -> Type} :
  (forall b, b \in a :: s -> P b) <-T-> (P a * (forall b, b \in s -> P b)).
Proof.
  split => [A|[A B] b]. 
  - split; first by apply: A. move => b in_s. apply A. by rewrite inE in_s orbT.
  - rewrite inE. case/orS => [/eqP -> //|]. exact: B. 
Qed.

Lemma bigmax_seq_sup (T : eqType) (s:seq T) (P : pred T) F k m :
  k \in s -> P k -> m <= F k -> m <= \max_(i <- s | P i) F i.
Proof. move => A B C. by rewrite (big_rem k) //= B leq_max C. Qed.

Lemma max_mem n0 (s : seq nat) : n0 \in s -> \max_(i <- s) i \in s.
Proof.
  case: s => // a s _. rewrite big_cons big_seq.
  elim/big_ind : _ => // [n m|n A].
  - rewrite -{5}[a]maxnn maxnACA => ? ?. rewrite {1}/maxn. by case: ifP.
  - rewrite /maxn. case: ifP => _ //. by rewrite inE A orbT.
Qed.

(* reasoning about singletons *)
Lemma seq1P (T : eqType) (x y : T) : reflect (x = y) (x \in [:: y]).
Proof. rewrite inE. exact: eqP. Qed.

Lemma sub1P (T : eqType) x (p : pred T) : reflect {subset [:: x] <= p} (x \in p).
Proof. apply: (iffP idP) => [A y|]; by [rewrite inE => /eqP->|apply]. Qed.

(** Finite Types - fintype.v *)

Lemma sub_forall (T: finType) (p q : pred T) :
  subpred p q -> [forall x : T, p x] -> [forall x : T, q x].
Proof. move => sub /forallP H. apply/forallP => x. exact: sub. Qed.

Lemma sub_exists (T : finType) (P1 P2 : pred T) :
  subpred P1 P2 -> [exists x, P1 x] -> [exists x, P2 x].
Proof. move => H. case/existsP => x /H ?. apply/existsP. by exists x. Qed.

Lemma card_leq_inj (T T' : finType) (f : T -> T') : injective f -> #|T| <= #|T'|.
Proof. move => inj_f. by rewrite -(card_imset predT inj_f) max_card. Qed.

Lemma bij_card {X Y : finType} (f : X->Y): bijective f -> #|X| = #|Y|.
Proof.
  case => g /can_inj Hf /can_inj Hg. apply/eqP.
  by rewrite eqn_leq (card_leq_inj Hf) (card_leq_inj Hg).
Qed.

Lemma cardT_eq (T : finType) (p : pred T) : #|{: { x | p x}}| = #|T| -> p =1 predT.
Proof. move/(inj_card_bij val_inj) => [g g1 g2 x]. rewrite -(g2 x). exact: valP. Qed.

(** Finite Ordinals *)

Lemma inord_max n : ord_max = inord n :> 'I_n.+1.
Proof. by rewrite -[ord_max]inord_val. Qed.

Lemma inord0 n : ord0 = inord 0 :> 'I_n.+1.
Proof. by rewrite -[ord0]inord_val. Qed.

Definition ord1 {n} := (@Ordinal (n.+2) 1 (erefl _)).

Lemma inord1 n : ord1 = inord 1 :> 'I_n.+2. 
Proof. apply: ord_inj => /=. by rewrite inordK. Qed.

Hint Resolve ltn_ord : core.

(** Finite Sets - finset.v *)

Lemma card_set (T:finType) : #|{set T}| = 2^#|T|.
Proof. rewrite -!cardsT -powersetT. exact: card_powerset. Qed.

(** Miscellaneous *)

Lemma Sub_eq (T : Type) (P : pred T) (sT : subType P) (x y : T) (Px : P x) (Py : P y) : 
  (@Sub _ _ sT) x Px = Sub y Py <-> x = y.
Proof. 
  split => [|e]. 
  - by rewrite -{2}[x](SubK sT) -{2}[y](SubK sT) => ->. 
  - move: Py. rewrite -e => Py. by rewrite (bool_irrelevance Py Px).
Qed.

Local Open Scope quotient_scope.
Lemma epiK {T:choiceType} (e : equiv_rel T) x : e (repr (\pi_{eq_quot e} x)) x.
Proof. by rewrite -eqmodE reprK. Qed.

Lemma set_enum (T : finType) : [set x in enum T] = [set: T].
Proof. apply/setP => x. by rewrite !inE  mem_enum. Qed.

Lemma find_minn_bound (p : pred nat) m :
  {n | [/\ n < m, p n & forall i, i < n -> ~~ p i]} + {(forall i, i < m -> ~~ p i)}.
Proof.
  case: (boolP [exists n : 'I_m, p n]) => C ; [left|right].
  - have/find_ex_minn: exists n, (n < m) && p n.
      case/existsP : C => [[n Hn pn]] /=. exists n. by rewrite Hn.
    case => n /andP [lt_m pn] min_n. exists n. split => // i Hi.
    apply: contraTN (Hi) => pi. rewrite -leqNgt min_n // pi andbT.
    exact: ltn_trans lt_m.
  - move => i lt_m. move: C. by rewrite negb_exists => /forallP /(_ (Ordinal lt_m)).
Qed.

(** Relations *)

Section Functional.
  Variables (T T' : finType) (e : rel T) (e' : rel T') (f : T -> T').

  Definition terminal x := forall y, e x y = false.
  Definition functional := forall x y z, e x y -> e x z -> y = z.

  Lemma term_uniq x y z : functional ->
    terminal y -> terminal z -> connect e x y -> connect e x z -> y = z.
  Proof. 
    move => fun_e Ty Tz /connectP [p] p1 p2 /connectP [q]. 
    elim: p q x p1 p2 => [|a p IH] [|b q] x /=; first congruence.
    - move => _ <-. by rewrite Ty.
    - case/andP => xa _ _ _ H. by rewrite -H Tz in xa.
    - case/andP => xa p1 p2 /andP [xb] q1 q2. 
      move: (fun_e _ _ _ xa xb) => ?; subst b. exact: IH q2.
  Qed.

  Hypothesis f_inj : injective f.
  Hypothesis f_eq : forall x y, e x y = e' (f x) (f y).
  Hypothesis f_inv: forall x z, e' (f x) z -> exists y, z = f y. 

  Lemma connect_transfer x y : connect e x y = connect e' (f x) (f y).
  Proof. apply/idP/idP.
    - case/connectP => s.
      elim: s x => //= [x _ -> |z s IH x]; first exact: connect0.
      case/andP => xz pth Hy. rewrite f_eq in xz.
      apply: connect_trans (connect1 xz) _. exact: IH.
    - case/connectP => s.
      elim: s x => //= [x _ /f_inj -> |z s IH x]; first exact: connect0.
      case/andP => xz pth Hy. case: (f_inv xz) => z' ?; subst. 
      rewrite -f_eq in xz. apply: connect_trans (connect1 xz) _. exact: IH.
  Qed.  
End Functional.

Lemma functional_sub (T : finType) (e1 e2 : rel T) : 
  functional e2 -> subrel e1 e2 -> functional e1.
Proof. move => f_e2 sub x y z /sub E1 /sub E2. exact: f_e2 E1 E2. Qed.

(** ** Inverting surjective functions *)

Definition surjective aT {rT : eqType} (f : aT -> rT) := forall y, exists x, f x == y.

Lemma surjectiveE (rT aT : finType) (f : aT -> rT) : surjective f -> #|codom f| = #|rT|.
Proof.
  move => H. apply: eq_card => x. rewrite inE. apply/codomP.
  move: (H x) => [y /eqP]. eauto.
Qed.

Lemma surj_card_bij (T T' : finType) (f : T -> T') :
  surjective f -> #|T| = #|T'| -> bijective f.
Proof.
  move => S E. apply: inj_card_bij (E). apply/injectiveP. change (uniq (codom f)).
  apply/card_uniqP. rewrite size_map -cardT E. exact: surjectiveE.
Qed.

(* We define a general inverse of surjective functions from choiceType -> eqType.
   This function gives a canonical representative, thus the name "cr". *)
Definition cr {X : choiceType} {Y : eqType} {f : X -> Y} (Sf : surjective f) y : X :=
  xchoose (Sf y).

Lemma crK {X : choiceType} {Y : eqType} {f : X->Y} {Sf : surjective f} x: f (cr Sf x) = x.
Proof. by rewrite (eqP (xchooseP (Sf x))). Qed.



Lemma dec_eq (P : Prop) (decP : decidable P) : decP <-> P.
Proof. by case: decP. Qed.




