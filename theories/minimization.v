(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph finfun finset generic_quotient.
From RegLang Require Import misc languages dfa.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.

Local Open Scope quotient_scope.

(** * DFA Minimization *)

Section Minimization.
Variable (char : finType).
Local Notation word := (word char).
Local Notation dfa := (dfa char).

Definition coll (A : dfa) x y := forall w, (delta x w \in dfa_fin A) = (delta y w \in dfa_fin A).

Definition connected (A : dfa) := surjective (delta_s A).
Definition collapsed (A : dfa) := forall x y: A, coll x y <-> x = y.
Definition minimal (A : dfa) := forall B, dfa_lang A =i dfa_lang B -> #|A| <= #|B|.

(** ** Uniqueness of connected and collapsed automata *)

Definition dfa_iso (A1 A2 : dfa) :=
  exists i: A1 -> A2,
    [/\ bijective i,
        forall x a, i (dfa_trans x a) = dfa_trans (i x) a,
        forall x, i (x) \in dfa_fin A2 = (x \in dfa_fin A1) &
        i (dfa_s A1) = dfa_s A2 ].

Section Isomopism.
  Variables (A B : dfa).
  Hypothesis L_AB : dfa_lang A =i dfa_lang B.

  Hypothesis (A_coll: collapsed A) (B_coll: collapsed B).
  Hypothesis (A_conn : connected A) (B_conn : connected B).

  Definition iso := delta_s B \o cr A_conn.
  Definition iso_inv := delta_s A \o cr B_conn.

  Lemma delta_iso w x : delta (iso x) w \in dfa_fin B = (delta x w \in dfa_fin A).
  Proof using L_AB. by rewrite -{2}[x](crK (Sf := A_conn)) -!delta_cat !delta_lang L_AB. Qed.

  Lemma delta_iso_inv w x : delta (iso_inv x) w \in dfa_fin A = (delta x w \in dfa_fin B).
  Proof using L_AB. by rewrite -{2}[x](crK (Sf := B_conn)) -!delta_cat !delta_lang L_AB. Qed.

  Lemma can_iso : cancel iso_inv iso.
  Proof using B_coll L_AB. move => x. apply/B_coll => w. by rewrite delta_iso delta_iso_inv. Qed.

  Lemma can_iso_inv : cancel iso iso_inv.
  Proof using A_coll L_AB. move => x. apply/A_coll => w. by rewrite delta_iso_inv delta_iso. Qed.

  Lemma coll_iso : dfa_iso A B.
  Proof using A_coll B_coll A_conn B_conn L_AB.
    exists iso. split.
    - exact: Bijective can_iso_inv can_iso.
    - move => x a. apply/B_coll => w. rewrite -[_ (iso x) a]/(delta (iso x) [::a]).
      by rewrite -delta_cat -!delta_iso_inv !can_iso_inv.
    - move => x. by rewrite -[iso x]/(delta _ [::]) delta_iso.
    - apply/B_coll => w. by rewrite delta_iso !delta_lang.
  Qed.

  Lemma dfa_iso_size : dfa_iso A B -> #|A| = #|B|.
  Proof. move => [iso [H _ _ _]]. exact (bij_eq_card H). Qed.
End Isomopism.

Lemma abstract_minimization A f :
  (forall B, dfa_lang (f B) =i dfa_lang B /\ #|f B| <= #|B| /\ connected (f B) /\ collapsed (f B))
  -> minimal (f A).
Proof.
  move => H B L_AB. apply: (@leq_trans #|f B|); last by firstorder. apply: eq_leq.
  apply: dfa_iso_size. (apply: coll_iso; try apply H) => w. rewrite L_AB. by case (H B) => ->.
Qed.

(** ** Construction of the Connected Sub-Automaton *)

Section Prune.
  Variable A : dfa.

  Definition reachable (q:A) := exseq_dec (@delta_rc _ A) (pred1 q).
  Definition connectedb := [forall x: A, reachable x].

  Lemma connectedP : reflect (connected A) (connectedb).
  Proof.
    apply: (iffP forallP) => H y; first by move/dec_eq: (H y).
    apply/dec_eq. case (H y) => x Hx. by exists x.
  Qed.

  Definition reachable_type := { x:A | reachable x }.

  Lemma reachable_trans_proof (x : reachable_type) a : reachable (dfa_trans (val x) a).
  Proof.
    apply/dec_eq. case/dec_eq : (svalP x) =>  /= y /eqP <-.
    exists (y++[::a]). by rewrite delta_cat.
  Qed.

  Definition reachable_trans (x : reachable_type) a : reachable_type :=
    Sub (dfa_trans (val x) a) (reachable_trans_proof x a).

  Lemma reachabe_s_proof : reachable (dfa_s A).
  Proof. apply/dec_eq. exists nil. exact: eqxx. Qed.

  Definition reachable_s : reachable_type := Sub (dfa_s A) reachabe_s_proof.

  Definition dfa_prune := {|
      dfa_s := reachable_s;
      dfa_fin := [set x | val x \in dfa_fin A];
      dfa_trans := reachable_trans |}.

  Lemma dfa_prune_correct : dfa_lang dfa_prune =i dfa_lang A.
  Proof.
    rewrite /dfa_lang /= -[dfa_s A]/(val reachable_s) => w.
    rewrite !inE. elim: w (reachable_s) => [|a w IHw] [x Hx] //=.
    + by rewrite /dfa_accept inE.
    + by rewrite accE IHw.
  Qed.

  Lemma dfa_prune_connected : connected dfa_prune.
  Proof.
    move => q. case/dec_eq: (svalP q) => /= x Hx. exists x.
    elim/last_ind : x q Hx => //= x a IHx q.
    rewrite -!cats1 /delta_s !delta_cat -!/(delta_s _ x) => H.
    have X : reachable (delta_s A x). apply/dec_eq; exists x. exact: eqxx.
    by rewrite (eqP (IHx (Sub (delta_s A x) X) _)).
  Qed.

  #[local] Hint Resolve dfa_prune_connected : core.

  Lemma dfa_prune_size : #|dfa_prune| <= #|A|.
  Proof. by rewrite card_sig subset_leq_card // subset_predT. Qed.

  (** If pruning does not remove any states, the automaton is connected *)

  Lemma prune_eq_connected : #|A| = #|dfa_prune| -> connected A.
  Proof.
    move => H. apply/connectedP. apply/forallP => x.
    by move: (cardT_eq (Logic.eq_sym H)) ->.
  Qed.

End Prune.

(** ** Quotient modulo collapsing relation

For the minimization of connected automata we construct the quotient of the
input automaton with respect to the collapsing relation. To form the quotient
constructively, we have to show that the collapsing relation is decidable. *)

Section Collapse.
  Variable A : dfa.

  (** Decidabilty of the collapsing relation   *)

  Definition coll_fun (p q : A) x := (delta p x,delta q x).

  Lemma coll_fun_RC p q x y a :
    coll_fun p q x = coll_fun p q y -> coll_fun p q (x++[::a]) = coll_fun p q (y++[::a]).
  Proof. move => [H1 H2]. by rewrite /coll_fun !delta_cat H1 H2. Qed.

  Definition collb p q : bool :=
    allseq_dec (@coll_fun_RC p q) [pred p | (p.1 \in dfa_fin A) == (p.2 \in dfa_fin A)].

  Lemma collP p q : reflect (coll p q) (collb p q).
  Proof.
    apply: (iffP idP).
    - move/dec_eq => H x. by move/eqP: (H x).
    - move => H. apply/dec_eq => x. apply/eqP. exact: H.
  Qed.

  Lemma collb_refl x : collb x x.
  Proof. apply/collP. rewrite /coll. auto. Qed.

  Lemma collb_sym : symmetric collb.
  Proof. move => x y. by apply/collP/collP; move => H w; rewrite H. Qed.

  Lemma collb_trans : transitive collb.
  Proof. move => x y z /collP H1 /collP H2. apply/collP => w. by rewrite H1 H2. Qed.

  Lemma collb_step a x y : collb x y -> collb (dfa_trans x a) (dfa_trans y a).
  Proof. move => /collP H. apply/collP => w. by rewrite !delta_cons H. Qed.

  (** We make collb the canonical equivalence relation on [A] and take
  the corresponding quotient type as state space for the minimized automaton *)

  Canonical collb_equiv := EquivRelPack (EquivClass collb_refl collb_sym collb_trans).

  Definition collapse_state := {eq_quot collb_equiv}.

  HB.instance Definition _ := Quotient.on collapse_state.
  HB.instance Definition _ := [Sub collapse_state of A by %/].
  HB.instance Definition _ := [Finite of collapse_state by <:%/].

  Definition collapse : dfa := {|
    dfa_s := \pi_(collapse_state) (dfa_s A);
    dfa_trans x a := \pi (dfa_trans (repr x) a);
    dfa_fin := [set x : collapse_state | repr x \in dfa_fin A ] |}.

  Lemma collapse_delta (x : A) w :
    delta (\pi x : collapse) w = \pi (delta x w).
  Proof.
    elim: w x => //= a w IHw x. rewrite -IHw. f_equal.
    apply/eqmodP. apply: collb_step. exact: epiK.
  Qed.

  Lemma collapse_fin (x : A) :
    (\pi x \in dfa_fin collapse) = (x \in dfa_fin A).
  Proof.
    rewrite /collapse /= inE.
    by move/collP: (epiK collb_equiv x) => /(_ [::]).
  Qed.

End Collapse.

(** ** Correctness of Minimization *)

(** Minimization yields a fully collapsed DFA accepting the same language *)

Lemma collapse_collapsed (A  : dfa) : collapsed (collapse A).
Proof.
  split => [H|->]; last by apply/collP; exact: collb_refl.
  rewrite -[x]reprK -[y]reprK. apply/eqmodP/collP => w.
  by rewrite -!collapse_fin -!collapse_delta !reprK.
Qed.

Lemma collapse_correct A : dfa_lang (collapse A) =i dfa_lang A.
Proof.
  move => w. rewrite !inE /dfa_accept {1}/dfa_s /= inE collapse_delta.
  by rewrite -!collapse_fin reprK.
Qed.

Lemma collapse_size A : #|collapse A| <= #|A|.
Proof. rewrite card_sub. exact: max_card. Qed.

Lemma collapse_connected A : connected A -> connected (collapse A).
Proof.
  move => H x. case: (H (repr x)) => w /eqP Hw. exists w.
  by rewrite /delta_s collapse_delta -/(delta_s A w) Hw reprK.
Qed.

(** Combine pruning and collapsing into minimization function *)

Definition minimize := collapse \o dfa_prune.

Lemma minimize_size (A : dfa) : #|minimize A| <= #|A|.
Proof. exact: leq_trans (collapse_size _) (dfa_prune_size _). Qed.

Lemma minimize_collapsed (A : dfa) : collapsed (minimize A).
Proof. exact: collapse_collapsed. Qed.

Lemma minimize_connected (A : dfa) : connected (minimize A).
Proof. apply collapse_connected. exact: dfa_prune_connected. Qed.

Lemma minimize_correct (A : dfa) : dfa_lang (minimize A) =i dfa_lang A.
Proof. move => x. by rewrite collapse_correct dfa_prune_correct. Qed.

#[local] Hint Resolve minimize_size minimize_collapsed minimize_connected : core.

Lemma minimize_minimal A : minimal (minimize A).
Proof. apply: abstract_minimization => B. auto using minimize_correct. (* and hints *) Qed.

(** ** Uniqueness of minimal automaton *)

Lemma minimal_connected A : minimal A -> connected A.
Proof.
  move => MA. apply: prune_eq_connected.
  apply/eqP. rewrite eqn_leq dfa_prune_size andbT.
  apply: MA => x. by rewrite dfa_prune_correct.
Qed.

Lemma minimal_collapsed A : minimal A -> collapsed A.
Proof.
  move => MA.
  have B : bijective (\pi_(collapse_state A)).
    apply: surj_card_bij.
    - move => x. exists (repr x). by rewrite reprK.
    - apply/eqP. rewrite eqn_leq collapse_size (MA (collapse A)) // => x.
      by rewrite collapse_correct.
  move => x y. split => [|->]; last exact/collP/collb_refl.
  move/collP/eqmodP. exact: bij_inj.
Qed.

(** In order to generalize the reasoning above to arbitrary quotients
types over finite types we would first have to ensure that [{eq_quot e}]
inherits the finType structure on the carrier of [e]. By default
this is not the case *)

Lemma minimalP A : minimal A <-> (connected A /\ collapsed A).
Proof.
  split.
  - move => H. split. exact: minimal_connected. exact: minimal_collapsed.
  - move => [H1 H2] B L_AB. apply: leq_trans _ (minimize_size _). apply: eq_leq.
    apply: dfa_iso_size. apply: coll_iso => // x. by rewrite minimize_correct.
Qed.

Lemma minimal_iso A B :
  dfa_lang A =i dfa_lang B -> minimal A -> minimal B -> dfa_iso A B.
Proof. move => L_AB /minimalP [? ?] /minimalP [? ?]. exact: coll_iso. Qed.

End Minimization.
