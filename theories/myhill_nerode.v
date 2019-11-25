(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
Require Import misc languages dfa minimization regexp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Classifiers *)

(** For us, classifiers (right-congruent functions from words into
some finite type) serve as a constructive approximation of
Myhill-Nerode partition. We show that classifiers for given language
can be turned into DFAs and vice versa. Moroever, we show that there
exist most general classifiers corresponding to minimal automata. *)

Section Clasifiers.

Variable char: finType.
Local Notation word := (word char).

Record classifier := Classifier {
  classifier_classes : finType;
  classifier_fun :> word -> classifier_classes }.

Notation classes_of := classifier_classes.

(** It would be desirable to have classifiers also coerce to [finType]
(to be able to write #|E| for the number of classes). However, this
introduces an ambiguity since [finType] already coerces to Funclass
(as the universally true predicate). *)


Definition right_congruent (X : eqType) (E : word -> X) :=
  forall u v a, E u = E v -> E (u ++ [::a]) = E (v ++ [::a]).

Definition refines (X: eqType) (L : dlang char) (E : word -> X) :=
  forall u v, E u = E v -> (u \in L) = (v \in L).

Record classifier_for L := {
    cf_classifier :> classifier;
    cf_congruent : right_congruent cf_classifier;
    cf_refines : refines L cf_classifier
  }.

Lemma cf_lang_eq_proof L1 L2 (M1 : classifier_for L1) : L1 =i L2 -> refines L2 M1.
Proof. move => H0 u v /cf_refines. by rewrite -!H0. Qed.

Definition cf_lang_eq L1 L2 (M1 : classifier_for L1) (H : L1 =i L2) :=
  {| cf_congruent := @cf_congruent L1 M1; cf_refines := cf_lang_eq_proof H |}.


(** ** Conversions between Classifiers and DFAs *)

Section DFAtoClassifier.
  Variable (A : dfa char).

  Lemma delta_s_right_congruent : right_congruent (delta_s A).
  Proof. move => u v a H. rewrite /= /delta_s !delta_cat. by f_equal. Qed.

  Lemma delta_s_refines : refines (dfa_lang A) (delta_s A).
  Proof. move => u v H. rewrite -!delta_lang. by f_equal. Qed.

  Definition dfa_to_cf : classifier_for (dfa_lang A) :=
    {| cf_classifier := Classifier (delta_s A);
       cf_congruent := delta_s_right_congruent;
       cf_refines := delta_s_refines |}.

  Lemma dfa_to_cf_size : #|A| = #|classes_of dfa_to_cf|. by []. Qed.
End DFAtoClassifier.


Section ClassifierToDFA.
  Variables (L : dlang char) (M : classifier_for L).

  Definition imfun_of := image_fun (@cf_congruent _ M).
  Definition imfun_of_surj := @surjective_image_fun _ _ _ (@cf_congruent _ M).

  Lemma imfun_of_refines : refines L imfun_of.
  Proof. move => x y []. exact: cf_refines. Qed.

  Lemma imfun_of_congruent : right_congruent imfun_of.
  Proof.
    move => x y a [] /cf_congruent.
    move/(_ a) => /eqP H. exact/eqP.
  Qed.
  
  Definition classifier_to_dfa :=
    {| dfa_s := imfun_of [::]; 
       dfa_fin := [set x | cr (imfun_of_surj) x \in L];
       dfa_trans x a := imfun_of (cr (imfun_of_surj) x ++ [::a]) |}.

  Lemma classifier_to_dfa_delta : delta_s classifier_to_dfa =1 imfun_of.
  Proof.
    apply: last_ind => [|w a IHw] //=.
    rewrite /delta_s -cats1 delta_cat -!/(delta_s _ _) IHw.
    apply: imfun_of_congruent. by rewrite crK.
  Qed.

  Lemma classifier_to_dfa_correct : dfa_lang classifier_to_dfa =i L.
  Proof.
    move => w. rewrite -delta_lang classifier_to_dfa_delta inE.
    apply: imfun_of_refines. by rewrite crK.
  Qed.
End ClassifierToDFA.

Lemma classifier_to_dfa_connected L (M : classifier_for L) :
  connected (classifier_to_dfa M).
Proof. 
  move => q. exists (cr (@imfun_of_surj _ M) q).
  rewrite -{2}[q](crK (Sf:=(@imfun_of_surj _ M))).
  by rewrite -/(delta_s _ _) classifier_to_dfa_delta.
Qed.

(** ** Most General Classifiers

Just like there exists a coarsest Myhill-Nerode relation, there also
exist most general classifiers. For these classifiers, the classes
correspond exactly to thos of the coarsest Myhill-Nerode relation. *)

Definition nerode (X : eqType) (L : dlang char) (E : word -> X) :=
  forall u v, E u = E v <->  forall w, (u++w \in L) = (v++w \in L).

Record mgClassifier L := {
    mg_classifier :> classifier;
    nerodeP : nerode L mg_classifier }.

Lemma mg_right_congruent L (N : mgClassifier L) : right_congruent N.
Proof. move => u v a /nerodeP H. apply/nerodeP => w. by rewrite -!catA. Qed.

Lemma mg_refines L (N : mgClassifier L) : refines L N.
Proof. move => u v /nerodeP H. by rewrite -[u]cats0 -[v]cats0. Qed.

Definition mg_to_classifier L (N : mgClassifier L) := {|
  cf_congruent := @mg_right_congruent L N;
  cf_refines := @mg_refines L N |}.

Coercion mg_to_classifier : mgClassifier >-> classifier_for.

Arguments cf_congruent [L M u v a] H: rename.
Arguments cf_refines [L M u v] H: rename.
Arguments nerodeP [L] N u v: rename.

(** Most general classifiers coerce to classifiers and can be converted to DFAs *)

Definition mg_to_dfa L (N : mgClassifier L) := classifier_to_dfa N.

Lemma mg_to_dfa_correct L (N : mgClassifier L) : dfa_lang (mg_to_dfa N) =i L.
Proof. exact: classifier_to_dfa_correct. Qed.

Lemma mg_to_connected L (N : mgClassifier L) : connected (mg_to_dfa N).
Proof. exact: classifier_to_dfa_connected. Qed.

(** Most general classifier yield minimal automata *)

Lemma mg_minimal (L : dlang char) (M : mgClassifier L) : minimal (mg_to_dfa M).
Proof.
  apply/minimalP. split; first exact: mg_to_connected.
  move => p q. split => [coll_pq|->//]. 
  rewrite -[p](crK (Sf := (@imfun_of_surj _ M))).
  rewrite -[q](crK (Sf := (@imfun_of_surj _ M))).
  apply/Sub_eq. apply/nerodeP => w.
  rewrite -!(@classifier_to_dfa_correct _ M) !inE /dfa_accept !delta_cat.
  rewrite -!/(delta_s _ _) !classifier_to_dfa_delta !crK. exact: coll_pq.
Qed.

(** We can cast mgClassifiers to equivalent languages *)

Lemma mg_eq_proof L1 L2 (N1 : mgClassifier L1) : L1 =i L2 -> nerode L2 N1.
Proof. move => H0 u v. split => [/nerodeP H1 w|H1].
  - by rewrite -!H0.
  - apply/nerodeP => w. by rewrite !H0.
Qed.

Definition mg_eq L1 L2 N1 (H : L1 =i L2) := {| nerodeP := mg_eq_proof N1 H |}.

(** Minimal DFAs immediately give rise to most general classifiers. *)

Section mDFAtoMG.
  Variable A : dfa char.
  Variable MA : minimal A.

  Lemma minimal_nerode : nerode (dfa_lang A) (delta_s A).
  Proof.
    move => u v. apply: iff_trans (iff_sym (minimal_collapsed MA _ _)) _.
    by split => H w; move: (H w); rewrite -!delta_cat !delta_lang.
  Qed.

  Definition minimal_classifier := {| classifier_fun := delta_s A |}.

  Definition dfa_to_mg := {|
    mg_classifier := minimal_classifier; 
    nerodeP := minimal_nerode |}.
End mDFAtoMG.

End Clasifiers.
