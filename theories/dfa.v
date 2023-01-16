(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import misc languages.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.

Section FA.
Variable char : finType.
Local Notation word := (word char).

(** * Deterministic Finite Automata *)

Record dfa : Type := {
    dfa_state :> finType;
    dfa_s : dfa_state;
    dfa_fin : {set dfa_state};
    dfa_trans : dfa_state -> char -> dfa_state }.

(* Arguments dfa_fin d _ : clear implicits. *)

(** We define acceptance for every state of a DFA. The language of a
DFA is then just the language of the starting state. *)

Section DFA_Acceptance.
Variable A : dfa.
Implicit Types (p q : A) (x y : word).

Fixpoint delta (p : A) x :=
  if x is a :: x' then delta (dfa_trans p a) x' else p.

Lemma delta_cons p a x : delta (dfa_trans p a) x = delta p (a :: x).
Proof. by []. Qed.

Lemma delta_cat p x y : delta p (x ++ y) = delta (delta p x) y.
Proof. elim: x p => // a x /= IH p. by rewrite IH. Qed.

Definition dfa_accept (p : A) x := delta p x \in dfa_fin A.

Definition delta_s w := delta (dfa_s A) w.
Definition dfa_lang := [pred x | dfa_accept (dfa_s A) x].

Lemma accept_nil p : dfa_accept p [::] = (p \in dfa_fin A).
Proof. by []. Qed.

Lemma accept_cons (x : A) a w :
  dfa_accept x (a :: w) = dfa_accept (dfa_trans x a) w.
Proof. by []. Qed.

Lemma delta_lang x : (delta_s x \in dfa_fin A) = (x \in dfa_lang).
Proof. by []. Qed.

Definition accE := (accept_nil,accept_cons).

End DFA_Acceptance.

(** ** Regularity

We formalize the notion of regularity as the type of DFAs accpepting
the language under consideration. This allows closure properties to be
used for the construction of translation functions. Where required,
the propositional variant of regularity is obtained as [inhabited (regular L)]. *)

Definition regular (L : lang char) := { A : dfa | forall x, L x <-> x \in dfa_lang A }.

Lemma regular_ext L1 L2 : regular L2 -> L1 =p L2 -> regular L1.
Proof. case => A HA B. exists A => w. by rewrite B. Qed.

(** ** Operations on DFAs

To prepare the translation from regular expresstions to DFAs, we show
that finite automata are closed under all regular operations. We build
the primitive automata, complement and boolean combinations using
DFAs. *)

Definition dfa_void :=
  {| dfa_s := tt; dfa_fin := set0 ; dfa_trans x a := tt |}.

Lemma dfa_void_correct (x: dfa_void) w: ~~ dfa_accept x w.
Proof. by rewrite /dfa_accept inE. Qed.

Section DFAOps.

Variable op : bool -> bool -> bool.
Variable A1 A2 : dfa.

(** Complement automaton **)
Definition dfa_compl :=
  {| dfa_s := dfa_s A1;
     dfa_fin := ~: (dfa_fin A1);
     dfa_trans := (@dfa_trans A1) |}.

Lemma dfa_compl_correct w :
  w \in dfa_lang dfa_compl = (w \notin dfa_lang A1).
Proof.
  rewrite /dfa_lang !inE {2}/dfa_compl /=.
  by rewrite /dfa_accept inE.
Qed.

(** BinOp Automaton *)

Definition dfa_op  :=
  {| dfa_s := (dfa_s A1, dfa_s A2);
     dfa_fin := [set q | op (q.1 \in dfa_fin A1) (q.2 \in dfa_fin A2)];
     dfa_trans x a := (dfa_trans x.1 a, dfa_trans x.2 a) |}.

Lemma dfa_op_correct w :
  w \in dfa_lang dfa_op = op (w \in dfa_lang A1) (w \in dfa_lang A2).
Proof.
  rewrite !inE {2}/dfa_op /=.
  elim: w (dfa_s A1) (dfa_s A2) => [| a w IHw] x y; by rewrite !accE ?inE /=.
Qed.

Definition dfa0 := {| dfa_s := tt; dfa_trans q a := tt; dfa_fin := set0 |}.

Lemma dfa0_correct x : x \in dfa_lang dfa0 = false.
Proof. by rewrite -delta_lang inE. Qed.

End DFAOps.

Lemma regular_inter (L1 L2 : lang char) :
  regular L1 -> regular L2 -> regular (fun x => L1 x /\ L2 x).
Proof.
  move => [A LA] [B LB]. exists (dfa_op andb A B) => x.
  by rewrite dfa_op_correct LA LB (rwP andP).
Qed.

Lemma regular0 : regular (fun _ : word => False).
Proof. exists (dfa0) => x. by rewrite dfa0_correct. Qed.

Lemma regularU (L1 L2 : lang char) :
  regular L1 -> regular L2 -> regular (fun x => L1 x \/ L2 x).
Proof.
  move => [A1 acc_L1] [A2 acc_L2]. exists (dfa_op orb A1 A2) => x.
  by rewrite dfa_op_correct -(rwP orP) -acc_L1 -acc_L2.
Qed.

Lemma regular_bigU (T : eqType) (L : T -> lang char) (s : seq T) :
  (forall a, a \in s -> regular (L a)) -> regular (fun x => exists2 a, a \in s & L a x).
Proof.
  elim: s => //.
  - move => _. apply: regular_ext regular0 _. by split => // [[a]].
  - move => a s IH /forall_consT [H1 H2].
    pose L' := (fun x => L a x \/ (fun x : word => exists2 a : T, a \in s & L a x) x).
    apply: (regular_ext (L2 := L')); first by apply: regularU => //; exact: IH.
    move => x. rewrite /L'. exact: exists_cons.
Qed.



(** ** Cut-Off Criterion  *)

Section CutOff.
  Variables (aT rT : finType) (f : seq aT -> rT).
  Hypothesis RC_f : forall x y a, f x = f y -> f (x++[::a]) = f (y++[::a]).
  Local Set Default Proof Using "RC_f".

  Lemma RC_seq x y z : f x = f y -> f (x++z) = f (y++z).
  Proof.
    elim: z x y => [|a z IHz] x y; first by rewrite !cats0.
    rewrite -(cat1s a) (catA x [::a]) (catA y [::a]). move/(RC_f a). exact: IHz.
  Qed.

  Lemma RC_rep x (i j : 'I_(size x)) :
    i < j -> f (take i x) = f (take j x) -> f (take i x ++ drop j x) = f x.
  Proof. move => Hij Hfij. rewrite -{5}(cat_take_drop j x). exact: RC_seq. Qed.


  Definition exseqb (p : pred rT) :=
    [exists n : 'I_#|rT|.+1, exists x : n.-tuple aT, p (f x)].

  Lemma exseqP (p : pred rT) : reflect (exists x, p (f x)) (exseqb p).
  Proof.
    apply: (iffP idP); last case.
    - case/existsP => n. case/existsP => x Hx. by exists x.
    - apply: (size_induction (measure := size)) => x IHx px.
      case H: (size x < #|rT|.+1).
      + apply/existsP. exists (Ordinal H). apply/existsP. by exists (in_tuple x).
      + have: ~ injective (fun i : 'I_(size x) => f (take i x)).
        { move/card_leq_inj. by rewrite -ltnS /= card_ord H. }
        move/injectiveP/injectivePn => [i [j]] Hij.
        wlog ltn_ij : i j {Hij} / i < j => [W|] E.
        { move: Hij. rewrite neq_ltn. case/orP => l; exact: W l _. }
        apply: (IHx (take i x ++ drop j x)); last by rewrite RC_rep.
        by rewrite size_cat size_take size_drop ltn_ord -ltn_subRL ltn_sub2l.
  Qed.

  Lemma exseq_dec (p : pred rT) : decidable (exists x, p (f x)).
  Proof. apply: decP. exact: exseqP. Qed.

  Lemma allseq_dec (p : pred rT) : decidable (forall x, p (f x)).
  Proof.
    case: (exseq_dec (predC p)) => H;[right|left].
    - move => A. case: H => [x /= Hx]. by rewrite A in Hx.
    - move => x. apply: contra_notT H => C. by exists x.
  Qed.

  (** Construction of Image *)

  Definition image_type := { a : rT | exseq_dec (pred1 a) }.

  Lemma image_fun_proof (x : seq aT) : exseq_dec (pred1 (f x)).
  Proof. apply/dec_eq. by exists x => /=. Qed.

  Definition image_fun (x : seq aT) : image_type := Sub (f x) (image_fun_proof x).

  Lemma surjective_image_fun : surjective (image_fun).
  Proof. move => [y Py]. case/dec_eq : (Py) => /= x ?. by exists x. Qed.

End CutOff.

(** ** Decidability of Language Equivalence

Language emptiness and inhabitation of DFAs is deciadable since the [delta]
function is right congruent *)

Section Emptyness.
  Variable A : dfa.

  Lemma delta_rc x y a : let s := dfa_s A in
    delta s x = delta s y -> delta s (x ++ [::a]) = delta s (y ++ [::a]).
  Proof. by rewrite /= !delta_cat => <-. Qed.

  Definition dfa_inhab : decidable (exists x, x \in dfa_lang A) :=
    exseq_dec delta_rc (fun x => x \in dfa_fin A).

  Lemma dfa_inhabP : reflect (exists x, x \in dfa_lang A) (dfa_inhab).
  Proof. apply: (iffP idP); by rewrite dec_eq. Qed.

  Definition dfa_empty := allseq_dec delta_rc (fun x => x \notin dfa_fin A).

  Lemma dfa_emptyP : reflect (dfa_lang A =i pred0) (dfa_empty).
  Proof.
    apply: (iffP idP) => [/dec_eq H x|H]; first by rewrite inE /dfa_accept (negbTE (H _)).
    apply/dec_eq => x. by rewrite -[_ \notin _]/(x \notin dfa_lang A) H.
  Qed.
End Emptyness.

(** The problem of deciding language eqivalence reduces to the problem
of deciding emptiness of [A [+] B] *)

Definition dfa_equiv A1 A2 := dfa_empty (dfa_op addb A1 A2).

Lemma dfa_equiv_correct A1 A2 :
  reflect (dfa_lang A1 =i dfa_lang A2) (dfa_equiv A1 A2).
Proof.
  apply: (iffP (dfa_emptyP _)) => H w.
  - move/negbT: (H w). rewrite !dfa_op_correct -addNb.
    move/addbP. by rewrite negbK.
  - apply/negbTE. by rewrite !dfa_op_correct H addbb.
Qed.

Definition dfa_incl A1 A2 := dfa_empty (dfa_op (fun a b => a && ~~ b) A1 A2).

Lemma dfa_incl_correct A1 A2 :
  reflect {subset dfa_lang A1 <= dfa_lang A2} (dfa_incl A1 A2).
Proof.
  apply: (iffP (dfa_emptyP _)) => H w.
  - move/negbT: (H w). rewrite dfa_op_correct -negb_imply negbK.
    by move/implyP.
  - rewrite dfa_op_correct -negb_imply. apply/negbTE. rewrite negbK.
    apply/implyP. exact: H.
Qed.

End FA.

(** ** DFA for preimages of homomorphisms *)

Section Preimage.
  Variables (char char' : finType).

  Variable (h : word char -> word char').
  Hypothesis h_hom : homomorphism h.

  Definition dfa_preim (A : dfa char') : dfa char :=
  {| dfa_s := dfa_s A;
     dfa_fin := dfa_fin A;
     dfa_trans x a := delta x (h [:: a]) |}.

  Lemma dfa_preimP A : dfa_lang (dfa_preim A) =i preim h (dfa_lang A).
  Proof using h_hom.
    move => w. rewrite !inE /dfa_accept /dfa_preim /=.
    elim: w (dfa_s A) => [|a w IHw] x /= ; first by rewrite h0.
    by rewrite -[a :: w]cat1s h_hom !delta_cat -IHw.
  Qed.

End Preimage.

Lemma preim_regular (char char' : finType) (h : word char -> word char') L :
  homomorphism h -> regular L -> regular (preimage h L).
Proof.
  move => hom_h [A HA]. exists (dfa_preim h A) => w.
  by rewrite dfa_preimP // unfold_in /= -HA.
Qed.

(** ** Closure under Right Quotients *)

Section RightQuotient.
  Variables (char: finType) (L1 L2 : lang char).

  Definition quotR := fun x => exists2 y, L2 y & L1 (x++y).

  Variable (A : dfa char).
  Hypothesis acc_L1 : dfa_lang A =p L1.
  Hypothesis dec_L2 : forall (q:A), decidable (exists2 y, L2 y & delta q y \in dfa_fin A).

  (** It would be better to not make the DFA explicit and require
  decidabiliy of [(exists2 y, L2 y & L1 (x ++ y))] but that would
  require a connected DFA in order to define the final states via
  canonical words *)

  Definition dfa_quot :=
    {| dfa_s := dfa_s A;
       dfa_trans := @dfa_trans _ A;
       dfa_fin := [set q | dec_L2 q] |}.

  Lemma dfa_quotP x : reflect (quotR x) (x \in dfa_lang dfa_quot).
  Proof using acc_L1.
    apply: (iffP idP).
    - rewrite inE /dfa_accept inE. case/dec_eq => y inL2.
      rewrite -delta_cat => H. exists y => //. by rewrite -acc_L1.
    - case => y y1 y2. rewrite inE /dfa_accept inE /= dec_eq.
      exists y => //. by rewrite -delta_cat acc_L1.
  Qed.

End RightQuotient.

(** Useful special case of the right-quotient construction. Other
special cases would be where [L2] is context free, the case for
arbitrary [L2] is non-constructive. *)

Lemma regular_quotR (char : finType) (L1 L2 : lang char) :
  regular L1 -> regular L2 -> regular (quotR L1 L2).
Proof.
  move => [A LA] reg2.
  suff dec_L1 q : decidable (exists2 y, L2 y & delta q y \in dfa_fin A).
  { exists (dfa_quot dec_L1) => x. apply: (rwP (dfa_quotP _ _ _)) => {x} x. by rewrite LA. }
  case: reg2 => {LA} [B LB].
  pose C := {| dfa_s := q ; dfa_fin := dfa_fin A ; dfa_trans := @dfa_trans _ A |}.
  pose dec := dfa_inhab (dfa_op andb B C).
  apply: (dec_iff dec); split.
  - move => [x X1 X2]. exists x. rewrite dfa_op_correct. apply/andP;split => //. exact/LB.
  - move => [x]. rewrite dfa_op_correct. case/andP => *. exists x => //. exact/LB.
Qed.

(** ** Closure under Left Quotients *)


Section LeftQuotient.
  Variables (char: finType) (L1 L2 : lang char).

  Definition quotL := fun y => exists2 x, L1 x & L2 (x++y).

  Variable (A : dfa char).
  Hypothesis acc_L2 : L2 =p dfa_lang A.
  Hypothesis dec_L1 : forall (q:A), decidable (exists2 y, L1 y & delta_s A y = q).

  Let A_start q := {| dfa_s := q; dfa_fin := dfa_fin A; dfa_trans := @dfa_trans _ A |}.


  Lemma A_start_cat x y : (x ++ y \in dfa_lang A) = (y \in dfa_lang (A_start (delta_s A x))).
  Proof. rewrite inE /delta_s. elim: x (dfa_s A)=> //= a x IH q. by rewrite accE IH. Qed.

  Lemma regular_quotL_aux : regular quotL.
  Proof using acc_L2 dec_L1.
    pose S := [seq q | q <- enum A & dec_L1 q].
    pose L (q:A) := mem (dfa_lang (A_start q)).
    pose R x := exists2 a, a \in S & L a x.
    suff: quotL =p R.
    { apply: regular_ext. apply: regular_bigU => q qS. by exists (A_start q). }
    move => y; split.
    - case => x H1 /acc_L2 H2. exists (delta_s A x).
      + apply/mapP. exists (delta_s A x) => //. rewrite mem_filter mem_enum inE andbT.
        apply/dec_eq. by exists x.
      + by rewrite /L topredE -A_start_cat.
    - case => ? /mapP [q]. rewrite mem_filter mem_enum inE andbT => /dec_eq [x L1_x <- ->].
      rewrite /L topredE -A_start_cat => Hxy. exists x => //. exact/acc_L2.
  Qed.
End LeftQuotient.

Lemma regular_quotL (char: finType) (L1 L2 : lang char) :
  regular L1 -> regular L2 -> regular (quotL L1 L2).
Proof.
  move => [A acc_L1] [B acc_L2]. apply: regular_quotL_aux acc_L2 _ => q.
  pose B_q := {| dfa_s := dfa_s B; dfa_fin := [set q] ; dfa_trans := @dfa_trans _ B |}.
  have B_qP y : delta_s B y = q <-> y \in dfa_lang B_q.
  { rewrite -delta_lang inE. by split => ?; exact/eqP. }
  pose dec := dfa_inhab (dfa_op andb A B_q).
  apply: dec_iff dec _. split.
  - move => [y] H1 Hq. exists y. rewrite dfa_op_correct.
    apply/andP;split; first exact/acc_L1. exact/B_qP.
  - move => [y]. rewrite dfa_op_correct => /andP [H1 H2]. exists y; first exact/acc_L1.
    exact/B_qP.
Qed.

(** regular languages are logically determined and since propositions
    can be embedded into languages, there are some languages that are regular
    iff we assume excluded middle. (take [P] to be any independent proposition) *)

Lemma regular_det (char : finType) L (w : word char):
  inhabited (regular L) -> (L w) \/ (~ L w).
Proof. case. case => A ->. by case: (w \in dfa_lang A); [left|right]. Qed.

Lemma regular_xm (char : finType) :
  (forall P, inhabited (regular (fun _ : word char => P))) <-> (forall P, P \/ ~ P).
Proof.
  split => [H|H] P ; first exact: regular_det [::] (H P).
  case: (H P) => HP; constructor.
  + exists (dfa_compl (dfa_void char)) => x. by rewrite dfa_compl_correct dfa_void_correct.
  + exists (dfa_void char) => w. by rewrite /dfa_lang inE (negbTE (dfa_void_correct _ _)).
Qed.

(** ** Residual Criterion *)

Section NonRegular.
  Variables (char : finType) .

  Implicit Types (L : lang char).

  Definition residual L x := fun y => L (x ++ y).

  Lemma residualP (f : nat -> word char) (L : lang char) :
    (forall n1 n2, residual L (f n1) =p residual L (f n2) -> n1 = n2) ->
    ~ inhabited (regular L).
  Proof.
    move => f_spec [[A E]].
    pose f' (n : 'I_#|A|.+1) := delta_s A (f n).
    suff: injective f' by move/card_leq_inj ; rewrite card_ord ltnn.
    move => [n1 H1] [n2 H2]. rewrite /f' /delta_s /= => H.
    apply/eqP; change (n1 == n2); apply/eqP. apply: f_spec => w.
    by rewrite /residual !E !inE /dfa_accept !delta_cat H.
  Qed.

  Hypothesis (a b : char) (Hab : a != b).
  Local Set Default Proof Using "Hab".

  Definition Lab w := exists n, w = nseq n a ++ nseq n b.

  Lemma countL n1 n2 : count (pred1 a) (nseq n1 a ++ nseq n2 b) = n1.
  Proof.
    by rewrite count_cat !count_nseq /= eqxx eq_sym (negbTE Hab) mul1n mul0n addn0.
  Qed.

  Lemma countR n1 n2 : count (pred1 b) (nseq n1 a ++ nseq n2 b) = n2.
  Proof. by rewrite count_cat !count_nseq /= (negbTE Hab) eqxx //= mul1n mul0n. Qed.

  Lemma Lab_eq n1 n2 : Lab (nseq n1 a ++ nseq n2 b) -> n1 = n2.
  Proof.
    move => [n H].
    by rewrite -[n1](countL _ n2) -{2}[n2](countR n1 n2) H countL countR.
  Qed.

  Lemma Lab_not_regular : ~ inhabited (regular Lab).
  Proof.
    pose f n := nseq n a.
    apply: (@residualP f) => n1 n2. move/(_ (nseq n2 b)) => H.
    apply: Lab_eq. apply/H. by exists n2.
  Qed.

End NonRegular.

(** ** Pumping Lemma *)

Section Pumping.
  Definition sub (T:eqType) i j (s : seq T) := take (j-i) (drop i s).

  Definition rep (T : eqType) (s : seq T) n := iter n (cat s) [::].

  Variable char : finType.

  Lemma delta_rep (A : dfa char) (p : A) x i : delta p x = p -> delta p (rep x i) = p.
  Proof. elim: i => //= i IH H. by rewrite delta_cat H IH. Qed.

  Lemma pump_dfa (A : dfa char) x y z :
    x ++ y ++ z \in dfa_lang A -> #|A| < size y ->
    exists u v w,
      [/\ ~~ nilp v, y = u ++ v ++ w & forall i, (x ++ u ++ rep v i ++ w ++ z) \in dfa_lang A].
  Proof.
    rewrite -delta_lang => H1 H2.
    have/injectivePn : ~~ injectiveb (fun i : 'I_(size y) => delta (delta_s A x) (take i y)).
      apply: contraL H2 => /injectiveP/card_leq_inj. by rewrite leqNgt card_ord.
    move => [i] [j] ij fij.
    wlog {ij} ij : i j fij / i < j. rewrite neq_ltn in ij. case/orP : ij => ij W; exact: W _ ij.
    exists (take i y), (sub i j y), (drop j y). split => [||k].
    - apply: contraL ij.
      by rewrite /nilp size_take size_drop ltn_sub2r ?ltn_ord // subn_eq0 leqNgt.
    - by rewrite catA -takeD subnKC 1?ltnW // cat_take_drop.
    - rewrite inE /dfa_accept !delta_cat delta_rep.
      by rewrite fij -!delta_cat !catA -[(x ++ _) ++ _]catA cat_take_drop -!catA.
      rewrite -delta_cat -takeD subnKC //. exact: ltnW.
  Qed.

  Lemma pumping (L : word char -> Prop) :
    (forall k, exists x y z, k <= size y /\ L (x ++ y ++ z) /\
      (forall u v w, y = u ++ v ++ w -> ~~ nilp v ->
         exists i, L (x ++ u ++ rep v i ++ w ++ z) -> False))
     -> ~ inhabited (regular L).
  Proof.
    move => H [[A LA]].
    move/(_ #|A|.+1) : H => [x] [y] [z] [size_y [/LA Lxyz]].
    move: (pump_dfa Lxyz size_y) => [u] [v] [w] [Hn Hy Hv] /(_ u v w Hy Hn).
    move => [i]. apply. exact/LA.
  Qed.

  Lemma cat_nseq_eq n1 n2 (a : char) :
    nseq n1 a ++ nseq n2 a = nseq (n1+n2) a.
  Proof. elim: n1 => [|n1 IHn1] //=. by rewrite -cat1s IHn1. Qed.

  Example pump_Lab (a b : char) : a != b -> ~ inhabited (regular (Lab a b)).
  Proof.
    move => neq. apply: pumping => k.
    exists [::], (nseq k a), (nseq k b). repeat split.
    - by rewrite size_nseq.
    - by exists k.
    - move => u [|c v] w // /eqP e _. exists 0 => /= H.
      have Hk: k = size (u ++ (c::v) ++ w) by rewrite -[k](@size_nseq _ _ a) (eqP e).
      rewrite Hk !size_cat -!cat_nseq_eq !eqseq_cat ?size_nseq // in e.
      case/and3P : e => [/eqP Hu /eqP Hv /eqP Hw].
      rewrite -Hu -Hw catA cat_nseq_eq in H. move/(Lab_eq neq) : H.
      move/eqP. by rewrite Hk !size_cat eqn_add2l -{1}[size w]add0n eqn_add2r.
  Qed.

End Pumping.
