(* Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import misc languages dfa.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.

Section NFA.
Variable char : finType.
#[local] Notation word := (word char).

(** * Nondeterministic Finite Automata.

We define both normal NFAs and NFAs with epsilon transitions
(eNFAs). For NFAs acceptance can still be defined by structural
recursion on the word. In particular, the length of an NFA run is
determined by the input word, a property that we exploit repeatedly. *)

Record nfa : Type := {
    nfa_state :> finType;
    nfa_s : { set nfa_state };
    nfa_fin : { set nfa_state };
    nfa_trans : nfa_state -> char -> nfa_state -> bool }.

Fixpoint nfa_accept (A : nfa) (x : A) w :=
  if w is a :: w' then [exists (y | nfa_trans x a y), nfa_accept y w']
                  else x \in nfa_fin A.

Definition nfa_lang (A : nfa) := [pred w | [exists s, (s \in nfa_s A) && nfa_accept s w]].

(** ** Epsilon NFAs *)

Record enfa : Type := {
  enfa_state :> finType;
  enfa_s : {set enfa_state};
  enfa_f : {set enfa_state};
  enfa_trans : option char -> enfa_state -> enfa_state -> bool }.

Section EpsilonNFA.
  Variables (N : enfa).

  (** For eNFAs, acceptance is defined relationally since structural
  recursion over the word is no longer possible. *)

  Inductive enfa_accept : N -> word -> Prop :=
    | EnfaFin q : q \in enfa_f N -> enfa_accept q [::]
    | EnfaSome p a q x : enfa_trans (Some a) p q -> enfa_accept q x -> enfa_accept p (a::x)
    | EnfaNone p q x : enfa_trans None p q -> enfa_accept q x -> enfa_accept p (x).

  Definition enfa_lang x := exists2 s, s \in enfa_s N & enfa_accept s x.

  (** We convert eNFAs to NFAs by extending the set of starting states and all
  transitions by epsilon-reachable states - also known as epsilon closure *)

  Definition eps_reach (p : N) := [set q | connect (enfa_trans None) p q].

  Lemma lift_accept p q x : q \in eps_reach p -> enfa_accept q x -> enfa_accept p x.
  Proof.
    rewrite inE => /connectP [s]. elim: s p x q => //= [p x q _ -> //| q s IHs p x q'].
    case/andP => pq ? ? H. apply: EnfaNone pq _. exact: IHs H.
  Qed.

  Definition nfa_of :=
    {| nfa_s := \bigcup_(p in enfa_s N) (eps_reach p);
       nfa_fin := enfa_f N;
       nfa_trans p a q := [exists p', enfa_trans (Some a) p p' && (q \in eps_reach p') ] |}.

  Lemma enfaE x p :
    (enfa_accept p x) <-> (exists2 q : nfa_of, q \in eps_reach p & nfa_accept q x).
  Proof. split.
    - elim => {p x} [q H|p a q x H _ [q' Hq1 Hq2]|p p' x].
      + exists q => //. by rewrite inE connect0.
      + exists p => /=; first by rewrite inE connect0.
        apply/exists_inP. exists q' => //. apply/exists_inP. by exists q.
      + move => H1 H2 [q Hq1 Hq2]. exists q => //. rewrite !inE in Hq1 *.
        exact: connect_trans (connect1 _) Hq1.
    - elim: x p => [|a x IH] p [p'] R /= H. apply: lift_accept R _. exact: EnfaFin.
      case/exists_inP : H => q /exists_inP [q' pq' qq'] H. apply: lift_accept R _.
      apply: EnfaSome pq' _. apply: IH. by exists q.
  Qed.

  Lemma nfa_ofP x : reflect (enfa_lang x) (x \in nfa_lang nfa_of).
  Proof.
    apply: (iffP exists_inP) => [[p Hp1 Hp2]|[s Hs1 /enfaE [p Hp1 Hp2]]].
    - case/bigcupP : Hp1 => s Hs H. exists s => //. by apply/enfaE; exists p.
    - exists p => //. by apply/bigcupP; exists s.
  Qed.
End EpsilonNFA.

(** ** Equivalence of DFAs and NFAs *)
(** We use the powerset construction to obtain
   a deterministic automaton from a non-deterministic one. **)
Section PowersetConstruction.

Variable A : nfa.

Definition nfa_to_dfa := {|
  dfa_s := nfa_s A;
  dfa_fin := [set X | X :&: nfa_fin A != set0];
  dfa_trans X a := [set q | [exists (p | p \in X), nfa_trans p a q]]
|}.

Lemma nfa_to_dfa_correct : nfa_lang A =i dfa_lang nfa_to_dfa.
Proof.
  move => w. rewrite !inE {2}/nfa_to_dfa /=.
  elim: w (nfa_s _) => [|a x IH] X; rewrite /= accE ?inE.
  - apply/existsP/set0Pn => [] [p] H; exists p; by rewrite inE in H *.
  - rewrite -IH /dfa_trans /=. apply/exists_inP/exists_inP.
    + case => p inX /exists_inP [q ? ?]. exists q => //. rewrite inE.
      apply/exists_inP. by exists p.
    + case => p. rewrite inE => /exists_inP [q] ? ? ?.
      exists q => //. apply/exists_inP. by exists p.
Qed.

End PowersetConstruction.

(** We also embed NFAs into DFAs. **)

Section Embed.

Variable A : dfa char.

Definition dfa_to_nfa : nfa := {|
  nfa_s := [set dfa_s A];
  nfa_fin := dfa_fin A;
  nfa_trans x a y := dfa_trans x a == y |}.

Lemma dfa_to_nfa_correct : dfa_lang A =i nfa_lang dfa_to_nfa.
Proof.
  move => w. rewrite !inE /nfa_s /=.
  elim: w (dfa_s A) => [|b w IHw] x; rewrite accE /=.
  - apply/idP/existsP => [Fx|[y /andP [/set1P ->]]//].
    exists x. by rewrite !inE eqxx.
  - rewrite IHw. apply/exists_inP/exists_inP.
    + case => y /set1P -> H. exists x; first exact: set11.
      apply/existsP. exists (dfa_trans x b). by rewrite H eqxx.
    + case => y /set1P -> {y} /existsP [z] /andP [] /eqP-> H.
      exists z; by rewrite ?set11.
Qed.

End Embed.

(** ** Operations on NFAs

To prepare the translation from regular expresstions to DFAs, we show
that finite automata are closed under all regular operations. We build
the primitive automata, complement and boolean combinations using
DFAs. *)

Definition nfa_char (a:char) :=
  {| nfa_s := [set false];
     nfa_fin := [set true];
     nfa_trans p b q := if (p,q) is (false,true) then (b == a) else false |}.

Lemma nfa_char_correct (a : char) : nfa_lang (nfa_char a) =1 pred1 [:: a].
Proof.
  move => w /=. apply/exists_inP/eqP => [[p]|].
  - rewrite inE => /eqP->. case: w => [|b [|c w]] /=; first by rewrite inE.
    + by case/exists_inP => [[/eqP->|//]].
    + case/exists_inP => [[_|//]]. by case/exists_inP.
  - move->. exists false; first by rewrite inE. apply/exists_inP.
    exists true; by rewrite ?inE //=.
Qed.

Definition nfa_plus (N M : nfa) :=
  {| nfa_s := [set q | match q with inl q => q \in nfa_s N | inr q => q \in nfa_s M end ];
     nfa_fin := [set q | match q with inl q => q \in nfa_fin N | inr q => q \in nfa_fin M end ];
     nfa_trans p a q := match p,a,q with
                         | inl p,a,inl q => nfa_trans p a q
                         | inr p,a,inr q => nfa_trans p a q
                         | _,_,_ => false
                         end |}.

Lemma nfa_plus_correct (N M : nfa) :
  nfa_lang (nfa_plus N M) =i plus (nfa_lang N) (nfa_lang M).
Proof.
  move => w. apply/idP/idP.
  - case/exists_inP => [[s|s]]; rewrite !inE => A B;
    apply/orP;[left|right];apply/exists_inP; exists s => //.
    + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
      case/exists_inP => [[|]// p A /IH B]. apply/exists_inP. by exists p.
    + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
      case/exists_inP => [[|]// p A /IH B]. apply/exists_inP. by exists p.
  - rewrite !inE. case/orP => /exists_inP [s A B];
    apply/exists_inP; [exists(inl s)|exists(inr s)]; rewrite ?inE //.
    + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
      case/exists_inP => [p A /IH B]. apply/exists_inP. by exists (inl p).
    + elim: w s {A} B => /= [|a w IH] s; first by rewrite inE.
      case/exists_inP => [p A /IH B]. apply/exists_inP. by exists (inr p).
Qed.

Definition nfa_eps : nfa :=
  {| nfa_s := [set tt]; nfa_fin := [set tt]; nfa_trans p a q := false |}.

Lemma nfa_eps_correct: nfa_lang (nfa_eps) =i pred1 [::].
Proof.
  move => w. apply/exists_inP/idP.
  + move => [[]]. case: w => [|a w] //= _. by case/exists_inP.
  + move => /=. rewrite inE=>/eqP->. exists tt; by rewrite /= inE.
Qed.

(** The automata for concatenation and Kleene star are constructed by
taking NFAs as input and first building eNFAs which are then converted
to NFAs. *)

Section eNFAOps.

Variables A1 A2 : nfa.

Definition enfa_conc : enfa :=
  {| enfa_s := inl @: nfa_s A1;
     enfa_f := inr @: nfa_fin A2;
     enfa_trans c p q :=
       match c,p,q with
         | Some a,inl p',inl q' => nfa_trans p' a q'
         | Some a,inr p',inr q' => nfa_trans p' a q'
         | None,inl p', inr q' => (p' \in nfa_fin A1) && (q' \in nfa_s A2)
         | _,_,_ => false
       end |}.

Lemma enfa_concE (p : enfa_conc) x : enfa_accept p x ->
  match p with
    | inr p' => nfa_accept p' x
    | inl p' => exists x1 x2, [/\ x = x1 ++ x2, nfa_accept p' x1 & x2 \in nfa_lang A2]
  end.
Proof.
  elim => {p x} [[?|?] /imsetP [q] // ? [->] //||].
  - move => [p|p] a [q|q] x //.
    + move => pq _ [x1] [x2] [X1 X2 X3]. exists (a::x1); exists x2; subst; split => //.
      by apply/exists_inP; exists q.
    + move => pq _ Hq. by apply/exists_inP; exists q.
  - move => [p|p] [q|q] //= x /andP[Hp Hq] _ ?. exists [::]; exists x; split => //.
    by apply/exists_inP; exists q.
Qed.

Lemma enfa_concIr (p : A2) x : nfa_accept p x -> @enfa_accept enfa_conc (inr p) x.
Proof.
  elim: x p => [p Hp|a x IH p /= /exists_inP [q q1 q2]].
  - (* compat: <mathcomp-1.12 *)
    constructor; solve [exact: imset_f|exact:mem_imset].
  - apply: (@EnfaSome enfa_conc _ _ (inr q)) => //. exact: IH.
Qed.

Lemma enfa_concIl (p : A1) x1 x2 :
  nfa_accept p x1 -> x2 \in nfa_lang A2 -> @enfa_accept enfa_conc (inl p) (x1++x2).
Proof.
  elim: x1 p => /= [p Hp /exists_inP [q q1 q2]|a x1 IH p /exists_inP [q q1 q2] H].
  - apply: (@EnfaNone enfa_conc _ (inr q)). by rewrite /= Hp. exact: enfa_concIr.
  - apply: (@EnfaSome enfa_conc _ _ (inl q)). by rewrite /= q1. exact: IH.
Qed.

Lemma enfa_concP x : reflect (enfa_lang enfa_conc x) (conc (nfa_lang A1) (nfa_lang A2) x).
Proof.
  apply: (iffP (@concP _ _ _ _)) => [[x1] [x2] [X1 [X2 X3]] |].
  - (* compat: <mathcomp-1.12 *)
    case/exists_inP : X2 => s ? ?. exists (inl s); first solve [exact: imset_f|exact:mem_imset].
    subst. exact: enfa_concIl.
  - move => [[s /imsetP [? ? [?]] /enfa_concE [x1] [x2] [? ? ?] |s]]; last by case/imsetP.
    exists x1; exists x2. repeat (split => //). apply/exists_inP. by exists s;subst.
Qed.

Definition enfa_star : enfa :=
  {| enfa_s := [set None];
     enfa_f := [set None];
     enfa_trans c p q :=
       match c,p,q with
           Some a,Some p', Some q' => q' \in nfa_trans p' a
         | None, Some p', None => p' \in nfa_fin A1
         | None, None, Some s => s \in nfa_s A1
         | _,_,_ => false
       end |}.

Lemma enfa_s_None : None \in enfa_s enfa_star.
Proof. by rewrite inE. Qed.

Lemma enfa_f_None : None \in enfa_f enfa_star.
Proof. by rewrite inE. Qed.

#[local] Hint Resolve enfa_s_None enfa_f_None : core.

Lemma enfa_star_cat x1 x2 (p : enfa_star) :
  enfa_accept p x1 -> enfa_lang enfa_star x2 -> enfa_accept p (x1 ++ x2).
Proof.
  elim => {p x1}.
  - move => p. rewrite inE => /eqP->. case => q. by rewrite inE => /eqP->.
  - move => p a q x /=. case: p => // p. case: q => // q pq ? IH H. exact: EnfaSome (IH H).
  - move => [p|] [q|] x //= p1 p2 IH H; exact: EnfaNone (IH H).
Qed.

Lemma enfa_starI x (p : A1) : nfa_accept p x -> @enfa_accept enfa_star (Some p) x.
Proof.
  elim: x p => /= [p H|a x IH p].
  - apply: (@EnfaNone enfa_star _ None) => //. exact: EnfaFin.
  - case/exists_inP => q q1 /IH. exact: EnfaSome.
Qed.

Lemma enfa_star_langI x : x \in nfa_lang A1 -> @enfa_accept enfa_star None x.
Proof.
  case/exists_inP => s s1 s2.
  apply: (@EnfaNone enfa_star _ (Some s)) => //. exact: enfa_starI.
Qed.

Lemma enfa_starE (o : enfa_star) x : enfa_accept o x ->
  if o is Some p
  then exists x1 x2, [/\ x = x1 ++ x2, nfa_accept p x1 & star (nfa_lang A1) x2]
  else star (nfa_lang A1) x.
Proof.
  elim => {x o}.
  - move => [q|//]. by rewrite inE; move/eqP.
  - move => [p|] a [q|] x // H acc [x1] [x2] [H1 H2 H3]. exists (a::x1); exists x2.
    rewrite H1. split => //. by apply/exists_inP; exists q.
  - move => [p|] [q|] x //=.
    + move => *. by exists [::]; exists x.
    + move => H acc [x1] [x2] [H1 H2]. rewrite H1. apply: star_cat.
      by apply/exists_inP; exists q.
Qed.

Lemma enfa_starP x : reflect (enfa_lang enfa_star x) (star (nfa_lang A1) x).
Proof. apply: (iffP idP).
  - case/starP => vv H ->. elim: vv H => /= [_|v vv].
    + exists None => //. exact: EnfaFin.
    + move => IH /andP[/andP [H1 H2] H3]. exists None => //.
      apply: enfa_star_cat (IH _) => //. exact: enfa_star_langI.
  - case => q. rewrite inE => /eqP-> {q}. exact: enfa_starE.
Qed.


Definition nfa_conc := nfa_of (enfa_conc).

Lemma nfa_conc_correct : nfa_lang nfa_conc =i conc (nfa_lang A1) (nfa_lang A2).
Proof. move => x. apply/nfa_ofP/idP => ?;exact/enfa_concP. Qed.

Definition nfa_star := nfa_of (enfa_star).
Lemma nfa_star_correct : nfa_lang nfa_star =i star (nfa_lang A1).
Proof. move => x. apply/nfa_ofP/idP => ?;exact/enfa_starP. Qed.

End eNFAOps.

(** ** Runs on NFAs *)

Section NFARun.
  Variable (M : nfa).

  Inductive nfa_run : word -> M -> seq M -> Prop :=
    | run0 p of p \in nfa_fin M : nfa_run [::] p [::]
    | runS a p q x r & q \in nfa_trans p a : nfa_run x q r -> nfa_run (a::x) p (q::r).

  Lemma nfa_acceptP x p : reflect (exists r, nfa_run x p r) (nfa_accept p x).
  Proof.
    apply: (iffP idP) => [|[r]].
    - elim: x p => [|a x IHx] p /=; first by exists [::]; constructor.
      case/exists_inP => q p1 p2. case (IHx q p2) => r ?. by exists (q::r); constructor.
    - elim: x r p => [|a x IHx] r p; first by inversion 1; subst.
      inversion 1; subst. apply/exists_inP. exists q => //. exact: IHx H4.
  Qed.

  Lemma run_size x r p : nfa_run x p r -> size x = size r.
  Proof. by elim => // {r p x} a p q r x _ _ /= ->. Qed.

  Lemma nfaP x : reflect (exists s r, s \in nfa_s M /\ nfa_run x s r) (x \in nfa_lang M).
  Proof.
    apply: (iffP exists_inP).
    - case => s ? /nfa_acceptP [r] ?. by exists s; exists r.
    - case => s [r] [? ?]. exists s => //. apply/nfa_acceptP. by exists r.
  Qed.

  Lemma run_last x p r : nfa_run x p r -> last p r \in nfa_fin M.
  Proof. by elim. Qed.

  Lemma run_trans x p r i (Hi : i < size x) : nfa_run x p r ->
    nth p (p::r) i.+1 \in nfa_trans (nth p (p::r) i) (tnth (in_tuple x) (Ordinal Hi)).
  Proof.
    move => H. elim: H i Hi => {x p r} // a p q x r tr run IH /= [|i] Hi //.
    rewrite !(set_nth_default q); try by rewrite /= -(run_size run) // ltnW.
    rewrite {1}[nth]lock (tnth_nth a) /=. rewrite ltnS in Hi.
    rewrite -{3}[i]/(nat_of_ord (Ordinal Hi)).
    by rewrite -[x]/(tval (in_tuple x)) -tnth_nth -lock IH.
  Qed.

  (** The following lemma uses [in_tuple] and [tnth] in order to avoid
  having to assume the existence of a default symbol *)

  Lemma runI x s r :
    size r = size x -> last s r \in nfa_fin M ->
    (forall i : 'I_(size x),
       nth s (s::r) i.+1 \in nfa_trans (nth s (s::r) i) (tnth (in_tuple x) i)) ->
    nfa_run x s r.
  Proof.
    elim: x s r => [|a x IHx ] s r /=.
    - move/eqP => e inF _. rewrite size_eq0 in e. rewrite (eqP e) in inF *. exact: run0.
    - case: r => // p r /eqP /=. rewrite eqSS => /eqP R1 R2 I.
      apply: runS (I ord0) _ => /=. apply: IHx => // i.
      move: (I (inord i.+1)). rewrite /tnth /= !inordK /= ?ltnS //.
      rewrite !(set_nth_default p) /= ?R1 // 1?ltnW ?ltnS //.
      by rewrite -[x]/(val (in_tuple x)) -!tnth_nth.
  Qed.

End NFARun.

(** Decidability of Language Emptiness *)

Definition nfa_inhab (N : nfa) := dfa_inhab (nfa_to_dfa N).

Lemma nfa_inhabP N : reflect (exists w, w \in nfa_lang N) (nfa_inhab N).
Proof.
  apply: (iffP (dfa_inhabP _)).
  - move => [x]. rewrite -nfa_to_dfa_correct. by exists x.
  - move => [x ?]. exists x. by rewrite -nfa_to_dfa_correct.
Qed.

Lemma nfa_regular L :
  regular L <-T->  { N : nfa  | forall x, L x <-> x \in nfa_lang N }.
Proof.
  split => [[A]|[N]] H.
  exists (dfa_to_nfa A) => x. by rewrite -dfa_to_nfa_correct.
  exists (nfa_to_dfa N) => x. by rewrite -nfa_to_dfa_correct.
Qed.

End NFA.

Arguments nfaP {char M x}.
