(* Authors Christian Doczkal and Jan-Oliver Kaiser *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import misc languages dfa regexp myhill_nerode.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Two Way Automata *)

(** ** Preliminaries

We want to represent configurations of two-way automata as pairs of states and
positions on the input word extended with left and right markers. That is
positions will be of type ['I_n.+2] with [n] being the length of the input
word. We need some facts about finite ordinals of this form.

We define a three-way case analysis on ['I_n.+2]. If [i:'I_n.+2] is
neither [ord0] nor [ord_max], then we can cast it (with offset 1) to
['I_n]. This is used for looking up charaters of an input word *)

Variant ord2_spec n (m : 'I_n.+2) :=
| Ord20 of m == ord0
| Ord2M of m == ord_max
| Ord2C (i : 'I_n) of i.+1 = m.

Arguments Ord20 [n m] _.
Arguments Ord2M [n m] _.
Arguments Ord2C [n m i] _.

Lemma ord2P n (m : 'I_n.+2) : ord2_spec m.
Proof.
  case: (unliftP ord0 m) => [j Hj|/eqP]; last exact: Ord20.
  case: (unliftP ord_max j) => [i Hi|Hj2]; last apply: Ord2M.
  * apply: (@Ord2C _ m i). by rewrite Hj Hi lift0 lift_max.
  * rewrite Hj Hj2. apply/eqP. apply/ord_inj. by rewrite lift0.
Qed.

Lemma ord2P0 n : ord2P (@ord0 n.+1) = Ord20 (eqxx _).
Proof. case: (ord2P (@ord0 n.+1)) => //= H. congr Ord20. exact: eq_irrelevance. Qed.

Lemma ord2PM n : ord2P (@ord_max n.+1) = Ord2M (eqxx _).
Proof.
  case: (ord2P (@ord_max n.+1)) => //= [H|i Hi].
  - apply: f_equal. exact: eq_irrelevance.
  - move: (ltn_ord i). move: (Hi) => Hi2. move: Hi => [] ->. by rewrite ltnn.
Qed.

Lemma ord2PC n {i : 'I_n.+2} {i' : 'I_n} (p : i'.+1 = i) : ord2P i = Ord2C p.
Proof.
  case: (ord2P i) => [Hi|Hi|j' p'].
  - exfalso. move/eqP: Hi => Hi. by rewrite Hi in p.
  - exfalso. move:Hi. apply/negP. apply: contra_eqN p => /eqP->.
    rewrite eqn_leq negb_and -[~~ (ord_max <= _)]ltnNge [_.+1 < _](_ : _ = true) ?orbT //.
    exact: leq_ltn_trans (ltn_ord _) _.
  - have ?: i' = j'. apply: ord_inj. apply/eqP. by rewrite -eqSS p p'. subst.
    by rewrite (eq_irrelevance p p').
Qed.

(** ** Definition of 2NFAs and their languages.

We need to call 2NFAs [nfa2] since names may not begin with numbers. *)

Section NFA2.
  Variable char : finType.

  Definition dir := bool.
  Definition L := true.
  Definition R := false.

  Record nfa2 := Nfa2 {
    nfa2_state :> finType;
    nfa2_s : nfa2_state;
    nfa2_f : {set nfa2_state};
    nfa2_trans : nfa2_state -> char -> {set nfa2_state * dir};
    nfa2_transL : nfa2_state -> {set nfa2_state};
    nfa2_transR : nfa2_state -> {set nfa2_state}}.

  Variables (A : nfa2) (x : word char).

  Definition tape := in_tuple x.
  Definition pos := ('I_(size x).+2)%type.
  Definition nfa2_config := (A * pos)%type.

  Definition read (q:A) (n : pos) : {set (A * dir)} :=
    match ord2P n with
      | Ord20 _ => setX (nfa2_transL q) [set R]
      | Ord2M _ => setX (nfa2_transR q) [set L]
      | Ord2C m' _ => nfa2_trans q (tnth tape m')
    end.

  Definition step (c d : nfa2_config) :=
    let: ((p,i),(q,j)) := (c,d) in
        ((q,R) \in read p i) && (j == i.+1 :> nat)
     || ((q,L) \in read p i) && (j.+1 == i :> nat).

  Definition nfa2_lang := [exists (q | q \in nfa2_f A), connect step (nfa2_s A,ord1) (q,ord_max)].
End NFA2.

Arguments step [char] A x c d.
Prenex  Implicits step.


(** ** Definition of 2DFAs as deterministic 2NFAs *)

Section DFA2.
  Variable char : finType.

  Record deterministic (M : nfa2 char) : Prop :=
  { detC : forall (p:M) a, #|nfa2_trans p a| <= 1;
    detL : forall (p:M), #|nfa2_transL p| <= 1;
    detR : forall (p:M), #|nfa2_transR p| <= 1}.

  Record dfa2 := DFA2 { nfa2_of :> nfa2 char ; dfa2_det : deterministic nfa2_of }.
  Definition dfa2_lang := nfa2_lang.

  Variable M : dfa2.

  Lemma cards_lt1 (T : finType) (A : {set T}) : #|A| <= 1 -> A = set0 \/ exists x, A = [set x].
  Proof.
    move => H. case (posnP #|A|) => H'.
    - left. exact:cards0_eq.
    - right. apply/cards1P. by rewrite eqn_leq H H'.
  Qed.

  Lemma read1 x (p:M) (j:pos x) : read p j = set0 \/ exists s : M * dir, read p j = [set s].
  Proof.
    rewrite /read.
    case: (ord2P _) => [||i] _;apply cards_lt1; rewrite ?cardsX ?cards1 ?muln1;
      by auto using detL, detC, detR, dfa2_det.
  Qed.

  Lemma step_fun x : functional (step M x).
  Proof.
    have lr: ((R == L = false)*(L == R = false))%type by done.
    move => [p i] [q j] [r k]. rewrite /step.
    case: (read1 p i) => [ -> |[[q' [|]] -> ]]; first by rewrite !inE.
    - rewrite !inE !xpair_eqE -/L -/R !lr !eqxx !andbT !andbF /=.
      move => /andP [/eqP -> /eqP A] /andP [/eqP -> /eqP B].
      f_equal. apply ord_inj. apply/eqP. by rewrite -eqSS A B.
    - rewrite !inE !xpair_eqE -/L -/R !lr !eqxx !andbT !andbF !orbF /=.
      move => /andP [/eqP -> /eqP A] /andP [/eqP -> /eqP B].
      f_equal. apply ord_inj. apply/eqP. by rewrite -eqSS A B.
  Qed.

End DFA2.

(** ** Simulation of DFAs *)



Section DFAtoDFA2.
  Variables (char : finType) (A : dfa char).

  Definition nfa2_of_dfa : nfa2 char :=
    {| nfa2_s := dfa_s A;
       nfa2_f := [set q in dfa_fin A];
       nfa2_trans q a := [set (dfa_trans q a,R)];
       nfa2_transL q := [set dfa_s A]; (* Never reached *)
       nfa2_transR q := set0
     |}.

  Lemma drop_accept (w : word char) (i : 'I_(size w)) (q : A) :
    drop i w \in dfa_accept q = (drop i.+1 w \in dfa_accept (dfa_trans q (tnth (tape w) i))).
  Proof.
    case: w i q => [[//]|a w [m Hm] q]. rewrite [drop]lock (tnth_nth a) /= -lock.
    elim: {w} (a :: w) m Hm q => [|b w IHw [|m] Hm q]; first by case.
    by rewrite drop0 drop1. exact: IHw.
  Qed.

  Variable (w : word char).
  Let n := size w.

  Lemma nfa2_of_aux (q:A) i : i < (size w).+1 ->
      ((drop i w) \in dfa_accept q) ->
      [exists f in nfa2_f nfa2_of_dfa, connect (step nfa2_of_dfa w) (q,inord i.+1) (f,ord_max)].
  Proof.
    move eq_m : (n - i) => m. elim: m q i eq_m => [|m IHm] q i /eqP H1 H2.
    - have/eqP -> : i == (size w). by rewrite eqn_leq -ltnS H2 -subn_eq0 H1.
      rewrite drop_size unfold_in -inord_max /= => F. apply/existsP;exists q. rewrite inE F. exact: connect0.
    - move => H. have Hi : i < size w.
      { rewrite ltn_neqAle -ltnS H2 andbT. apply: contraTN H1 => /eqP->. by rewrite subnn. }
      have Hm : n - i.+1 = m by apply/eqP;rewrite subnS (eqP H1).
      move/(_ (dfa_trans q (tnth (tape w) (Ordinal Hi))) _ Hm Hi) : IHm.
      rewrite -[i.+1]/(Ordinal Hi).+1 -drop_accept. move => /(_ H).
      case/exists_inP => f f1 f2. apply/exists_inP;exists f => //. apply: connect_trans (connect1 _) f2.
      rewrite /step /read (ord2PC (i' := (Ordinal Hi))) ?inordK //= => _.
      by rewrite inE ?eqxx.
  Qed.

  Lemma nfa2_of_aux2 (q f:A) (i : pos w) : i != ord0 ->
    f \in nfa2_f nfa2_of_dfa -> connect (step nfa2_of_dfa w) (q,i) (f,ord_max) ->
    ((drop i.-1 w) \in dfa_accept q).
  Proof.
    move => H fin_f. case/connectP => p. elim: p i H q => //= [|[q' j] p IHp i Hi q].
    - move => i Hi q _ [<- <-]. rewrite drop_size -topredE /= accept_nil. by rewrite inE in fin_f.
    - rewrite {1}/step /read. case: (ord2P i) => /= [|/eqP->|i' Hi']; try by rewrite ?inE ?(negbTE Hi).
      rewrite !inE !xpair_eqE (_ : L == R = false) ?eqxx ?andbT ?andbF ?orbF -?andbA //=.
      case/and3P => /eqP -> /eqP E. rewrite -Hi' drop_accept.
      have -> : i'.+1 = j.-1 by rewrite E. apply IHp.
      by apply: contra_eq_neq E =>->.
  Qed.

  Lemma nfa2_of_correct : (w \in dfa_lang A) = (w \in nfa2_lang nfa2_of_dfa).
  Proof.
    apply/idP/idP; rewrite -![_ \in _ A]topredE /=.
    - rewrite -{1}[w]drop0 /nfa2_lang -topredE /= inord1 => H. exact: nfa2_of_aux.
    - rewrite -{2}[w]drop0 -[0]/((@ord1 n).-1). case/exists_inP => p. exact: nfa2_of_aux2.
  Qed.

  Lemma nfa2_of_dfa_det : deterministic (nfa2_of_dfa).
  Proof. split => [p a|p|p]; by rewrite ?cards1 ?cards0. Qed.

  Definition dfa2_of_dfa := DFA2 nfa2_of_dfa_det.

  Lemma dfa2_of_correct : (w \in dfa_lang A) = (w \in dfa2_lang dfa2_of_dfa).
  Proof. exact: nfa2_of_correct. Qed.

End DFAtoDFA2.
