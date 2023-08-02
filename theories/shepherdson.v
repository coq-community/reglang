(* Author: Christian Doczkal  *)
(* Distributed under the terms of CeCILL-B. *)
From Coq Require Import Lia.
From mathcomp Require Import all_ssreflect.
From RegLang Require Import misc setoid_leq languages dfa myhill_nerode two_way.

Set Default Proof Using "Type".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shepherdson Construction for 2NFAs *)

(** Preliminaries *)

Lemma contraN (b : bool) (P : Prop) : b -> ~~ b -> P. Proof. by case b. Qed.

Lemma inord_inj n m : n <= m -> injective (@inord m \o @nat_of_ord n.+1).
Proof.
  move => Hnm k k' /= /(f_equal (@nat_of_ord _)) E. apply/ord_inj.
  rewrite !inordK // in E; exact: leq_trans (ltn_ord _) _.
Qed.

(** Lemmas for character lookups on composite words *)

Lemma tnthL (T:eqType) (x z : seq T) (i : 'I_(size x)) (j : 'I_(size (x++z))) :
  i = j :> nat -> tnth (in_tuple x) i = tnth (in_tuple (x++z)) j.
Proof.
  move => e. pose a := tnth (in_tuple x) i.
  by rewrite !(tnth_nth a) /= -e nth_cat ltn_ord.
Qed.

Lemma tnthR (T:eqType) (x z : seq T) (i : 'I_(size z)) (j : 'I_(size (x++z))) :
  size x + i = j -> tnth (in_tuple z) i = tnth (in_tuple (x++z)) j.
Proof.
  move => e. pose a := tnth (in_tuple z) i.
  by rewrite !(tnth_nth a) /= -e nth_cat ltnNge leq_addr /= addKn.
Qed.

(** Wrapper for [lia] that uses ssreflects operators on [nat] *)

Ltac norm := rewrite ?(size_cat,cats0); simpl in *.
Ltac normH := match goal with [ H : is_true (_ <= _) |- _] => move/leP : H end.
Ltac ssrlia :=
  try (try (apply/andP; split); apply/leP; repeat normH; norm ; rewrite ?addnE /addn_rec ; intros; lia).

Section NFA2toAFA.

  Variables (char : finType) (M : nfa2 char).
  Implicit Types (x y z w v : word char).

  (** We fix some 2NFA [M]. Instead of directly defining a DFA for [M], we
  instantiate the construction of DFAs from classifiers. This means that we have
  to give a finite type [Q] and define a function [T : word char -> Q] which is
  right congruent and refines the language of [M]. We take [Q] to be the type of
  tables or black-box results for [M]. *)

  Definition table := ({set M} * {set M * M})%type.

  (** We define the mapping from [word char] to [table] using a restriction of the
  step relation. The stop relation [srel k x] behaves like [step x] except that
  it does not continue if the head is at position [k]. *)

  Definition srel (k:nat) x (c d : nfa2_config M x) := (step M x c d) && (k != c.2).
  Arguments srel : clear implicits.

  Lemma srel_step k w : subrel (srel k w) (step M w).
  Proof. by move => c d /= => /andP[->]. Qed.

  Lemma srel_step_max x : srel (size x).+2 x =2 step M x.
  Proof. move => c d /=. by rewrite /srel neq_ltn ltn_ord orbT andbT. Qed.

  Definition Tab x : table :=
    ([set q | connect (srel (size x).+1 x) (nfa2_s M, ord1) (q,ord_max)],
     [set pq | connect (srel (size x).+1 x) (pq.1,inord (size x)) (pq.2,ord_max)]).

  (** To show that [Tab] is right-congruent and refines the language of [M], we
  need to make use of the fact that [M] moves its head only one step at a
  time. In particular, this allows us to split runs starting with head position
  [i] and ending at head position [j] at any position [k] in beteen. *)

  Lemma srelLR k x p i q j : srel k x (p,i) (q,j) ->
    j.+1 = i :> nat \/ j = i.+1 :> nat.
  Proof. case/srel_step/orP => /andP [_ /eqP ->]; tauto. Qed.

  Lemma srel1 k x c d : srel k x c d -> d.2 <= c.2.+1.
  Proof. move: c d => [p i] [q j] /srelLR [<-|->] //=. by ssrlia. Qed.

  Lemma srelSr k' k x (c d : nfa2_config M x) : c.2 < k ->
    srel k x c d = srel (k+k') x c d.
  Proof. move => lt_k. by rewrite /srel !neq_ltn ltn_addr lt_k ?orbT. Qed.

  Lemma srelS k x p q (i j : pos x) m : i <= k ->
     connect (srel k x) (p,i) (q,j) -> connect (srel (k+m) x) (p,i) (q,j).
  Proof.
    move => H /connectP [cs].
    elim: cs p i H => [/= p i H _ [-> ->] //|[p' i'] cs IH p i H /= /andP [s pth] l].
    have Hk: i < k. case/andP : s => _ /= s. by rewrite ltn_neqAle H eq_sym s.
    apply: (connect_trans (y := (p',i'))) (connect1 _) _; first by rewrite -srelSr.
    apply: IH => //. move/srel1 : s Hk => /= s. exact: leq_trans.
  Qed.

  Lemma srel_mid_path (k k' : nat) x (i j : pos x) (p q : M) cs :
    i <= k <= j -> path (srel k' x) (p,i) cs -> (q,j) = last (p,i) cs ->
    exists p' cl cr, [/\ cs = cl ++ cr, (p',inord k) = last (p,i) cl & path (srel k x) (p,i) cl].
  Proof.
    move: cs p i. apply: (size_induction (measure := size)) => cs IH p i /andP [H1 H2].
    case: (boolP (i == k :> nat)) => Ei.
    - exists p, [::], cs. by rewrite -[i]inord_val (eqP Ei).
    - destruct cs as [|c cs] => [_ /= [_ E]|/= /andP [s p1] p2]; subst.
      + by rewrite eqn_leq H1 H2 in Ei.
      + have Hi: i < k by rewrite ltn_neqAle Ei H1.
        have mid: c.2 <= k <= j by rewrite (leq_trans (srel1 s)).
        case: (IH cs _ c.1 _ mid) ; rewrite -?surjective_pairing //.
        move => p' [cl] [cr] [C1 C2 C3]. exists p', (c::cl), cr.
        rewrite /= -C1 C3 andbT. split => //. rewrite /srel /= eq_sym Ei andbT.
        exact: srel_step s.
  Qed.

  Lemma srel_mid (k k' : nat) x (i j : pos x) (p q : M) : i <= k <= j -> k <= k' ->
    reflect (exists2 p', connect (srel k x) (p,i) (p',inord k) & connect (srel k' x) (p',inord k) (q,j))
            (connect (srel k' x) (p,i) (q,j)).
  Proof.
    move => H X. apply: (iffP idP).
    - case/connectP => cs c1 c2. case: (srel_mid_path H c1 c2) => [p'] [cl] [cr] [Ecs L C].
      subst cs. rewrite cat_path last_cat -L in c1 c2. case/andP : c1 => ? c1. exists p'.
      + apply/connectP. by exists cl.
      + apply/connectP. by exists cr.
    - case/andP: H => H1 H2 [p']. move/(srelS (k'-k) H1). rewrite subnKC //. exact: connect_trans.
  Qed.

  Lemma readL x z (p:M) (k : pos x) : k != (size x).+1 :> nat ->
    read p (inord k : pos (x++z)) = read p k.
  Proof.
    move => Hk. rewrite /read. case: (ord2P k) => [/eqP->|E|i Hi].
    - by rewrite /= -inord0 ord2P0.
    - apply: contraN Hk. by rewrite (eqP E).
    - have oi : i < size (x++z) by rewrite size_cat ltn_addr.
      have H_eq: (Ordinal oi).+1 = (inord k : pos (x++z)). by rewrite -Hi inordK // ; ssrlia.
      by rewrite (ord2PC H_eq) -(tnthL (i := i)).
  Qed.

  Section CompositeWord.
    Variables (x z : word char).

    (** We first show that runs on [x] that do not cross the boundary between
    [x] and [z] do not depend on [z]. *)

    Lemma srelL (i j : pos x) p q :
      srel (size x).+1 x (p,i) (q,j) = srel (size x).+1 (x++z) (p,inord i) (q,inord j).
    Proof.
      case: (boolP (i == (size x).+1 :> nat)) => Hi.
      - rewrite /srel (eqP Hi) /= inordK ?eqxx //= ?andbF //; ssrlia.
      - have Hi' : i < (size x).+1. by rewrite ltn_neqAle Hi -ltnS ltn_ord.
        rewrite /srel /step readL // !inordK //; ssrlia.
        move: (ltn_ord j) => ?. ssrlia.
    Qed.

    Lemma runL (i j : pos x) p q :
      connect (srel (size x).+1 x) (p,i) (q,j) =
      connect (srel (size x).+1 (x++z)) (p,inord i) (q,inord j).
    Proof.
      pose f (c : nfa2_config M x) : nfa2_config M (x ++ z) := (c.1, inord c.2).
      rewrite -[(p,inord i)]/(f (p,i)) -[(q,inord j)]/(f (q,j)).
      apply: connect_transfer => //.
      - move => {p q i j} [p i] [q j] /= [->] /inord_inj.
        case/(_ _)/Wrap => [|->//]. ssrlia.
      - move => [? ?] [? ?]. rewrite /f /=. exact: srelL.
      - move => {p q i j} [p i] [q j] step. exists (q,inord j).
        rewrite /f /= inordK ?inord_val //.  move: (srel1 step) => /= Hs.
        case/andP : step => /= _ Hi. rewrite (leqRW Hs) ltn_neqAle eq_sym Hi /=.
        by rewrite inordK ltnS ?leq_ord // (leqRW (leq_ord i)) ltnS size_cat leq_addr.
    Qed.

    (** This entails, that the behaviour of [M] starting from the endpoints of
    [x] is also independent of [z]. Note that the direction from right to left
    makes use of lemma [term_uniq] *)

    Lemma Tab1P q : q \in (Tab x).1
        <-> connect (srel (size x).+1 (x++z)) (nfa2_s M,ord1) (q,inord (size x).+1).
    Proof. by rewrite /Tab inE runL /= -[ord1]inord_val. Qed.

    Lemma Tab2P p q : (p,q) \in (Tab x).2
        <-> connect (srel (size x).+1 (x++z)) (p,inord (size x)) (q,inord (size x).+1).
    Proof. by rewrite inE runL /= inordK. Qed.

    (** Dually, steps on the right of [x++z] do not depend on [x], if they do not
    cross the boundary between [x] and [z]. *)

    Lemma readR (q:M) k : k != 0 -> k < (size z).+2 ->
       read q (inord k : pos z) = read q (inord (size x + k) : pos (x++z)).
    Proof.
      move => Hk0 Hk. rewrite /read. case: (ord2P _) => [H|H|i Hi].
      - apply: contraN Hk0.
        move/eqP/(f_equal (@nat_of_ord _)) : H => /=. by rewrite inordK // => ->.
      - by rewrite -[k](@inordK (size z).+1) ?(eqP H) //= addnS -size_cat -inord_max ord2PM.
      - have Hi' : size x + i < size (x ++ z) by rewrite size_cat ltn_add2l.
        have X: (Ordinal Hi').+1 = (inord (size x + k) : pos (x ++ z)).
          by rewrite /= -addnS Hi !inordK //; ssrlia.
        by rewrite (ord2PC X) -(tnthR (i := i)).
    Qed.

    Lemma srelR (m k k' : nat) p p' : k != 0 -> k < (size z).+2 -> k' < (size z).+2 ->
        srel ((size x).+1 + m) (x++z) (p,inord (size x + k)) (p',inord (size x + k'))
      = srel m.+1 z (p,inord k) (p',inord k').
    Proof.
      move => Hk0 Hk Hk'. rewrite /srel /= !inordK ?addSnnS ?eqn_add2l //; ssrlia.
      case: (_ != _); rewrite ?andbT ?andbF // /step -?readR //.
      rewrite !inordK //; ssrlia. by rewrite -!addnS !eqn_add2l.
    Qed.

    Lemma srelRE m k p c : k < (size z).+2 -> k != 0 ->
      srel m (x++z) (p,inord (size x + k)) c ->
      exists q k', k' < (size z).+2 /\ c = (q,inord (size x + k')).
    Proof.
      move: k c => [//|k] [q j] Hk _ /srelLR [/eqP C|/eqP C];
        exists q; rewrite inordK addnS ?eqSS in C; ssrlia.
      - exists k. by rewrite ltnW // -[j]inord_val (eqP C).
      - exists k.+2. rewrite !addnS -[j]inord_val (eqP C). split => //.
        rewrite eqn_leq in C. case/andP : C => _ C.
        move: (leq_ltn_trans C (ltn_ord j)).
        by rewrite size_cat -!addnS leq_add2l.
    Qed.

  End CompositeWord.

  (** The main lemma used both in the proof of right-congruence and language
  refinement states that as long as the black-box results for [x] and [y]
  agreee, runs starting and ending on the right of composite words [x++z] and
  [y++z] behave the same even if they cross the boundaries. *)

  Lemma runR x y z p q (i j: nat) k :
    Tab x = Tab y -> i <= (size z).+1 -> 0 < j <= (size z).+1 ->
    connect (srel ((size x).+1 + k) (x++z)) (p,inord (size x + i)) (q,inord (size x + j)) ->
    connect (srel ((size y).+1 + k) (y++z)) (p,inord (size y + i)) (q,inord (size y + j)).
  Proof.
    move => Tab_eq Hi /andP [Hj0 Hj]. case/connectP => cs. move: cs i Hi p.
    apply: (size_induction (measure := size)) => /= cs IH i Hi p.
    case: (boolP (i == 0)) => Hi0.
    - rewrite (eqP Hi0) !addn0 => p1 p2.
      case: (srel_mid_path (k := (size x).+1) _ p1 p2); try solve [rewrite inordI; ssrlia].
      apply/andP; split; rewrite !inordK; ssrlia. move => p' [cl] [cr] [Ecs Lcl Pcl].
      apply/(@srel_mid (size y).+1) ; try solve [rewrite !inordK; ssrlia|rewrite -addn1; ssrlia].
      + exists p'. apply/Tab2P. rewrite -Tab_eq. apply/Tab2P. by apply/connectP; exists cl.
      + subst cs. rewrite -[_.+1 as X in inord X]addn1.
        apply: (IH cr) => {IH} //; ssrlia.
        * destruct cl as [|c cs]; simpl in *. case: Lcl => _.
          -- move/(f_equal (@nat_of_ord _)); rewrite ?inordK; intros; ssrlia.
          -- by  rewrite[size (cs ++ cr)]size_cat -addnS leq_addl.
        * rewrite cat_path -Lcl addn1 in p1 *. by case/andP : p1.
        * by rewrite p2 last_cat -Lcl addn1.
    - destruct cs as [|c cs]; simpl in *.
      + move => _ [-> /(f_equal (@nat_of_ord _))/eqP].
        rewrite !inordK ?eqn_add2l ?size_cat -?addnS ?leq_add2l // => /eqP ->.
        exact: connect0.
      + case/andP => P1 P2 L. case/srelRE: (P1) => // p' [ip] [Hip ?]; subst.
        rewrite srelR // -(@srelR y z) // in P1. apply: connect_trans (connect1 P1) _.
        exact: (IH cs).
  Qed.

  (** Variant of the lemma above, that generales equality subgoals *)
  Lemma runR_eq x y z p q (i j: nat) k xk xi xj yk yi yj :
    Tab x = Tab y -> i <= (size z).+1 -> 0 < j <= (size z).+1 ->
    xk = (size x).+1 + k -> xi = size x + i -> xj = size x + j ->
    yk = (size y).+1 + k -> yi = size y + i -> yj = size y + j ->
    connect (srel xk (x++z)) (p,inord xi) (q,inord xj) ->
    connect (srel yk (y++z)) (p,inord yi) (q,inord yj).
  Proof. move => ? ? ? ? ? ? ? ? ?. subst. exact: runR. Qed.

  Lemma Tab_refines : refines (nfa2_lang M) Tab.
  Proof.
    move => x y E.
    wlog suff W: x y E / (x \in nfa2_lang M) -> (y \in nfa2_lang M).
    { by apply/idP/idP; exact: W. }
    case/exists_inP => f Hq1 Hq2. apply/exists_inP; exists f => //. move: Hq2.
    rewrite -[x]cats0 -[y]cats0 -!(eq_connect (@srel_step_max _)).
    case/(@srel_mid (size x).+1); ssrlia => q /Tab1P q1 q2.
    apply/(@srel_mid (size y).+1); ssrlia.
    - exists q. apply/Tab1P. by rewrite -E.
    - move: q2 => {q1}. rewrite !inord_max.
      apply: (runR_eq (i := 1) (j := 1) (k := 1)); rewrite ?addn1 ?cats0 //=.
  Qed.

  Lemma Tab_rc : right_congruent Tab.
  Proof.
    move => x y a E.
    have Tab2 : (Tab (x ++ [:: a])).2 = (Tab (y ++ [:: a])).2.
    { apply/setP => [[p q]]. rewrite /Tab !inE /= !inord_max.
      apply/idP/idP; apply: (runR_eq (i := 1) (j := 2) (k := 1)); by rewrite ?size_cat ?addn1 ?addn2. }
    suff ?: (Tab (x ++ [:: a])).1 = (Tab (y ++ [:: a])).1 by congr pair.
    apply/setP => q /=. rewrite !inE.
    pose C x := connect (srel (size (x ++ [:: a])).+1 (x ++ [:: a])) (nfa2_s M, ord1) (q, ord_max).
    wlog suff W: x y E Tab2 / C x -> C y; [by apply/idP/idP; exact: W|].
    case/(@srel_mid (size x).+1); ssrlia => p /Tab1P p1 p2.
    apply/(@srel_mid (size y).+1); ssrlia.
    exists p; first by apply/Tab1P; rewrite -E. move: p2.
    rewrite -![_.+1 as X in inord X]addn1 -[1]/(size [:: a]) -!size_cat.
    rewrite !(@runL _ [::]) !inordK; ssrlia. move/Tab2P => p2. by apply/Tab2P; rewrite -Tab2.
  Qed.

  Definition nfa2_to_classifier : classifier_for (nfa2_lang M) :=
    {| cf_classifier := Classifier Tab; cf_congruent := Tab_rc; cf_refines := Tab_refines |}.

  Theorem nfa2_to_dfa :
    { A : dfa char | dfa_lang A =i nfa2_lang M & #|A| <= 2 ^ (#|M| ^ 2 + #|M|) }.
  Proof.
    exists (classifier_to_dfa (nfa2_to_classifier)); first exact: classifier_to_dfa_correct.
    rewrite card_sub (leqRW (max_card _)) [#|_|]/=.
    by rewrite card_prod expnD mulnC leq_mul //= card_set // card_prod -mulnn.
  Qed.

End NFA2toAFA.

(** If M is deterministic, the size bound on the constructed 2DFA improves
  to [(#|M|.+1)^(#|M|.+1)] *)

Arguments srel [char] M k x c d.

(** ** Improved Bound for Translation of 2DFAs to DFAs *)

Section DFA2toAFA.
  Variables (char : finType) (M : dfa2 char).

  Lemma functional_srel k w : functional (srel M k w).
  Proof. apply: functional_sub (@srel_step _ _ k w). exact: step_fun. Qed.

  Lemma term_srel k x q (H: k < (size x).+2) : terminal (srel M k x) (q,inord k).
  Proof. move => c /=. by rewrite /srel inordK // ?eqxx /= andbF. Qed.

  Lemma Tab1_uniq x p q : p \in (Tab M x).1 -> q \in (Tab M x).1 -> p = q.
  Proof.
    rewrite !inE => H1 H2. suff: (p,@ord_max (size x).+1) = (q,ord_max) by case.
    apply: term_uniq H1 H2; rewrite ?inord_max; auto using term_srel, functional_srel.
  Qed.

  Lemma Tab2_functional x p q r : (p,q) \in (Tab M x).2 -> (p,r) \in (Tab M x).2 -> q = r.
  Proof.
    rewrite !inE => /= H1 H2. suff: (q,@ord_max (size x).+1) = (r,ord_max) by case.
    apply: term_uniq H1 H2; rewrite ?inord_max; auto using term_srel, functional_srel.
  Qed.

  Definition Tab' := image_fun (@Tab_rc _ M).

  Lemma image_rc : right_congruent Tab'.
  Proof. move => x y a /(congr1 val) /= E. apply: val_inj. exact: Tab_rc. Qed.

  Lemma image_refines : refines (nfa2_lang M) Tab'.
  Proof. move => x y /(congr1 val) E. exact: Tab_refines. Qed.

  Definition dfa2_to_myhill :=
    {| cf_classifier := Classifier Tab';
       cf_congruent := image_rc;
       cf_refines := image_refines |}.

  Lemma det_range : #|{:image_type (@Tab_rc _ M)}| <= (#|M|.+1)^(#|M|.+1).
  Proof.
    pose table' := (option M * {ffun M -> option M})%type.
    apply: (@leq_trans #|{: table'}|); last by rewrite card_prod card_ffun !card_option expnS.
    pose f (x : image_type (@Tab_rc _ M)) : table' :=
      let (b,_) := x in ([pick q | q \in b.1],[ffun p => [pick q | (p,q) \in b.2]]).
    suff : injective f by apply: leq_card.
    move => [[a1 a2] Ha] [[b1 b2] Hb] [E1 /ffunP E2]. apply: val_inj => /=.
    move: Ha Hb => /dec_eq /= [x Hx] /dec_eq [y Hy].
    rewrite [Tab M x]surjective_pairing [Tab M y]surjective_pairing !xpair_eqE in Hx Hy.
    case/andP : Hx => /eqP ? /eqP ?. case/andP : Hy => /eqP ? /eqP ?. subst. f_equal.
    - apply/setP => p. case: (pickP _) E1 => q1; case: (pickP _) => q2 //; last by rewrite q1 q2.
      move => {E2} H1 H2 [?]; subst.
      wlog suff S : p x y H1 H2 / (p \in (Tab M x).1) -> (p \in (Tab M y).1).
      { apply/idP/idP; exact: S. }
      move => H. by rewrite (@Tab1_uniq x p q2).
    - apply/setP => [[p q]]. move: E2 {E1} => /(_ p). rewrite !ffunE.
      case: (pickP _) => r1; case: (pickP _) => r2 //; last by rewrite r1 r2.
      move => H1 H2 [?]; subst. apply/idP/idP => ?.
      + by rewrite (@Tab2_functional x p q r2).
      + by rewrite (@Tab2_functional y p q r2).
  Qed.

  Theorem dfa2_to_dfa :
    { A : dfa char | dfa_lang A =i dfa2_lang M & #|A| <= (#|M|.+1)^(#|M|.+1) }.
  Proof.
    exists (classifier_to_dfa (dfa2_to_myhill)); first exact: classifier_to_dfa_correct.
    rewrite card_sub (leqRW (max_card _)). exact: det_range.
  Qed.

End DFA2toAFA.
