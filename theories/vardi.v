(* Author: Christian Doczkal *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
From RegLang Require Import misc languages nfa two_way.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Vardi Construction *)

Definition bsimp := (andbT,andbF,andTb,andFb,orbT,orbF,orTb,orFb).

(** Translation from 2NFAs to NFAs for the complement language *)
                
Section Vardi.
  Variables (char : finType) (M : nfa2 char).
  Implicit Types (x y z w v : word char) (U V W : {set M}) (X Y : {set M} * {set M}).
                      
  Definition reject_cert x (T : pos x -> {set M}) := 
    [/\ nfa2_s M \in T ord1, 
        [disjoint (nfa2_f M) & (T ord_max)] & 
        forall i p j q, p \in T i -> step M x (p,i) (q,j) -> q \in T j ].

  Definition run_table x (i : pos x) := [set q | connect (step M x) (nfa2_s M, ord1) (q,i)].
  Arguments run_table x i : clear implicits.

  Lemma sub_run x C (i : pos x) : reject_cert C -> {subset run_table x i <= C i}.
  Proof using.
    case => T1 T2 T3 p. rewrite inE. case/connectP => cs. 
    elim/last_ind: cs p i => /= [p i _|cs c IH p i]; first by case => -> ->. 
    rewrite rcons_path last_rcons [last _ _]surjective_pairing => /andP [pth stp] E. subst.
    apply: T3 stp. by apply: IH; rewrite -?surjective_pairing.
  Qed.

  Lemma dfa2Pn x : reflect (exists T, @reject_cert x T) (x \notin nfa2_lang M).
  Proof using. apply: introP => [H|].
    - exists (run_table x) ; split; first by rewrite inE ?connect0.
      + apply/pred0P => q. rewrite !inE. apply: contraNF H => C.
        by apply/existsP; exists q.
      + move => i p j q. rewrite !inE => ? S. exact: connect_trans (connect1 S).
    - move/negPn => /exists_inP [q Hq1 Hq2] [c C]. 
      have/(sub_run C) H : q \in run_table x ord_max by rewrite inE.
      case: C => _ /disjoint_setI0 C _. move: C. move/setP/(_ q). by rewrite !inE Hq1 H.
  Qed.
    
  Section Completeness.
    Variables (a : char) (U V W : {set M}).
    
    Definition compL := [forall p in U, forall q, (q \in nfa2_transL p) ==> (q \in V)].

    Definition compR := [forall p in V, forall q, (q \in nfa2_transR p) ==> (q \in U)].

    Definition comp := [forall p in V, forall q, 
      (((q,L) \in nfa2_trans p a) ==> (q \in U)) && (((q,R) \in nfa2_trans p a) ==> (q \in W))].

  End Completeness.

  Definition nfa_of := 
    {| nfa_s   := [set X : {set M} * {set M} | (nfa2_s M \in X.2) & compL X.1 X.2];
       nfa_fin := [set X : {set M} * {set M} | [disjoint (nfa2_f M) & X.2] & compR X.1 X.2];
       nfa_trans X a Y := (X.2 == Y.1) && comp a X.1 X.2 Y.2 |}.

  Lemma nfa_ofP x : reflect (exists T, @reject_cert x T) (x \in nfa_lang nfa_of). 
  Proof using. apply: (iffP nfaP).
    - move => [s] [r] [Hp Hr].
      pose T (i : pos x) := if i:nat is i'.+1 then (nth s (s::r) i').2 else (nth s (s::r) 0).1.
      have T_comp (j : 'I_(size x)) :  
          comp (tnth (tape x) j) (T (inord j)) (T (inord j.+1)) (T (inord j.+2)).
        case: j => /= m Hm. move: (run_trans Hm Hr) => /andP [_]. 
        have -> : (nth s (s :: r) m).1 = T (inord m).
          case: m Hm => [|m] Hm; first by rewrite -inord0. 
          rewrite /T inordK ?ltnS // 2?ltnW //.
          move/ltnW : Hm => Hm. by case/andP : (run_trans Hm Hr) => /eqP-> ?.
        have -> : (nth s (s :: r) m).2 = T (inord m.+1) by rewrite /T inordK // ltnS ltnW.
        have -> // : (nth s r m).2 = T (inord m.+2). by rewrite /T inordK // ltnS.
      exists T. split => //.
      + rewrite /T /=. move: Hp. rewrite inE. by case/andP.
      + rewrite /T /= (run_size Hr) -last_nth. 
        move/run_last : (Hr). rewrite inE. by case/andP.
      + move => i p j q H. rewrite /step /read. 
        case: (ord2P _) => [/eqP ?|/eqP ?|i' Hi']; subst => //=.
        * rewrite [_ == 0]eqn_leq ltn0 !bsimp => /andP [q1 q2].
          rewrite /T (eqP q2) /= in H *.
          move: Hp. rewrite !inE => /andP [_ /forall_inP /(_ _ H) /forall_inP]. 
          apply. by rewrite !inE eqxx andbT /= in q1.
        * rewrite [_ == _.+2](ltn_eqF) // !bsimp eqSS => /andP [q1 q2].
          rewrite /T /= (run_size Hr) -[size r]/((size (s :: r)).-1) nth_last in H.
          move: (run_last Hr). rewrite inE. rewrite !inE eqxx andbT /= in q1.
          move => /andP [_ /forall_inP /(_ p H) /forall_inP /(_ q q1)].
          rewrite /T (eqP q2) (run_size Hr). case e : (size r) => [|m] ; first by rewrite (size0nil e).
          have Hm : m < size x by rewrite -e (run_size Hr).
          rewrite -nth_last e /=. by case/andP: (run_trans Hm Hr) => /eqP ->.
        - move: (T_comp i') => /= /forall_inP /(_ p). rewrite Hi' inord_val => /(_ H) /forallP /(_ q).
          case/andP => q1 q2. 
          case/orP; case/andP => Ht e; rewrite ?Ht /= in q1 q2.
          -- move: q2. by rewrite /T (eqP e) inordK // -Hi' ?ltnS.
          -- move: q1. rewrite -Hi' eqSS in e. by rewrite -(eqP e) -{2}[j]inord_val.
    - move => [T] [T1 T2 T3]. 
      set s := (T ord0, T ord1). exists s.
      set r := [tuple (T (inord i.+1), T (inord i.+2)) | i < (size x)]. exists r.
      have E m : m <= size x -> nth s (s :: r) m = (T (inord m), T (inord m.+1)). 
        case: m => m; first by rewrite nth0 /= -inord0 -inord1.
        move => H. by rewrite [r]lock /= -lock -[m]/(val (Ordinal H)) -tnth_nth tnth_mktuple. 
      split.
      + rewrite inE /= T1 /=. apply/forall_inP => p /T3 H. apply/forall_inP => q Hq.
        apply: H. by rewrite /step /read ord2P0 !inE Hq eqxx. 
      + apply: runI.
        * by rewrite size_map size_enum_ord. 
        * rewrite -nth_last [nth _ _ _](_ : _ = nth s (s::r) (size r)); last by case: (tval r).
          rewrite size_tuple E // -inord_max inE /= T2 /=. 
          apply/forall_inP => p /T3 H. apply/forall_inP => q Hq.
          apply H. by rewrite /step /read ord2PM !inE Hq inordK // eqxx !bsimp.
        * move => i. rewrite unfold_in. rewrite !E //= 1?ltnW // eqxx /=.
          apply/forall_inP => p /T3 H. apply/forallP => q.
          have Hi : i.+1 = (inord i.+1 : pos x). by rewrite inordK // !ltnS 1?ltnW //.
          apply/andP ; split; apply/implyP => Ht; apply H; rewrite /step /read /= (ord2PC Hi) Ht.
          - by rewrite !inordK ?eqxx ?bsimp // !(ltn_ord,ltnS,ltnW).
          - by rewrite !inordK ?eqxx ?bsimp // !(ltn_ord,ltnS,ltnW).
  Qed.
        
  Lemma nfa_of_correct : nfa_lang nfa_of =i [predC (nfa2_lang M) ].
  Proof using. move => w. rewrite !inE. apply/idP/dfa2Pn; by move/nfa_ofP. Qed.
End Vardi.

