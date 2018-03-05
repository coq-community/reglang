(* Author: Christian Doczkal *)
(* Distributed under the terms of CeCILL-B. *)
From mathcomp Require Import all_ssreflect.
Require Import misc languages dfa nfa regexp.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.

(** Preliminaries *)

(* to be used after simplification and rewriting with [tupleE] *)
Lemma behead_cons (T:Type) n (t : n.-tuple T) a : behead_tuple (cons_tuple a t) = t.
Proof.
  rewrite /cons_tuple /behead_tuple /=.
  case: t => t tP /=. set X := (behead_tupleP _). by rewrite (eq_irrelevance X tP).
Qed.

(** * Weak Monadic Second-Order Logic *)

(** We employ a minimal syntax for MSO formulas that permits only second-order
variables. *)

Inductive form :=
| Incl of  nat & nat
| Less of  nat & nat
| FF
| Imp of form & form
| Ex of form.

(** All variables are interpreted as finite sets (actually lists) of natural numbers *)
Definition valuation := nat -> seq nat.

Implicit Types (s t : form) (X Y : nat) (I : valuation) (N : seq nat).

Definition cons N I : valuation := fun k => if k is k'.+1 then I k' else N.

Fixpoint satisfies (I : valuation) (s : form) :=
  match s with 
  | Incl X Y => {subset I X <= I Y}
  | Less X Y => forall x y, x \in I X -> y \in I Y -> x < y
  | FF => False
  | Imp s t => satisfies I s -> satisfies I t
  | Ex s => exists N, satisfies (cons N I) s
  end.

Fixpoint bound (s : form) : nat :=
  match s with 
  | Incl X Y => maxn X.+1 Y.+1
  | Less X Y => maxn X.+1 Y.+1
  | FF => 0
  | Imp s t => maxn (bound s) (bound t)
  | Ex s => (bound s).-1
  end.

Definition agree n I I' := forall X, X < n -> I X =i I' X.

Lemma agree_dc n m I I' : n <= m -> agree m I I' -> agree n I I'.
Proof. move => A B X ltn_m. apply: B. exact: leq_trans A. Qed.

Lemma coincidence I I' s:
  agree (bound s) I I' -> satisfies I s <-> satisfies I' s.
Proof.
  elim: s I I' => [X Y|X Y||s IHs t IHt|s IHs] /= I I' C.
  - split.
    + move => A B. rewrite -!C ?leq_maxl ?leq_maxr //. exact: A.
    + move => A B. rewrite !C  ?leq_maxl ?leq_maxr //. exact: A.
  - split => H x y;[rewrite -!C|rewrite !C]; try solve [exact: H|by rewrite ?leq_maxl ?leq_maxr].
  - tauto.
  - by rewrite -(IHs I I') ?(IHt I I') //; apply: agree_dc C; rewrite ?leq_maxl ?leq_maxr.
  - have bound_s N : agree (bound s) (cons N I) (cons N I').
    { move => X. case: X C => //= Y A B. apply: A. rewrite -ltnS. by case: (bound s) B. }
    split.
    + move => [N] sat_s. exists N. rewrite -IHs. eassumption. exact: bound_s.
    + move => [N] sat_s. exists N. rewrite IHs. eassumption. exact: bound_s.
Qed.

Lemma weak_coincidence I I' s : (forall X, I X =i I' X) -> satisfies I s -> satisfies I' s.
Proof. move => H. by rewrite (@coincidence I I' s). Qed.

(** ** Language-Theoretic Interpretation *)
  
Section Language.
  Variables (char : finType).

  Definition I_of n (v : seq (n.-tuple bool)) : valuation :=
    fun X => [seq i <- iota 0 (size v) | nth false (nth [tuple of nseq n false] v i) X].

  Definition vec_of (w : word char) : seq (#|char|.-tuple bool) :=
    map (fun a => [tuple X == enum_rank a | X < #|char|]) w.

  Lemma I_of_vev_max k (a:char) w: 
    k \in I_of (vec_of w) (enum_rank a) -> k < size w.
  Proof. by rewrite /vec_of /I_of mem_filter mem_iota add0n size_map => /andP[_]. Qed.
    
  Lemma I_of_vecP k a w: k < size w -> 
    (k \in I_of (vec_of w) (enum_rank a) = (nth a w k == a)).
  Proof.
    move => H. rewrite /vec_of /I_of mem_filter mem_iota add0n size_map /=. 
    rewrite (nth_map a) // H andbT. 
    rewrite (nth_map (enum_rank a)) ?size_tuple ?ltn_ord //.
    by rewrite nth_ord_enum (inj_eq enum_rank_inj) eq_sym.
  Qed.

  Definition vec_lang n s := fun v : seq (n.-tuple bool) => satisfies (I_of v) s.

  Definition mso_lang s := fun w => vec_lang s (vec_of w).

  Lemma vec_of_hom : homomorphism vec_of.
  Proof. exact: map_cat. Qed.

  Lemma mso_preim s : mso_lang s =p preimage vec_of (@vec_lang #|char| s).
  Proof. done. Qed.
  
End Language.

Notation vec n := [finType of n.-tuple bool].

(** ** Translation from MSO Formulas to NFAs *)

(** propositional connectives *)

Definition nfa_for_bot n := dfa_to_nfa (dfa_void (vec n)). 

Definition nfa_for_imp n (A B : nfa (vec n)) := 
  dfa_to_nfa (dfa_op implb (nfa_to_dfa A) (nfa_to_dfa B)).

(** MSO Primitives *)

Definition nfa_for_incl n X Y :=
  {| nfa_state := [finType of unit]; 
     nfa_s := setT;
     nfa_fin := setT;
     nfa_trans := fun p (v : vec n) q => nth false v X ==> nth false v Y |}.

Definition enfa_for_ltn n X Y : enfa (vec n) := 
  {| enfa_s := [set false];
     enfa_f := setT;
     enfa_trans := fun (c : option (vec n)) p q => 
                     match p,c,q with
                     | false, Some a, false => ~~ nth false a Y
                     | true, Some a, true => ~~ nth false a X
                     | false, None, true => true
                     | _,_,_ => false
                     end; |}.

Definition nfa_for_ltn n X Y := nfa_of (enfa_for_ltn n X Y).

(** Existential Quantification *)

Definition prj0 n (w : seq (vec n.+1)) : seq (vec n) :=
  map (fun v : vec (n.+1) => [tuple of behead v]) w.
Prenex Implicits prj0.

Definition trans_b0 n (A : nfa (vec n.+1)) (p q : A) :=
  [exists b, nfa_trans p [tuple of b :: nseq n false] q].
Arguments trans_b0 [n] A p q.

Definition nfa_for_ex n (A : nfa (vec n.+1)) : nfa (vec n) := 
  {| nfa_s := nfa_s A; 
     nfa_fin := [set p | [exists (q | q \in nfa_fin A), connect (trans_b0 A) p q]];
     nfa_trans := fun p (v : vec n) q => [exists b, nfa_trans p [tuple of b::v] q] |}.

(** Translation to NFAs *)

Fixpoint nfa_of_form  n s {struct s} : nfa (vec n) :=
  match s with 
  | Incl X Y => nfa_for_incl n X Y
  | Less X Y => nfa_for_ltn n X Y
  | FF => nfa_for_bot n
  | Imp s t => nfa_for_imp (nfa_of_form n s) (nfa_of_form n t)
  | Ex s => nfa_for_ex (nfa_of_form n.+1 s)
  end.

(** ** Correctness of the Translation *)

(** Correctness of Existential Quantification *)

Fixpoint glue (bs : seq bool) n (w : seq (vec n)) :=
  match bs,w with
  | b::bs,v::w => [tuple of b :: v] :: glue bs w
  | b::bs,[::] => [tuple of b :: nseq n false] :: glue bs [::]
  | nil,w => map (fun v : vec n => [tuple of false :: v]) w
  end.

Lemma nfa_for_exI n (A : nfa (vec n.+1)) b w :
  glue b w \in nfa_lang A -> w \in nfa_lang (nfa_for_ex A).
Proof.
  rewrite /nfa_lang !inE.
  case/exists_inP => s s1 s2. apply/exists_inP. exists s => //.
  elim: b w s {s1} s2 => [w p /=|b bs IH w p].
  - elim: w p => /= [|v w IHw] p.
    + rewrite /= inE => H. by apply/exists_inP; exists p.
    + apply: sub_exists => q /andP [q1 q2]. rewrite IHw // andbT.
     by apply/existsP;exists false.
  - case: w => [|v w] /=.
    + case/exists_inP => q q1 /IH /= q2. rewrite !inE in q2 *.
      apply: sub_exists q2 => r /andP [r1 r2].
      rewrite r1 (connect_trans (connect1 _) r2) // /trans_b0. by apply/existsP;exists b.
    + apply: sub_exists => q /andP [q1 q2]. rewrite IH // andbT. by apply/existsP;exists b.
Qed.

Lemma nfa_for_exE n (A : nfa (vec n.+1)) w :
  w \in nfa_lang (nfa_for_ex A) -> exists b : seq bool, glue b w \in nfa_lang A.
Proof.
  rewrite /nfa_lang /= !inE => H.
  suff S (q:A) : @nfa_accept _ (nfa_for_ex A) q w -> exists b, nfa_accept q (glue b w).
  { case/exists_inP : H => p p1 /S [b b1]. exists b. rewrite inE. by apply/exists_inP; exists p. }
  elim: w q {H} => [|v vs IH] q /=.
  - rewrite inE => /exists_inP [f f1 /connectP[p]].
    elim: p q => [x _ |p ps IHp q /= /andP [pth1 pth2]] /= E; first by exists nil; subst.
    case: (IHp _ pth2 E) => bs Hbs. case/existsP : pth1 => b pth1. exists (b::bs). 
    by apply/exists_inP; exists p.
  - case/exists_inP => p /= /existsP [b p1] p2. case: (IH _ p2) => bs Hbs. exists (b::bs). 
    by apply/exists_inP; exists p. 
Qed.

Lemma size_glue b n (v : seq (vec n)) : size (glue b v) = maxn (size b) (size v).
Proof.
  elim: b v => [|b bs IH] v /=; first by rewrite max0n size_map.
  case: v => [|v vs]; by rewrite /= ?maxnSS IH ?maxn0.
Qed.

Lemma nth_glue0 b n (v : seq (vec n)) k :
  nth false (nth [tuple of nseq n.+1 false] (glue b v) k) 0 =
  nth false b k.
Proof.
  elim: k v b => [|k IH] [|v vs] [|b bs] //; rewrite [glue _ _]/= ?nth_nil ?nth_cons ?IH //.
  case: (ltnP k (size vs)) => A.
  - by rewrite (nth_map [tuple of nseq n false]) //.
  - by rewrite [_ _ _ k]nth_default // size_map.
Qed.

Lemma I_of_glue0 i b n (v : seq (vec n)) : 
  i \in I_of (glue b v) 0 = nth false b i.
Proof.
  rewrite mem_filter mem_iota add0n leq0n andTb.
  rewrite nth_glue0 size_glue leq_max andbC. 
  case: (ltnP i (size b)) => //= A. by rewrite nth_default ?andbF.
Qed.

Lemma nth_glueS b n (v : seq (vec n)) i k :
  nth false (nth [tuple of nseq n.+1 false] (glue b v) k) i.+1 =
  nth false (nth [tuple of nseq n false] v k) i.
Proof.
  elim: k v b => [|k IH] [|v vs] [|b bs]  //.
  - by rewrite [glue _ _]/= IH !nth_nil nth_nseq if_same.
  - rewrite [glue _ _]/= !nth_cons.
    case: (ltnP k (size vs)) => A.
    + by rewrite (nth_map [tuple of nseq n false]).
    + by rewrite ![_ _ _ k]nth_default ?size_map.
  - by rewrite [glue _ _]/= !nth_cons.
Qed.
  
Lemma I_of_glueS i b n (v : seq (vec n)) k : 
  i \in I_of (glue b v) k.+1 = nth false (nth [tuple of nseq n false] v i) k.
Proof.
  rewrite mem_filter mem_iota add0n leq0n andTb.
  rewrite nth_glueS size_glue leq_max andbC orbC.
  case: (ltnP i (size v)) => //= A. 
  by rewrite [_ _ v i]nth_default // nth_nseq if_same andbF.
Qed.

Lemma vec_ex_glue s n (vs : seq (vec n)) :
  vec_lang (Ex s) vs -> exists bs, vec_lang s (glue bs vs).
Proof.
  rewrite /vec_lang /= => [[N sat_s]]. 
  exists [seq i \in N | i <- iota 0 (\max_(k <- N) k).+1].
  apply: weak_coincidence sat_s => X i. 
  case: X => [|X].
  - rewrite I_of_glue0. case: (boolP (i < (\max_(k <- N) k).+1)) => ltn_max.
    + by rewrite (nth_map 0) ?size_iota // nth_iota.
    + rewrite nth_default ?size_map ?size_iota 1?leqNgt //. 
      apply: contraNF ltn_max => H. rewrite ltnS. exact: bigmax_seq_sup H _ _.
  - rewrite I_of_glueS /= /I_of mem_filter mem_iota /= add0n.
    case: (ltnP i (size vs)) => H; first by rewrite andbT.
    rewrite andbF [nth _ _ i]nth_default //.
    by rewrite nth_nseq if_same.
Qed.

Lemma vec_lang0 s n (v : seq (vec n)) k :
  vec_lang s v <-> vec_lang s (v ++ nseq k [tuple of nseq n false]).
Proof.
  apply coincidence => X ? i. rewrite !mem_filter !mem_iota /= !add0n size_cat nth_cat.
  case: (boolP (i < size v)) => Hi; first by rewrite ltn_addr.
  by rewrite andbF !(nth_nseq,if_same). 
Qed.

Lemma prj_glue bs n (v : seq (vec n)) :
  exists k, prj0 (glue bs v) = v ++ nseq k [tuple of nseq n false].
Proof.
  exists (size bs - size v). elim: bs v => [|b bs IH] v /=.
  - rewrite /prj0 -map_comp cats0 map_id_in //= => b. by rewrite !tupleE behead_cons.
  - case: v => [| v vs] /=; by rewrite IH /= ?subn0 ?subss !tupleE behead_cons.
Qed.

Lemma vec_Ex_prj0 s n (w : word (vec n.+1)) : vec_lang s w -> vec_lang (Ex s) (prj0 w).
Proof.
  rewrite /vec_lang => /= A.
  exists [seq i <- iota 0 (size w) | nth false (nth [tuple of nseq n.+1 false] w i) 0].
  apply: weak_coincidence A => X i. rewrite mem_filter mem_iota add0n /= /cons.
  case: X => [|X].
  + by rewrite mem_filter mem_iota /= add0n.
  + rewrite mem_filter mem_iota add0n size_map /prj0 andTb -nth_behead.
    (case: (boolP (i < _)); rewrite ?andbF ?andbT //) => A. congr nth.
      by erewrite nth_map.
Qed.

Lemma nfa_for_ex_correct n s (A : nfa (vec n.+1)) v:
  (forall u, reflect (vec_lang s u) (u \in nfa_lang A)) ->
  reflect (vec_lang (Ex s) v) (v \in nfa_lang (nfa_for_ex A)).
Proof.
  move => IHs. apply: (iffP idP).
  + case/nfa_for_exE => b. move/IHs. move/vec_Ex_prj0.
    case: (prj_glue b v) => k ->. by rewrite -vec_lang0.
  + case/vec_ex_glue => b. move/IHs. exact: nfa_for_exI.
Qed.

(** Correctness of the NFAs for the primitive operations *)

Lemma nfa_for_incl_correct X Y n (v : seq (vec n)): 
  reflect (vec_lang (Incl X Y) v) (v \in nfa_lang (nfa_for_incl n X Y)).
Proof.
  rewrite /nfa_lang inE. apply: (equivP existsP).
  rewrite (_ : (exists _,_) <-> nfa_accept (tt : nfa_for_incl n X Y) v); last first.
  - split => [[x]|];[case: x|exists tt]; by rewrite inE.
  - rewrite (_ : vec_lang _ _ <-> (forall u, u \in v -> nth false u X -> nth false u Y)).
    + elim: v => //= v vs IH. split.
      * case/exists_inP => [[/implyP A] /IH B] u /predU1P []; first by move=>?;subst.
        exact: B.
      * move => A. apply/exists_inP; exists tt;[apply/implyP|].
        -- apply: A; exact: mem_head.
        -- apply/IH => u Hu. apply: A. by rewrite inE Hu orbT.        
    + rewrite /vec_lang /=. split.
      * move => A u in_v u_X. 
        set i := index u v.
        move: (A i). rewrite /I_of !mem_filter !mem_iota !add0n /=.
        rewrite index_mem in_v !andbT. rewrite nth_index //. by apply.
      * move => A => k. rewrite /I_of !mem_filter !mem_iota !add0n /=.
        case: (boolP (_ < _)); rewrite ?andbT ?andbF // => B.
        set u := nth [tuple of nseq n false] v k.
        apply A. by rewrite mem_nth.
Qed.

Definition zero_at n X := forall (v : vec n), nth false v X = false.

Lemma nfa_for_ltnP {X Y n} {v : seq (vec n)} : 
  reflect (exists v1 v2, [/\ v = v1 ++ v2, {in v1,zero_at n Y} & {in v2,zero_at n X}]) 
          (v \in nfa_lang (nfa_for_ltn n X Y)).
Proof.
  move: v => v0. apply: (iffP (nfa_ofP _ _)).
  - rewrite /enfa_lang => [[[|_]]]; first by rewrite inE.
    suff S q v: 
      enfa_accept (N := enfa_for_ltn n X Y) q v -> 
      if q 
      then {in v, zero_at n X} 
      else (exists v1 v2, [/\ v = v1 ++ v2, {in v1,zero_at n Y} & {in v2,zero_at n X}]).
    { by move/S. }
    elim => // {v0 v} [||].
    + case => // _. by do 2 exists nil. 
    + move => [|] a [|] //= v.
      * move => A _ B u. case/predU1P => [->|]; by [rewrite (negbTE A)| apply: B].
      * move => A _ [v1] [v2] [C D E]. 
        exists (a :: v1); exists v2; split => //; first by rewrite C.
        apply/all1s. split => //. by rewrite (negbTE A).
    + move => [|] [|] // v. by exists nil; exists v.
  - move => [v1] [v2] [->] A B. exists false; first by rewrite inE. 
    elim: v1 A => /= [_|a v1 IH A].
    + (apply: EnfaNone; first instantiate (1 := true)) => //.
      elim: v2 B {v0} => [_|a s IH B]. 
      * constructor. by rewrite inE.
      * (apply: EnfaSome; first instantiate (1 := true)) => //=.
        -- by rewrite B ?inE ?eqxx.
        -- apply: IH => u C. apply B. by rewrite inE C orbT.
    + apply: EnfaSome; first instantiate (1 := false).
      * by rewrite /= A ?inE ?eqxx.
      * apply IH => u C. apply A. by rewrite inE C orbT.
Qed.

Lemma mem_I_of n (v : seq (vec n)) X k : 
  (k \in I_of v X) = (k < size v) && nth false (nth [tuple of nseq n false] v k) X.
Proof. by rewrite mem_filter mem_iota add0n /= andbC. Qed.

Lemma nfa_for_ltn_correct X Y n (v : seq (vec n)): 
  reflect (vec_lang (Less X Y) v) (v \in nfa_lang (nfa_for_ltn n X Y)).
Proof.
  apply: (iffP nfa_for_ltnP).
  - move => [v1] [v2] [A B C] i j. 
    rewrite /I_of !mem_filter !mem_iota !add0n /= ![_ && (_ < _)]andbC.
    case: (boolP (_ < _)) => //= D. case: (boolP (_ < _)) => //= E F G.
    have Hi : i < size v1.  
    { move: F. rewrite A nth_cat. case: (ifP _) => // /negbT H. 
      rewrite C ?mem_nth //. rewrite -leqNgt in H. 
      by rewrite -subSn // leq_subLR -size_cat -A. }
    have : size v1 <= j. 
    { move: G. rewrite A nth_cat. case: (ltnP j (size v1)) => // H.
      by rewrite B ? mem_nth. }
    exact: leq_trans.
  - rewrite /vec_lang /= => A.
    case: (boolP (has predT (I_of v X))).
    + case/hasP => x0 /max_mem k_in_X _.
      set k := (\max_(i <- I_of v X) i) in k_in_X. 
      have size_k: k < size v by move: k_in_X; rewrite mem_I_of => /andP[].
      have size_tk: size (take k.+1 v) = k.+1. 
      { rewrite size_take. 
        case: (ltnP k.+1 (size v)) size_k => // H1 H2.
        apply/eqP. by rewrite eqn_leq H1 H2. }
      exists (take k.+1 v); exists (drop k.+1 v); split; first by rewrite cat_take_drop.
      * move => u B. apply/negbTE/negP => D.
        pose i := index u (take k.+1 v).
        have E: i <= k by rewrite -ltnS -size_tk index_mem B.
        move: (A k i). case/(_ _ _)/Wrap => //; last by rewrite leqNgt ltnS E.
        rewrite mem_I_of (leq_ltn_trans E size_k) /=.
        rewrite /i index_take // nth_index //. exact: mem_take B.
      * move => u B. apply/negbTE/negP => D.
        pose i := k.+1 + index u (drop k.+1 v).
        have i_in_X : i \in I_of v X.
        { rewrite mem_I_of. 
          rewrite -[v](cat_take_drop k.+1) size_cat size_tk. 
          rewrite -addnS leq_add2l index_mem B andTb.
          rewrite nth_cat size_tk leqNgt leq_addr /= /i.
          by rewrite addnC -addnBA // subnn addn0 nth_index. }
        have: i <= k by apply: bigmax_seq_sup i_in_X _ _.
        by rewrite /i addSn -ltn_subRL subnn. 
    + move/hasPn => /= B. exists nil; exists v; split => // u in_v.
      apply/negbTE/negP => D. 
      pose i := index u v. move: (B i). case/(_ _)/Wrap => //.
      by rewrite mem_I_of index_mem in_v nth_index. 
Qed.

Theorem nfa_of_form_correct n (v : seq (n.-tuple bool)) s :
  reflect (vec_lang s v) (v \in nfa_lang (nfa_of_form n s)).
Proof.
  elim: s n v => [X Y|X Y||s IHs t IHt|s IHs] /= n v.
  - exact: nfa_for_incl_correct.
  - exact: nfa_for_ltn_correct.
  - rewrite -dfa_to_nfa_correct in_simpl (negbTE (dfa_void_correct _ _)).
    by constructor.
  - rewrite -dfa_to_nfa_correct dfa_op_correct -!nfa_to_dfa_correct.
    by apply: (iffP implyP) => A /IHs/A/IHt.
  - exact: nfa_for_ex_correct.
Qed.

(** Greatest number used in first n variables *)
Definition lim I n := \max_(X < n) \max_(n <- I X) n.

Definition vec_of_val I n : seq (n.-tuple bool) :=
  [seq [tuple i \in I X | X < n] | i <- iota 0 (lim I n).+1].

Lemma vec_of_val_agrees : forall I n, agree n I (I_of (vec_of_val I n)).
Proof.
  move => I n X lt_n i.
  rewrite mem_filter mem_iota /= add0n size_map size_iota.
  case: (boolP (i < _)); rewrite ?(andbT,andbF) => A.
  + rewrite /vec_of_val.
    rewrite (nth_map 0) ?size_iota // nth_iota // add0n. 
    by rewrite (nth_map (Ordinal lt_n)) ?size_enum_ord ?nth_enum_ord.
  + apply: contraNF A => A. rewrite ltnS. rewrite /lim.
    apply: bigmax_sup => //. instantiate (1 := Ordinal lt_n) => /=.
    exact: bigmax_seq_sup A _ _ . 
Qed.

Lemma vec_of_valP I s : satisfies I s <-> satisfies (I_of (vec_of_val I (bound s))) s.
Proof. apply: coincidence. exact: vec_of_val_agrees. Qed.

Corollary satisfies_dec I s : decidable (satisfies I s).
Proof. apply: dec_iff (vec_of_valP I s).  exact: decP (nfa_of_form_correct _ _). Qed.

Corollary mso_dec s : decidable (exists I, satisfies I s).
Proof.
  pose n := bound s.
  case: (nfa_inhabP (nfa_of_form n s)) => A;[left|right].
  - case: A => w /(@nfa_of_form_correct n) Hw. by exists (I_of w).
  - move => [I sat_I_s]. apply A. 
    exists (vec_of_val I n). apply/nfa_of_form_correct. 
    by rewrite /vec_lang -vec_of_valP.
Qed.

Corollary vec_lang_regular n s : regular (@vec_lang n s).
Proof.
  apply/nfa_regular. exists (nfa_of_form n s) => x. 
  apply: rwP. exact: nfa_of_form_correct. 
Qed.

(** ** Regularity of the Language of an MSO formula *)

Corollary mso_regular (char: finType) s : regular (@mso_lang char s).
Proof.
  apply: regular_ext (mso_preim s). 
  exact: preim_regular (@vec_of_hom _) (vec_lang_regular _ _).
Qed.

(** ** Translation from NFAs to WMSO *)

(** In order to translate NFAs to formulas, we define a number of defined
operations on top of the minimal syntax employed above. In particular, we make
use of the fact that [satisfies I s] is decidable and, hence, the logic behaves
classically. *)

Notation "I |= s" := (satisfies I s) (at level 50).

(** Propositional Connectives *)

Lemma satNNPP I s : ~ ~ I |= s -> I |= s.
Proof. case: (satisfies_dec I s); tauto. Qed.

Notation "s --> t" := (Imp s t) (at level 49, right associativity).
Definition Not s := Imp s FF.

Lemma satDN I s : I |= Not (Not s) <-> I |= s.
Proof. move: (@satNNPP I s) => /= ; tauto. Qed.

Lemma sat_imp I s t : I |= Imp s t <-> (I |= s -> I |= t).
Proof. done. Qed.

Lemma sat_not I s : I |= Not s <-> ~ I |= s.
Proof. done. Qed.

Definition TT := FF --> FF.

Lemma sat_true I : I |= TT.
Proof. done. Qed.

Definition And s t := Not (Imp s (Not t)).
Notation "s :/\: t" := (And s t) (at level 45).

Lemma sat_and I s t : I |= And s t <-> (I |= s /\ I |= t).
Proof. 
  rewrite /And /Not /=. split => [A|]; last tauto.
  split; apply: satNNPP; tauto.
Qed.

Definition Or s t := Not s --> t.
Notation "s :\/: t" := (Or s t) (at level 47).

Lemma sat_or I s t : I |= s :\/: t <-> I |= s \/ I |= t.
Proof. rewrite /Or /Not /=. split;[case: (satisfies_dec I s)|];tauto. Qed.

Opaque And Or.

Definition Iff s t := (s --> t) :/\: (t --> s).
Notation "s <--> t" := (Iff s t) (at level 50).

Definition All s := Not (Ex (Not s)).

Lemma sat_all I s :
  I |= All s <-> (forall N, satisfies (cons N I) s).
Proof.
  split => [A N|A].
  - apply: satNNPP => B. apply: A. by exists N.
  - case: (satisfies_dec I (Ex (Not s))) => //= [[N B]].
    exfalso. exact: B. 
Qed.

Opaque All.

(** Emptiness and Singletons *)

Definition empty X := All (Incl (X.+1) 0).

Lemma sat_empty I X : 
  I |= empty X <-> I X =i pred0.
Proof.
  rewrite sat_all; split => [/= /(_ [::]) A k|A N k]; last by rewrite A.
  rewrite inE. apply: negbTE. apply/negP. by move/A. 
Qed.

Lemma sat_emptyN I X : 
  I |= Not (empty X) <-> (exists n, n \in I X).
Proof. 
  rewrite satDN; split => [[N]|] /=.
  - case: (I X) => [|x IX _]. 
    + by case/(_ _)/Wrap.
    + by exists x; rewrite mem_head.
  - case => n A. exists [:: n.+1]. move/(_ _ A). by rewrite inE ltn_eqF.
Qed.

Definition single X := Not(empty X) :/\: All (Not(empty 0) --> Incl 0 X.+1 --> Incl X.+1 0).

Lemma sat_singles I X :
  I |= single X <-> exists n, I X =i [:: n].
Proof.
  rewrite sat_and sat_emptyN. split. 
  - move => [[n A] B].
    exists n. move => m. rewrite inE. apply/idP/eqP => [H|-> //].
    move/sat_all/(_ [:: n]): B. rewrite 2!sat_imp. case/(_ _ _)/Wrap.
    + rewrite sat_emptyN. exists n. by rewrite inE.
    + move => k /=. by rewrite inE => /eqP->.
    + move/(_ _ H). by rewrite inE => /eqP->.
  - case => n A. split; first by exists n;rewrite A.
    apply/sat_all => N. rewrite 2!sat_imp sat_emptyN => /= [[k Hk] D] m E. 
    move: (D _ Hk). rewrite A inE => /eqP ?; subst. 
    rewrite A inE in E. by rewrite (eqP E).
Qed.

(** Big Operatiors *)

Notation "\or_ ( i <- r ) F" := (\big [Or/FF]_(i <- r)  F)
  (at level 42, F at level 42, i at level 0,
    format "'[' \or_ ( i  <-  r ) '/ '  F ']'").

Notation "\or_ ( i \in A ) F" := (\big [Or/FF]_(i <- enum A)  F)
  (at level 42, F at level 42, i at level 0,
    format "'[' \or_ ( i  \in  A ) '/ '  F ']'").

Notation "\and_ ( i <- r ) F" := (\big [And/TT]_(i <- r)  F)
  (at level 41, F at level 41, i at level 0,
    format "'[' \and_ ( i  <-  r ) '/ '  F ']'").

Notation "\and_ ( i \in A ) F" := (\big [And/TT]_(i <- enum A)  F)
 (at level 41, F at level 41, i at level 0,
 format "'[' \and_ ( i  \in  A ) '/ '  F ']'").

Lemma sat_orI (T:eqType) (s : seq T) x F I :
  x \in s -> I |= F x -> I |= \or_(i <- s) F i.
Proof. elim: s => // a s IH /predU1P [<-|/IH A]; rewrite big_cons sat_or; tauto. Qed.

Lemma sat_orE (T:eqType) (s : seq T) F I :
  I |= \or_(i <- s) F i -> exists2 x, x \in s & I |= F x.
Proof.
  elim: s => // [|a s IH]; first by rewrite big_nil.
  rewrite big_cons sat_or. case => [A|/IH [x A B]]; first by exists a.
  exists x => //. by rewrite inE A orbT.
Qed.

Lemma sat_bigand (T:eqType) (s : seq T) F I : 
  I |= \and_(i <- s) F i <-> forall x, x \in s -> I |= F x.
Proof.
  elim: s => [|a s IH]; first by rewrite big_nil; split => // _; apply.
  rewrite big_cons sat_and IH. split => [[A B]x/predU1P[->//|]|A]. exact: B.
  split => [|x B]; apply: A => //. by rewrite inE B orbT.
Qed.

(** First-oder Quantification *)
(** Note that "first-order" variables are interpreted as one-element lists
rather than directly as numbers. Hence we need the lemmas [seq1P] and [sub1P] *)

Definition All1 s := All (single 0 --> s).

Lemma sat_all1 I s : 
  I |= All1 s <-> (forall n, cons [:: n] I |= s).
Proof.
  rewrite sat_all; split.
  - move => H n. move: (H [:: n]) => {H} /=. apply. rewrite sat_singles. by exists n.
  - move => H N. rewrite sat_imp sat_singles => [[n Hn]].
    apply: weak_coincidence (H n). by case.
Qed.

Definition Ex1 s := Ex (single 0 :/\: s).

Lemma sat_ex1 I s : 
  I |= Ex1 s <-> (exists n, cons [:: n] I |= s).
Proof.
  rewrite /Ex1; split. 
  - case => N. rewrite -/satisfies => /sat_and [/sat_singles [n] /= B C]. exists n. 
    apply: weak_coincidence C. by case. 
  - case => n A. exists [:: n]. apply/sat_and;split => //. 
    apply/sat_singles. by exists n. 
Qed.

(* Successor relation and Zero Predicate *)

Lemma nat_succ x y : y = x.+1 <-> x < y /\ ~ exists k, x < k /\ k < y.
Proof.
  split. 
  - move => ->. rewrite leqnn. split=>//.
    move => [k] [A B]. move:(leq_trans A B). by rewrite ltnn.
  - move => [A B]. apply/eqP. rewrite eqn_leq leqNgt A andbT. 
    apply/negP. apply: impliesPn B. constructor. 
    exists x.+1. by rewrite leqnn H. 
Qed.

Definition succ X Y := 
  Less X Y :/\: Not (Ex1 (Less X.+1 0 :/\: Less 0 Y.+1)).

Lemma sat_succ I X x Y y : I X =i [:: x] -> I Y =i [:: y] ->
  I |= succ X Y <-> y = x.+1.
Proof.
  move => A B. rewrite sat_and sat_not sat_ex1 nat_succ. 
  split => [[C D]|[C D]]. 
  - split; first apply C; rewrite ?A ?B //.
    apply: impliesPn D; constructor => [[k [k1 k2]]]. exists k.
    rewrite sat_and /=; split => ? ?; by rewrite ?A ?B => /seq1P-> /seq1P->.
  - split. move => ? ? ; by rewrite ?A ?B => /seq1P-> /seq1P->.
    apply: impliesPn D; constructor => [[k] /sat_and [k1 k2]]. exists k.
    split; [apply k1|apply k2]; by rewrite /= ?A ?B. 
Qed.

Definition zero X := single X :/\: Not (Ex1 (succ 0 X.+1)).

Lemma sat_zero I X : I X =i [:: 0] <-> I |= zero X.
Proof. 
  rewrite sat_and sat_singles sat_not sat_ex1.
  split. 
  - move => A. split; first by exists 0. 
    move => [n]. move/sat_succ. move/(_ 0 n) => /=. by case/(_ _ _)/Wrap.
  - move => [[n A] B] k. rewrite A !inE. 
    suff S : n == 0. apply/idP/idP => /eqP->; by rewrite // eq_sym. 
    destruct n as [|n] => //. exfalso. apply B.
    exists n. by rewrite (sat_succ (x := n) (y := n.+1)).
Qed.

Definition Leq X Y := All1 (succ Y.+1 0 --> Less X.+1 0).

Lemma sat_leq I X x Y y : I X =i [:: x] -> I Y =i [:: y] ->
  I |= Leq X Y <-> x <= y.
Proof.
  move => A B. rewrite sat_all1. split.
  - move/(_ y.+1). rewrite sat_imp. case/(_ _)/Wrap. 
    + by rewrite (sat_succ (x := y) (y := y.+1)).
    + move/(_ x y.+1). rewrite /= A !inE ltnS. by apply.
  - move => C n. rewrite sat_imp. rewrite (sat_succ (x := y) (y := n)) // => ->.
    move => ? ? /=. rewrite A !inE => /eqP-> /eqP->. by rewrite ltnS.
Qed.

(** Interated existential quantification *)

Definition cat (Ns: seq (seq nat)) I := 
  fun x => if x < size Ns then nth [::] Ns x else I (x - size Ns).

Lemma cat_prefix I n (Ns : n.-tuple (seq nat)) X : X < n -> cat Ns I X = nth [::] Ns X.
Proof. move => A. by rewrite /cat size_tuple A. Qed.

Lemma cat_beyond I n (Ns : n.-tuple (seq nat)) X : n <= X -> cat Ns I X = I (X - n).
Proof. move => A. by rewrite /cat size_tuple ltnNge A. Qed.

Lemma cat_size I n (Ns : n.-tuple (seq nat)) : cat Ns I n = I 0.
Proof. by rewrite cat_beyond ?subnn. Qed.

Definition exn n s := iter n Ex s.

Lemma sat_exn n s I : 
  (I |= exn n s) <-> (exists Ns : n.-tuple (seq nat), cat Ns I |= s).
Proof.
  elim: n I => [|n IH] I.
  - split. 
    + exists [tuple]. rewrite /cat /=. apply: weak_coincidence H => X. by rewrite subn0.
    + case => Ns. rewrite tuple0 /cat /=. 
      apply: weak_coincidence => X. by rewrite subn0.
  - have agr Ns N X : cat (rcons Ns N) I X =i cat Ns (cons N I) X.
      { rewrite /cat /= !size_rcons ltnS. 
        case: (ltngtP X (size Ns)) => B.
        * by rewrite (ltnW B) nth_rcons B.
        * rewrite leqNgt B /=. by rewrite -[X - size Ns]prednK ?subn_gt0 //= subnS.
        * by rewrite B leqnn subnn nth_rcons ltnn eqxx. }
    rewrite /=. split => [[N] /IH [Ns A]|].
    + exists [tuple of rcons Ns N]. apply: weak_coincidence A => X k. by rewrite agr.
    + case. case => Ns /=. elim/last_ind : Ns => // Ns N _. 
      rewrite size_rcons eqSS =>  A B.
      exists N. apply/IH. exists (Tuple A) => /=. 
      exact: weak_coincidence _ B. 
Qed.

Section NFAtoMSO.
  Variables (T : finType) (A : nfa T).
  Let n := #|A|. 
  Notation rank := enum_rank.
  Notation val := enum_val.

  Definition max :=
    All1 (Less 0 1 <--> \or_(a \in T) Incl 0 (rank a).+2).

  Lemma sat_max (w : word T)  m : 
    cons [:: m] (I_of (vec_of w)) |= max <-> m = size w.
  Proof.
    split.
    - move/sat_all1 => B.
      apply/eqP. rewrite eqn_leq [_ <= m]leqNgt [m <= _]leqNgt.
      apply/andP; split; apply/negP => C.
      + case: m C B => // m C /(_ m). case/sat_and => [/sat_imp B _]. move: B.
        case/(_ _)/Wrap; first by move => ? ? /seq1P-> /seq1P->.
        case/sat_orE => a _ /= /sub1P /I_of_vev_max => D. rewrite ltnS in C.
        move: (leq_trans D C). by rewrite ltnn.
      + move/(_ m) : B. case/sat_and => _. move/sat_imp.
        case/(_ _)/Wrap.
        * set a := (tnth (in_tuple w) (Ordinal C)).
          apply: (sat_orI (x := a)); first by rewrite mem_enum.
          apply/sub1P => /=. by rewrite I_of_vecP // {2}/a (tnth_nth a).
        * move/(_ m m) => /=. rewrite !mem_head ltnn. by case/(_ _ _)/Wrap.
    - move->. 
      rewrite sat_all1 => k.
      rewrite sat_and; split.
      + rewrite /= => H. 
        move: H => /(_ k (size w)). case/(_ _ _)/Wrap => // H.
        pose a0 := tnth (in_tuple w) (Ordinal H).
        apply (sat_orI (x := nth a0 w k)); first by rewrite mem_enum.
        rewrite /= => ? /seq1P->. by rewrite I_of_vecP ?(set_nth_default a0).
      + case/sat_orE => a _ /sub1P /=.
        rewrite /vec_of /I_of mem_filter => /andP [_].
        by rewrite mem_iota add0n size_map /= => H ? ? /seq1P-> /seq1P->.
  Qed.

  Definition part X := 
    All1 (Leq 0 X.+1 --> 
          (\or_(q \in A) (Incl 0 (rank q).+1 :/\:
                        \and_(q' \in [pred x | q != x]) Not (Incl 0 (rank q').+1)))).

  Lemma sat_part X I k : 
    I X =i [:: k] -> 
    I |= part X <-> forall n, n <= k -> exists! q:A, n \in I (rank q).
  Proof.
    move => H0. split.
    - move => H1 m Hm. move/sat_all1 : H1 => /(_ m) /sat_imp. case/(_ _)/Wrap. 
      + rewrite sat_leq ; first apply Hm; done.
      + case/sat_orE => q _ /sat_and [/= /sub1P q1 /sat_bigand q2]. 
        exists q; split => // q' B. apply/eqP. apply/negPn/negP => C.
        apply: (q2 q'); by [rewrite mem_enum inE|apply/sub1P]. 
    - move => H1. 
      apply/sat_all1 => m. rewrite sat_imp => /sat_leq H2. 
      have/H1 {H2} : m <= k by apply: H2.
      case => q [q1 q2]. apply: (sat_orI (x := q)); first by rewrite mem_enum.
      rewrite sat_and; split; first by move => ? /seq1P ->. 
      apply/sat_bigand => q'. rewrite mem_enum inE => qq' /sub1P /q2 ?. 
      subst. by rewrite eqxx in qq'.
  Qed.
  
  (* forall y x -> succ(x,y) -> x < max -> \or_( ... ) ... *)
  (*        1 0                                            *)
  Definition run X : form :=
    All1 (All1(succ 0 1 --> Less 0 X.+2 --> 
               \or_(paq \in [pred x : A * T * A | nfa_trans x.1.1 x.1.2 x.2])
               let: (p,a,q) := paq in 
                    Incl 0 ((rank a).+1 + X).+2 (* a at pos x *)
               :/\: Incl 0 (rank p).+2     (* state p active at time x *)
               :/\: Incl 1 (rank q).+2     (* state q is next state of run *)
         )).

  Lemma sat_run (Ns : n.-tuple (seq nat)) m I :
    cat Ns (cons [:: m] I) |= run n <-> 
    (forall k, k < m -> exists (p:A) (a:T) (q:A), nfa_trans p a q /\
                                       k \in I (rank a) /\ 
                                       k \in tnth Ns (rank p) /\ 
                                       k.+1 \in tnth Ns (rank q)).
  Proof.
    split.
    - move => H k lt_m. move/sat_all1/(_ k.+1) : H. move/sat_all1/(_ k).
      rewrite 2!sat_imp. case/(_ _ _)/Wrap.
      + by apply/(sat_succ (x := k) (y := k.+1)).
      + move => /= ? y /seq1P ->. rewrite cat_beyond // subnn /=.
        by move/seq1P->.
      + case/sat_orE => [[[p a] q]]. rewrite mem_enum inE /= => B.
        rewrite !sat_and. (do 2 case) => /= /sub1P C /sub1P D /sub1P E. 
        exists p. exists a. exists q. repeat split => //. 
        * by rewrite cat_beyond ?leq_addl -?addnBA // subnn addn0 in C.
        * by rewrite cat_prefix // -tnth_nth in D.
        * by rewrite cat_prefix // -tnth_nth in E.
    - move => H. apply/sat_all1 => k'. apply/sat_all1 => k. rewrite !sat_imp => B C.
      move/sat_succ : B => /(_ k' k). case/(_ _ _)/Wrap => // ?;subst.
      case: (H _ (C k m _ _)) => //=; first by rewrite cat_size //=.
      move => p [a] [q] [paq [D [E F]]]. 
      apply: (sat_orI (x := (p,a,q))); first by rewrite mem_enum. 
      rewrite !sat_and; repeat split. 
      + apply/sub1P. rewrite /= cat_beyond ?leq_addl //.
        rewrite -addnBA // subnn addn0. done.
      + apply/sub1P. by rewrite /= cat_prefix // -tnth_nth.
      + apply/sub1P. by rewrite /= cat_prefix // -tnth_nth.
  Qed.

  Definition init : form :=
    All1 (zero 0 --> \or_(q \in nfa_s A) Incl 0 (rank q).+1).
  
  Lemma sat_init (Ns : n.-tuple (seq nat)) I : 
    cat Ns I |= init <-> exists2 q, q \in nfa_s A & 0 \in tnth Ns (rank q).
  Proof.
    split.
    - move/sat_all1/(_ 0)/sat_imp. case/(_ _)/Wrap; first exact/sat_zero.
      case/sat_orE => s. rewrite mem_enum /= => B /sub1P C. exists s => //.
      by rewrite cat_prefix // -tnth_nth in C.
    - case => q q1 q2. apply/sat_all1 => m. rewrite sat_imp. move/sat_zero => /= B.
      have -> : m = 0. move: (B 0). by rewrite !inE eqxx => /eqP.
      apply (sat_orI (x := q)); first by rewrite mem_enum.
      apply/sub1P. by rewrite /= cat_prefix -?tnth_nth.
  Qed.

  Definition accept X := \or_(q \in nfa_fin A) Incl X (rank q).

  Lemma sat_accept (Ns : n.-tuple (seq nat)) m I : 
    cat Ns (cons [:: m] I) |= accept n <-> 
    exists2 q, q \in nfa_fin A & m \in tnth Ns (rank q).
  Proof.
    split.
    - case/sat_orE => q. 
      rewrite mem_enum /= cat_size ?cat_prefix // -tnth_nth.
      move => B /sub1P C. by exists q.
    - case => q q1 q2. apply: (sat_orI (x := q)); first by rewrite mem_enum.
      rewrite /= cat_size ?cat_prefix // -tnth_nth. exact/sub1P.
  Qed.
    

  (** underneath of [exn], [#|A|] refers to the length of the word (i.e. "max") *)
  Definition form_of := 
    Ex1 (max :/\: exn #|A| ( 
      part #|A| :/\: init :/\: run #|A| :/\: accept #|A|)).


  Theorem form_ofP w : reflect (@mso_lang T form_of w) (w \in nfa_lang A).
  Proof.
    apply: (iffP nfaP).
    - move =>[s] [r] [r1 r2].
      rewrite /mso_lang /vec_lang sat_ex1. exists (size w). 
      set I' := cons _ _. 
      have Hmax : I' |= max by apply/sat_max. 
      rewrite sat_and sat_exn. split => //. 
      pose pos (i : 'I_#|A|) := [seq n <- iota 0 (size r).+1 | nth s (s::r) n == enum_val i].
      pose t := [tuple pos i | i < #|A|].
      exists t.
      have tP k N (i : 'I_#|A|) : 
        k \in nth N t i = (k <= size r) && (nth s (s::r) k == val i). 
      { by rewrite -tnth_nth tnth_mktuple mem_filter mem_iota /= add0n ltnS andbC. }
      rewrite !sat_and; repeat split.
      + apply/(sat_part (k := (size w))). by rewrite cat_size.
        move => k Hk. exists (nth s (s::r) k) ;split.
        * by rewrite cat_prefix // tP -(run_size r2) Hk enum_rankK eqxx.
        * move => q'. rewrite cat_prefix //.
          rewrite tP -(run_size r2) Hk enum_rankK. by move/eqP.
      + apply/sat_init. exists s => //. by rewrite tP /= enum_rankK.
      + apply/sat_run => k Hk. have Hk': k < size r by rewrite -(run_size r2).
        exists (nth s (s::r) k). 
        exists (tnth (in_tuple w) (Ordinal Hk)). 
        exists (nth s (s :: r) k.+1). repeat split.
        * exact: run_trans. 
        * rewrite I_of_vecP //. set X := tnth _ _. by rewrite {2}/X (tnth_nth X). 
        * by rewrite tP ltnW // enum_rankK eqxx. 
        * by rewrite tP enum_rankK Hk' eqxx.
      + apply/sat_accept. exists (last s r); first exact: run_last r2. 
        rewrite tP. by rewrite (run_size r2) leqnn enum_rankK nth_last /=.
    - rewrite /mso_lang /vec_lang sat_ex1 => [[m] /sat_and [/sat_max B /sat_exn [Ns]]]. 
      repeat case/sat_and. subst. set I' := cat _ _. 
      move => /sat_part B /sat_init [s s1 s2] /sat_run D /sat_accept E.
      move: {B} (B (size w)). 
      case/(_ _)/Wrap => [k|B]; first by rewrite /I' cat_size.
      have exP (i : 'I_(size w)) : exists q : A, i.+1 \in I' (rank q). 
      { case: (B i.+1)=> // q [q1 q2]. by exists q. }
      exists s. pose r := [tuple xchoose (exP i) | i < size w]. exists r. split => //.
      have tP k p : k <= size w -> k \in tnth Ns (rank p) -> nth s (s::r) k = p.
      { case: k => [_|k lt_w] H /=. 
        - case: (B 0 _) => // q' [q1 q2]. 
          by rewrite -[p]q2 -1?[s]q2 // /I' cat_prefix // -tnth_nth.
        - rewrite (nth_map (Ordinal lt_w)) ?size_enum_ord //. 
          set m := nth _ _ _. move: (exP _) => F. move: (xchooseP F) => G.
          case: (B m.+1 _) => // q' [q1 q2]. 
          rewrite -[xchoose F]q2 -1?[p]q2 //. 
          rewrite /I' cat_prefix // -tnth_nth.
          by rewrite /m nth_enum_ord.
      }
      apply: runI.
      + by rewrite size_tuple.
      + case: E => f f1 f2. rewrite (_ : last s r = f) //. 
        by rewrite (last_nth s) size_tuple (tP _ _ _ f2).
      + move => i. move: (D _ (ltn_ord i)) => [p] [a] [q] [pq [Ha [Hp Hq]]].
        rewrite I_of_vecP // in Ha. rewrite (tnth_nth a) (eqP Ha) //.
        by rewrite (tP _ _ _ Hp) 1?ltnW // (tP _ _ _ Hq).
  Qed.

End NFAtoMSO.
