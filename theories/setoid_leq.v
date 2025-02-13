(* Author: Christian Doczkal  *)
(* Distributed under the terms of CeCILL-B. *)

From Coq Require Import Basics Setoid Morphisms BinPos.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Setoid Rewriting with Ssreflect's boolean inequalities.                      *)
(** Solution suggested by Georges Gonthier (ssreflect mailinglist @ 18.12.2016) *)

(** Preorder and Instances for bool *)

Inductive leb a b := Leb of (a ==> b).

Lemma leb_eq a b : leb a b <-> (a -> b).
Proof. move: a b => [|] [|]; firstorder. Qed.

#[export] Instance: PreOrder leb.
Proof. split => [[|]|[|][|][|][?][?]]; try exact: Leb. Qed.

#[export] Instance: Proper (leb ==> leb ==> leb) andb.
Proof. move => [|] [|] [A] c d [B]; exact: Leb. Qed.

#[export] Instance: Proper (leb ==> leb ==> leb) orb.
Proof. move => [|] [|] [A] [|] d [B]; exact: Leb. Qed.

#[export] Instance: Proper (leb ==> impl) is_true.
Proof. move => a b []. exact: implyP. Qed.

(** Instances for le  *)

#[export] Instance: Proper (le --> le ++> leb) leq.
Proof. move => n m /leP ? n' m' /leP ?. apply/leb_eq => ?. eauto using leq_trans. Qed.

#[export] Instance: Proper (le ==> le ==> le) addn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_add. Qed.

#[export] Instance: Proper (le ==> le ==> le) muln.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_mul. Qed.

#[export] Instance: Proper (le ++> le --> le) subn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_sub. Qed.

#[export] Instance: Proper (le ==> le) S.
Proof. move => n m /leP ?. apply/leP. by rewrite ltnS. Qed.

#[export] Instance: RewriteRelation le := Build_RewriteRelation _.

(** Wrapper Lemma to trigger setoid rewrite *)
Definition leqRW m n  : m <= n -> le m n := leP.

(** Testing *)

Lemma T1 : forall x y, x <= y -> x + 1 <= y + 1.
Proof. move => x y h. by rewrite (leqRW h). Qed.

Lemma T2 : forall x y, x <= y -> (x + 1 <= y + 1) && true.
Proof. move => x y h. by rewrite (leqRW h) andbT. Qed.
