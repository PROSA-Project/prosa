(** Setoid Rewriting with boolean inequalities of ssreflect. Solution
    suggested by Georges Gonthier (ssreflect mailinglist @ 18.12.2016) *)

From Stdlib Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(** This construction allows us to "rewrite" inequalities with ≤. *)

Inductive leb a b := Leb of (a ==> b).

(** The following establishes a number of "plumbing facts" that are necessary to
    interface [leb] with the [rewrite] tactic. *)

(** [leb] expresses an implication. *)
Lemma leb_eq a b : leb a b <-> (a -> b).
Proof. move: a b => [|] [|]; firstorder. Qed.

(** [leb] is a preorder. *)
#[global] Instance : PreOrder leb.
Proof. split => [[|]|[|][|][|][?][?]]; try exact: Leb. Qed.

(** Various  [leb] required for the interface:

    Relation of [leb] and [andb]. *)
#[global] Instance : Proper (leb ==> leb ==> leb) andb.
Proof. move => [|] [|] [A] c d [B]; exact: Leb. Qed.

(** Relation of [leb] and [orb]. *)
#[global] Instance : Proper (leb ==> leb ==> leb) orb.
Proof. move => [|] [|] [A] [|] d [B]; exact: Leb. Qed.

(** Relation of [leb] and [is_true]. *)
#[global] Instance : Proper (leb ==> impl) is_true.
Proof. move => a b []. exact: implyP. Qed.

(** Relation with [leq]. *)
#[global] Instance : Proper (le --> le ++> leb) leq.
Proof. move => n m /leP ? n' m' /leP ?. apply/leb_eq => ?. eauto using leq_trans. Qed.

(** Relation with [addn]. *)
#[global] Instance : Proper (le ==> le ==> le) addn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_add. Qed.

(** Relation with [subn]. *)
#[global] Instance : Proper (le ++> le --> le) subn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_sub. Qed.

(** Relation with the successor constructor. *)
#[global] Instance : Proper (le ==> le) S.
Proof. move => n m /leP ?. apply/leP. by rewrite ltnS. Qed.

(** Establishing [le] as a rewrite relation. *)
#[global] Instance : RewriteRelation le.
Defined.

(** Wrapper for use in rewrite steps: *)
Definition leqRW {m n} : m <= n -> le m n := leP.

(** To see the benefits, consider the following example.

<<
Goal
  forall a b c d x y,
    x <= y ->
    a + (b + (x + c)) + d <= a + (b + (y + c)) + d.
Proof.
  move => a b c d x y LE.
  (* This could be an unpleasant proof, but we can just [rewrite LE] *)
  by rewrite (leqRW LE). (* magic here *)
Qed.
>>
 *)

(** Another benefit of [leqRW] is that it allows
    to avoid unnecessary [eapply leq_trans].

<<
Goal
  forall a b x y z,
    a <= x ->
    b <= y ->
    x + y <= z ->
    a + b <= z.
Proof.
  move => a b x y z LE1 LE2 LE3.
  rewrite -(leqRW LE3) leq_add //.
Qed.
>>
 *)
