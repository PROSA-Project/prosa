From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Export prosa.util.list.

(** This file contains utility lemmas not used by Prosa itself, but still
    required for legacy versions of POET. They will eventually be removed from
    Prosa. *)

(** This lemma allows us to check proposition of the form
    [forall x ∈ xs, exists y ∈ ys, P x y] using a boolean expression
    [all P (zip xs ys)]. *)
Lemma forall_exists_implied_by_forall_in_zip :
  forall {X Y : eqType} (P_bool : X * Y -> bool) (P_prop : X -> Y -> Prop) (xs : seq X),
    (forall x y, P_bool (x, y) <-> P_prop x y) ->
    (exists ys, size xs = size ys /\ all P_bool (zip xs ys) == true) ->
    (forall x, x \in xs -> exists y, P_prop x y).
Proof.
  move=> X Y P_bool P_prop xs EQ TR x IN.
  destruct TR as [ys [SIZE ALL]].
  set (idx := index x xs).
  have x__d : Y by destruct xs, ys.
  have y__d : Y by destruct xs, ys.
  exists (nth y__d ys idx); apply EQ; clear EQ.
  move: ALL => /eqP/allP -> //.
  eapply in_zip; first by done.
  exists idx; repeat split.
  - by rewrite index_mem.
  - by apply nth_index.
    Unshelve. by done.
Qed.
