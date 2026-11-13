From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Export prosa.util.list.

(** This file contains utility lemmas not used by Prosa itself, but still
    required for legacy versions of POET. They will eventually be removed from
    Prosa. *)

(** This lemma allows us to check a proposition of the form
    [forall x ∈ xs, exists y ∈ ys, P x y] using a boolean expression
    [all P (zip xs ys)]. *)
Lemma forall_exists_implied_by_forall_in_zip :
  forall {X Y : eqType} (P_bool : X * Y -> bool) (P_prop : X -> Y -> Prop) (xs : seq X),
    (forall x y, P_bool (x, y) <-> P_prop x y) ->
    (exists ys, size xs = size ys /\ all P_bool (zip xs ys) == true) ->
    (forall x, x \in xs -> exists y, P_prop x y).
Proof.
  move=> X Y P_bool P_prop xs EQ [ys [SIZE /eqP/allP ALL]] x IN.
  case: ys SIZE ALL => [|y ys] SIZE ALL; first by case: xs IN SIZE ALL.
  exists (nth y (y :: ys) (index x xs)); apply/EQ/ALL.
  apply/(nthP (x, y)); exists (index x xs).
  - by rewrite size_zip -SIZE minnn index_mem.
  - by rewrite nth_zip // nth_index.
Qed.
