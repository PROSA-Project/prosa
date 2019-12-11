From mathcomp Require Import ssreflect ssrbool eqtype seq.

(** * Computation of a Sequence's Supremum *)

(** This module provides a simple function [supremum] for the computation of a
    maximal element of a sequence, according to any given relation [R]. If the
    relation [R] is reflexive, total, and transitive, the result of [supremum]
    is indeed the supremum of the set of items in the sequence.  *)

Section SelectSupremum.

  (** Consider any type of elements with decidable equality... *)
  Context {T : eqType}.

  (** ...and any given relation [R]. *)
  Variable R : rel T.

  (** We first define a help function [choose_superior] that, given an element
      [x] and maybe a second element [y], picks [x] if [R x y] holds, and [y]
      otherwise. *)
  Definition choose_superior (x : T) (maybe_y : option T) : option T :=
    match maybe_y with
    | Some y => if R x y then Some x else Some y
    | None => Some x
    end.

  (** The supremum of a given sequence [s] can then be computed by simply
      folding [s] with [choose_superior]. *)
  Definition supremum (s : seq T) : option T := foldr choose_superior None s.

  (** Next, we establish that [supremum] satisfies its specification. To this
      end, we first establish a few simple helper lemmas. *)

  (** We start with observing how [supremum] can be unrolled one step. *)
  Lemma supremum_unfold:
    forall head tail,
      supremum (head :: tail) = choose_superior head (supremum tail).
  Proof.
    move=> head tail.
    by rewrite [LHS]/supremum /foldr -/(foldr choose_superior None tail) -/(supremum tail).
  Qed.

  (** Next, we observe that [supremum] returns a result for any non-empty
      list. *)
  Lemma supremum_exists: forall x s, x \in s -> supremum s != None.
  Proof.
    move=> x s IN.
    elim: s IN; first by done.
    move=> a l _ _.
    rewrite supremum_unfold.
    destruct (supremum l); rewrite /choose_superior //.
    by destruct (R a s).
  Qed.

  (** Conversely, if [supremum] finds nothing, then the list is empty. *)
  Lemma supremum_none: forall s, supremum s = None -> s = nil.
  Proof.
    move=> s.
    elim: s; first by done.
    move => a l IH.
    rewrite supremum_unfold /choose_superior.
    by destruct (supremum l); try destruct (R a s).
  Qed.

  (** Next, we observe that the value found by [supremum] comes indeed from the
      list that it was given. *)
  Lemma supremum_in:
    forall x s,
      supremum s = Some x ->
      x \in s.
  Proof.
    move=> x.
    elim => // a l IN_TAIL IN.
    rewrite in_cons; apply /orP.
    move: IN; rewrite supremum_unfold.
    destruct (supremum l); rewrite /choose_superior.
    { elim: (R a s) => EQ.
      - left; apply /eqP.
        by injection EQ.
      - right; by apply IN_TAIL. }
    { left. apply /eqP.
      by injection IN. }
  Qed.

  (** To prove that [supremum] indeed computes the given sequence's supremum,
      we need to make additional assumptions on [R]. *)

  (** (1) [R] is reflexive. *)
  Hypothesis H_R_reflexive: reflexive R.
  (** (2) [R] is total. *)
  Hypothesis H_R_total: total R.
  (** (3) [R] is transitive. *)
  Hypothesis H_R_transitive: transitive R.

  (** Based on these assumptions, we show that the function [supremum] indeed
      computes an upper bound on all elements in the given sequence. *)
  Lemma supremum_spec:
    forall x s,
      supremum s = Some x ->
      forall y,
        y \in s -> R x y.
  Proof.
    move=> x s SOME_x.
    move: x SOME_x (supremum_in _ _ SOME_x).
    elim: s; first by done.
    move=> s1 sn IH z SOME_z IN_z_s y.
    move: SOME_z. rewrite supremum_unfold /choose_superior => SOME_z.
    destruct (supremum sn) as [b|] eqn:SUPR; last first.
    { apply supremum_none in SUPR; subst.
      rewrite mem_seq1 => /eqP ->.
      by injection SOME_z => ->. }
    { rewrite in_cons => /orP [/eqP EQy | INy]; last first.
      - have R_by: R b y
          by apply IH => //; apply supremum_in.
        apply H_R_transitive  with (y := b) => //.
        destruct (R s1 b) eqn:R_s1b;
          by injection SOME_z => <-.
      - move: IN_z_s; rewrite in_cons => /orP [/eqP EQz | INz];
          first by subst.
        move: (H_R_total s1 b) => /orP [R_s1b|R_bs1].
        + move: SOME_z. rewrite R_s1b => SOME_z.
          by injection SOME_z => EQ; subst.
        + by destruct (R s1 b); injection SOME_z => EQ; subst. }
  Qed.

End SelectSupremum.
