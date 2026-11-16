From mathcomp Require Import ssreflect ssrbool eqtype seq.

(** * Computation of a Sequence's Supremum *)

(** This module provides a simple function [supremum] for the computation of a
    maximal element of a sequence, according to any given relation [R]. If the
    relation [R] is total and transitive, the result of [supremum]
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
  Lemma supremum_unfold :
    forall head tail,
      supremum (head :: tail) = choose_superior head (supremum tail).
  Proof.
    move=> head tail.
    by rewrite [LHS]/supremum /foldr -/(foldr choose_superior None tail) -/(supremum tail).
  Qed.

  (** Next, we observe that [supremum] returns a result for any non-empty
      list. *)
  Lemma supremum_exists : forall x s, x \in s -> supremum s != None.
  Proof.
    move=> x s IN.
    elim: s IN; first by done.
    move=> a l _ _.
    rewrite supremum_unfold.
    destruct (supremum l) as [s|]; rewrite /choose_superior //.
    by destruct (R a s).
  Qed.

  (** Conversely, if [supremum] finds nothing, then the list is empty. *)
  Lemma supremum_none : forall s, supremum s = None -> s = nil.
  Proof.
    move=> s.
    elim: s; first by done.
    move => a l IH.
    rewrite supremum_unfold /choose_superior.
    by destruct (supremum l) as [s|]; try destruct (R a s).
  Qed.

  (** Next, we observe that the value found by [supremum] comes indeed from the
      list that it was given. *)
  Lemma supremum_in :
    forall x s,
      supremum s = Some x ->
      x \in s.
  Proof.
    move=> x.
    elim => // a l IN_TAIL IN.
    rewrite in_cons; apply /orP.
    move: IN; rewrite supremum_unfold.
    destruct (supremum l) as [s|]; rewrite /choose_superior.
    { elim: (R a s) => EQ.
      - left; apply /eqP.
        by injection EQ.
      - right; by apply IN_TAIL. }
    { move=> IN; left. apply /eqP.
      by injection IN. }
  Qed.

  (** To prove that [supremum] indeed computes the given sequence's supremum,
      we need to make additional assumptions on [R]. *)

  (** (1) [R] is total. *)
  Hypothesis H_R_total : total R.
  (** (2) [R] is transitive. *)
  Hypothesis H_R_transitive : transitive R.

  (** Based on these assumptions, we show that the function [supremum] indeed
      computes an upper bound on all elements in the given sequence. *)
  Lemma supremum_spec :
    forall x s,
      supremum s = Some x ->
      forall y,
        y \in s -> R x y.
  Proof.
    move=> x s; elim: s x => [|a s IH] x; first by rewrite /supremum.
    rewrite supremum_unfold /choose_superior.
    case E: (supremum s) => [b|].
    - case AB: (R a b).
      + move=> [<-] y; rewrite in_cons => /orP [/eqP ->|Ys].
        * by move: (H_R_total a a); rewrite orbb.
        * apply: H_R_transitive AB _.
          exact: (IH b E y Ys).
      + move=> [<-] y; rewrite in_cons => /orP [/eqP ->|Ys].
        * by move: (H_R_total a b); rewrite AB /=.
        * exact: (IH b E y Ys).
    - move=> [<-] y; rewrite (supremum_none _ E) mem_seq1 => /eqP ->.
      by move: (H_R_total a a); rewrite orbb.
  Qed.

End SelectSupremum.
