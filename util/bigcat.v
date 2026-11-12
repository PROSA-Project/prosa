Require Export mathcomp.zify.zify.
Require Export prosa.util.tactics prosa.util.notation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Require Export prosa.util.bigop prosa.util.tactics prosa.util.list.

(** * Lemmas Awaiting the Next MathComp Release *)

(** In this section, we introduce a few lemmas about the concatenation
    operation performed over arbitrary sequences. *)
Section BigCatSeqLemmas.

  (** Consider any two types [X] and [Y] supporting equality comparisons... *)
  Variable X Y : eqType.

  (** ...and a function [f] that, given an index [X], yields a sequence of [Y]. *)
  Variable f : X -> seq Y.

  (** First, we show that the concatenation comprises all the elements of each sequence;
      i.e. any element contained in one of the sequences will also be an element of the
      result of the concatenation. *)
  (** TODO: MathComp's [mem_bigcatP] covers this lemma and is expected
      in the next MathComp release (PR #1660:
      https://github.com/math-comp/math-comp/pull/1660). *)
  Lemma mem_bigcat :
    forall x y s,
      x \in s ->
      y \in f x ->
      y \in \cat_(x <- s) f x.
  Proof.
    move=> x y s INs INfx.
    elim: s INs => [//|z s IHs] INs.
    rewrite big_cons mem_cat.
    move:INs; rewrite in_cons => /orP[/eqP HEAD | CONS].
    - by rewrite -HEAD; apply /orP; left.
    - by apply /orP; right; apply IHs.
  Qed.

  (** Conversely, we prove that any element belonging to a concatenation of sequences
      must come from one of the sequences. *)
  (** TODO: MathComp's [mem_bigcatP] covers this lemma and is expected
      in the next MathComp release (PR #1660:
      https://github.com/math-comp/math-comp/pull/1660). *)
  Lemma mem_bigcat_exists :
    forall {P} s y,
      y \in \cat_(x <- s | P x) f x ->
      exists x, x \in s /\ y \in f x.
  Proof.
    move=> P.
    elim=> [|a s IHs] y; first by rewrite big_nil.
    rewrite big_cons.
    case: (P a) => [|IN];
      last by move: (IHs y IN) => [x [INx INy]]; exists x; split => //; rewrite in_cons INx orbT.
    rewrite mem_cat => /orP[HEAD | CONS].
    - exists a.
      by split => //; apply mem_head.
    - move: (IHs _ CONS) => [x [INs INfx]].
      exists x; split =>//.
      by rewrite in_cons; apply /orP; right.
  Qed.

  (** In this section, we show how we can preserve uniqueness of the elements
      (i.e. the absence of a duplicate) over a concatenation of sequences. *)
  Section BigCatDistinctElements.

    (** Consider a list [xs], ... *)
    Context {xs : seq X}.

    (** ... a filter predicate [P], ... *)
    Context {P : pred X}.

    (** ... assume that there are no duplicates in each of the possible
        sequences to concatenate... *)
    Hypothesis H_uniq_f : forall x, P x -> uniq (f x).

    (** ...and that there are no elements in common between the sequences. *)
    Hypothesis H_no_elements_in_common :
      forall x y z,
        x \in f y -> x \in f z -> y = z.

    (** We prove that the concatenation will yield a sequence with unique elements. *)
    (** TODO: MathComp's [bigcat_uniq] covers this lemma and is expected
        in the next MathComp release (PR #1660:
        https://github.com/math-comp/math-comp/pull/1660). *)
    Lemma bigcat_uniq :
        uniq xs ->
        uniq (\cat_(x <- xs | P x) (f x)).
    Proof.
      move: xs.
      elim=> [|a xs' IHxs]; first by rewrite big_nil.
      rewrite cons_uniq => /andP [NINxs UNIQ].
      rewrite big_cons.
      case Pa: (P a) => //.
      rewrite cat_uniq.
      apply /andP; split; first by apply H_uniq_f.
      apply /andP; split; last by apply IHxs.
      apply /hasPn=> x IN; apply /negP=> INfa.
      move: (mem_bigcat_exists _ _ IN) => [a' [INxs INfa']].
      move: (H_no_elements_in_common x a a' INfa INfa') => EQa.
      by move: NINxs; rewrite EQa => /negP CONTRA.
    Qed.

  End BigCatDistinctElements.

End BigCatSeqLemmas.


(** In this section, we introduce lemmas about the concatenation
    operation performed over arbitrary sequences. *)
Section BigCatNatLemmas.

  (** Consider any type [T] supporting equality comparisons... *)
  Variable T : eqType.

  (** ...and a function [f] that, given an index, yields a sequence. *)
  Variable f : nat -> seq T.

  (** First, we show that the concatenation comprises all the elements of each sequence;
      i.e., any element contained in one of the sequences will also be an element of the
      result of the concatenation. *)
  (** TODO: MathComp's [mem_bigcatP] covers this lemma and is expected
      in the next MathComp release (PR #1660:
      https://github.com/math-comp/math-comp/pull/1660). *)
  Lemma mem_bigcat_nat :
    forall x m n j,
      m <= j < n ->
      x \in f j ->
      x \in \cat_(m <= i < n) (f i).
  Proof.
    intros x m n j LE IN; move: LE => /andP [LE LE0].
    rewrite -> big_cat_nat with (n := j); simpl; [| by ins | by apply ltnW].
    rewrite mem_cat; apply/orP; right.
    destruct n; first by rewrite ltn0 in LE0.
    rewrite big_nat_recl; first by ins.
    by rewrite mem_cat; apply/orP; left.
  Qed.

  (** Conversely, we prove that any element belonging to a concatenation of sequences
      must come from one of the sequences. *)
  (** TODO: MathComp's [mem_bigcatP] covers this lemma and is expected
      in the next MathComp release (PR #1660:
      https://github.com/math-comp/math-comp/pull/1660). *)
  Lemma mem_bigcat_nat_exists :
    forall x m n,
      x \in \cat_(m <= i < n) (f i) ->
      exists i,
        x \in f i /\ m <= i < n.
  Proof.
    intros x m n IN.
    elim: n IN => [|n IHn] IN; first by rewrite big_geq // in IN.
    destruct (leqP m n); last by rewrite big_geq ?in_nil // ltnW in IN.
    rewrite big_nat_recr // /= mem_cat in IN.
    move: IN => /orP [HEAD | TAIL].
    - move: (IHn HEAD) => [x0 [H /andP[H0 H1]]]; exists x0.
      split; first by done.
      by apply/andP; split; last by apply ltnW.
    - exists n; split; first by done.
      by apply/andP; split; last apply ltnSn.
  Qed.

  (** We also restate lemma [mem_bigcat_nat] in terms of ordinals. *)
  (** TODO: MathComp's [mem_bigcatP] covers this lemma and is expected
      in the next MathComp release (PR #1660:
      https://github.com/math-comp/math-comp/pull/1660). *)
  Lemma mem_bigcat_ord :
    forall (x : T) (n : nat) (j : 'I_n) (f : 'I_n -> seq T),
      j < n ->
      x \in (f j) ->
      x \in \cat_(i < n) (f i).
  Proof.
    move=> x; elim=> [//|n IHn] j f' Hj Hx.
    rewrite big_ord_recr /= mem_cat; apply /orP.
    move: Hj; rewrite ltnS leq_eqVlt => /orP [/eqP Hj|Hj].
    - have EQ: ord_max = j by apply ord_inj; rewrite /= Hj.
      by right; rewrite EQ.
    - left.
      apply (IHn (Ordinal Hj)); [by []|].
      by set j' := widen_ord _ _; have -> : j' = j; [apply ord_inj|].
  Qed.

  (** In this section, we show how we can preserve uniqueness of the elements
      (i.e. the absence of a duplicate) over a concatenation of sequences. *)
  Section BigCatNatDistinctElements.

    (** Assume that there are no duplicates in each of the possible
        sequences to concatenate... *)
    Hypothesis H_uniq_seq : forall i, uniq (f i).

    (** ...and that there are no elements in common between the sequences. *)
    Hypothesis H_no_elements_in_common :
      forall x i1 i2, x \in f i1 -> x \in f i2 -> i1 = i2.

    (** We prove that the concatenation will yield a sequence with unique elements. *)
    (** TODO: MathComp's [bigcat_uniq] covers this lemma and is expected
        in the next MathComp release (PR #1660:
        https://github.com/math-comp/math-comp/pull/1660). *)
    Lemma bigcat_nat_uniq :
      forall n1 n2,
        uniq (\cat_(n1 <= i < n2) (f i)).
    Proof.
      intros n1 n2.
      case (leqP n1 n2) => [LE | GT]; last by rewrite big_geq // ltnW.
      rewrite -[n2](addKn n1).
      rewrite -addnBA //; set delta := n2 - n1.
      elim: delta => [|delta IHdelta]; first by rewrite addn0 big_geq.
      rewrite addnS big_nat_recr /=; first by apply leq_addr.
      rewrite cat_uniq; apply/andP; split; first by apply IHdelta.
      apply /andP; split; last by apply H_uniq_seq.
      rewrite -all_predC; apply/allP; intros x INx.
      simpl; apply/negP; unfold not; intro BUG.
      apply mem_bigcat_nat_exists in BUG.
      move: BUG => [i [IN /andP [_ LTi]]].
      apply H_no_elements_in_common with (i1 := i) in INx; last by done.
      by rewrite INx ltnn in LTi.
    Qed.

  End BigCatNatDistinctElements.

End BigCatNatLemmas.


(** * Recovering a Component of a Concatenation *)

(** In this section, we show how to recover one sequence from a concatenation
    by filtering for the elements that originate from it. *)
Section BigCatReconstruction.

  (** Consider any two types [X] and [Y] supporting equality comparisons... *)
  Variable X Y : eqType.

  (** ...and a function [f] that, given an index [X], yields a sequence of [Y]. *)
  Variable f : X -> seq Y.

  (** Consider a function [g]... *)
  Variable g : Y -> X.

  (** ... and assume that [g] can cancel [f] starting from an element of
      the sequence [f x]. *)
  Hypothesis H_g_cancels_f : forall x y, y \in f x -> g y = x.

  (** Assume we are given an element [y] which is contained in a
      duplicate-free sequence [xs]. Then, [f] is applied to each element of
      [xs], but only the elements for which [g] yields [y] are kept. In this
      scenario, concatenating the resulting sequences will always lead to [f y]. *)
  Lemma bigcat_seq_uniqK :
    forall y xs,
      y \in xs ->
      uniq xs ->
      \cat_(x <- xs) [seq x' <- f x | g x' == y] = f y.
  Proof.
    move=> y xs IN UNI.
    transitivity (\cat_(x <- xs | x == y) f x); last by apply: big_pred1_seq.
    rewrite [RHS]big_mkcond; apply: eq_bigr => x _.
    case: eqP => [-> | NE].
    - apply/all_filterP/allP => z INz.
      by rewrite (H_g_cancels_f _ _ INz) eqxx.
    - apply: filter_in_pred0 => z INz.
      by rewrite (H_g_cancels_f _ _ INz); apply/eqP.
  Qed.

End BigCatReconstruction.
