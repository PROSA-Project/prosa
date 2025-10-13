Require Export mathcomp.zify.zify.
Require Export prosa.util.tactics prosa.util.notation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
Require Export prosa.util.tactics prosa.util.list.

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
    rewrite big_nat_recl; last by ins.
    by rewrite mem_cat; apply/orP; left.
  Qed.

  (** Conversely, we prove that any element belonging to a concatenation of sequences
      must come from one of the sequences. *)
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
  Lemma mem_bigcat_ord :
    forall (x : T) (n : nat) (j : 'I_n) (f : 'I_n -> seq T),
      j < n ->
      x \in (f j) ->
      x \in \cat_(i < n) (f i).
  Proof.
    move=> x; elim=> [//|n IHn] j f' Hj Hx.
    rewrite big_ord_recr /= mem_cat; apply /orP.
    move: Hj; rewrite ltnS leq_eqVlt => /orP [/eqP Hj|Hj].
    - by right; rewrite (_ : ord_max = j); [|apply ord_inj].
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
    Lemma bigcat_nat_uniq :
      forall n1 n2,
        uniq (\cat_(n1 <= i < n2) (f i)).
    Proof.
      intros n1 n2.
      case (leqP n1 n2) => [LE | GT]; last by rewrite big_geq // ltnW.
      rewrite -[n2](addKn n1).
      rewrite -addnBA //; set delta := n2 - n1.
      elim: delta => [|delta IHdelta]; first by rewrite addn0 big_geq.
      rewrite addnS big_nat_recr /=; last by apply leq_addr.
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

  (** We show that filtering a concatenated sequence by any predicate
      [P] is the same as concatenating the elements of the sequence
      that satisfy [P]. *)
  Lemma bigcat_nat_filter_eq_filter_bigcat_nat :
    forall {X : Type} (F : nat -> seq X) (P : X -> bool) (t1 t2 : nat),
      [seq x <- \cat_(t1 <= t < t2) F t | P x] = \cat_(t1 <= t < t2)[seq x <- F t | P x].
  Proof.
    move=> X F P t1 t2.
    specialize (leq_total t1 t2) => /orP [T1_LT | T2_LT].
    + have EX: exists Δ, t2 = t1 + Δ by simpl; exists (t2 - t1); lia.
      move: EX => [Δ EQ]; subst t2.
      elim: Δ T1_LT => [|Δ IHΔ] T1_LT.
      { by rewrite addn0 !big_geq => //. }
      { rewrite addnS !big_nat_recr => //=; try by rewrite leq_addr.
        rewrite filter_cat IHΔ => //.
        by lia. }
    + by rewrite !big_geq => //.
  Qed.

  (** We show that the size of a concatenated sequence is the same as
      summation of sizes of each element of the sequence. *)
  Lemma size_big_nat :
    forall {X : Type} (F : nat -> seq X) (t1 t2 : nat),
      \sum_(t1 <= t < t2) size (F t)
      = size (\cat_(t1 <= t < t2) F t).
  Proof.
    move=> X F t1 t2.
    specialize (leq_total t1 t2) => /orP [T1_LT | T2_LT].
    - have EX: exists Δ, t2 = t1 + Δ by simpl; exists (t2 - t1); lia.
      move: EX => [Δ EQ]; subst t2.
      elim: Δ T1_LT => [|Δ IHΔ] T1_LT.
      { by rewrite addn0 !big_geq => //. }
      { rewrite addnS !big_nat_recr => //=; try by rewrite leq_addr.
        by rewrite size_cat IHΔ => //; lia. }
    - by rewrite !big_geq => //.
  Qed.

End BigCatNatLemmas.


(** In this section, we introduce a few lemmas about the concatenation
    operation performed over arbitrary sequences. *)
Section BigCatLemmas.

  (** Consider any two types [X] and [Y] supporting equality comparisons... *)
  Variable X Y : eqType.

  (** ...and a function [f] that, given an index [X], yields a sequence of [Y]. *)
  Variable f : X -> seq Y.

  (** First, we show that the concatenation comprises all the elements of each sequence;
      i.e. any element contained in one of the sequences will also be an element of the
      result of the concatenation. *)
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

  (** Next, we show that a map and filter operation can be done either
      before or after a concatenation, leading to the same result. *)
  Lemma bigcat_filter_eq_filter_bigcat :
    forall xss P,
      [seq x <- \cat_(xs <- xss) f xs | P x]
      = \cat_(xs <- xss) [seq x <- f xs | P x].
  Proof.
    move=> xss P.
    elim: xss => [|a xss IHxss].
    - by rewrite !big_nil.
    - by rewrite !big_cons filter_cat IHxss.
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

  (** In this section, we show some properties of the concatenation of
      sequences in combination with a function [g] that cancels [f]. *)
  Section BigCatWithCancelFunctions.

    (** Consider a function [g]... *)
    Variable g : Y -> X.

    (** ... and assume that [g] can cancel [f] starting from an element of
        the sequence [f x]. *)
    Hypothesis H_g_cancels_f : forall x y, y \in f x -> g y = x.

    (** First, we show that no element of a sequence [f x1] can be fed into
        [g] and obtain an element [x2] which differs from [x1]. Hence, filtering
        by this condition always leads to the empty sequence. *)
    Lemma seq_different_elements_nil :
      forall x1 x2,
        x1 != x2 ->
        [seq x <- f x1 | g x == x2] = [::].
    Proof.
      move => x1 x2 => /negP NEQ.
      apply filter_in_pred0.
      move => y IN; apply/negP => /eqP EQ2.
      apply: NEQ; apply/eqP.
      move: (H_g_cancels_f _ _ IN) => EQ1.
      by rewrite -EQ1 -EQ2.
    Qed.

    (** Finally, assume we are given an element [y] which is contained in a
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
      elim: xs IN UNI => [//|x' xs IHxs] IN UNI.
      move: IN; rewrite in_cons => /orP [/eqP EQ| IN].
      { subst; rewrite !big_cons.
        have -> :  [seq x <- f x' | g x == x'] = f x'.
        { apply/all_filterP/allP.
          intros y IN; apply/eqP.
          by apply H_g_cancels_f. }
        have ->: \cat_(j<-xs)[seq x <- f j | g x == x'] = [::]; last by rewrite cats0.
        rewrite big1_seq // => xs2 /andP [_ IN].
        have NEQ: xs2 != x'; last by rewrite seq_different_elements_nil.
        apply/neqP; intros EQ; subst x'.
        move: UNI; rewrite cons_uniq => /andP [NIN _].
        by move: NIN => /negP NIN; apply: NIN. }
      { rewrite big_cons IHxs //; last by move:UNI; rewrite cons_uniq=> /andP[_ ?].
        have NEQ: (x' != y); last by rewrite seq_different_elements_nil.
        apply/neqP; intros EQ; subst x'.
        move: UNI; rewrite cons_uniq => /andP [NIN _].
        by move: NIN => /negP NIN; apply: NIN. }
    Qed.

  End BigCatWithCancelFunctions.

End BigCatLemmas.


(** In the following section we introduce a lemma that relates to partitioning.*)
Section BigCatPartitionLemma.
  (** Consider an item type [X] and partition type [Y] both supporting equality comparisons. *)
  Variable X Y : eqType.

  (** Consider a sequence of items of type [X] ... *)
  Variable xs : seq X.
  (** ... and a sequence of partitions. *)
  Variable ys : seq Y.

  (** Consider a predicate [P] on [X]. *)
  Variable P : pred X.

  (** Define a mapping from items to partitions. *)
  Variable x_to_y : X -> Y.

  (** We assume that any item in [xs] has its corresponding partition in the sequence of partitions [ys]. *)
  Hypothesis H_no_partition_missing : forall x, x \in xs -> P x -> x_to_y x \in ys.

  (** Consider a partition of [xs]. *)
  Let partitioned_seq (y : Y) := [seq x <- xs | P x && (x_to_y x == y)].

  (** We prove that any element in [xs] is also contained in the union of the partitions. *)
  Lemma bigcat_partitions :
    forall j,
      (j \in [seq x <- xs | P x])
      = (j \in \cat_(y <- ys) partitioned_seq y).
  Proof.
    move=> j.
    apply /idP/idP.
    { rewrite mem_filter => /andP [PredJ_true IN].
      apply mem_bigcat with (x := x_to_y j).
      { move: IN PredJ_true.
        by apply H_no_partition_missing. }
      rewrite mem_filter.
      by do 2! [apply /andP; split; eauto]. }
    { move=> /mem_bigcat_exists [x [x_IN IN]].
      move: IN.
      rewrite !mem_filter.
      move=> /andP [/andP [PredJ X_to_Y_eq] IN].
      by apply /andP. }
  Qed.

End BigCatPartitionLemma.
