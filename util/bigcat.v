Require Export prosa.util.tactics prosa.util.notation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** In this section, we introduce useful lemmas about the concatenation operation performed
    over an arbitrary range of sequences. *)
Section BigCatLemmas.

  (** Consider any type supporting equality comparisons... *)
  Variable T: eqType.

  (** ...and a function that, given an index, yields a sequence. *)
  Variable f: nat -> list T.

  (** In this section, we prove that the concatenation over sequences works as expected: 
      no element is lost during the concatenation, and no new element is introduced. *)
  Section BigCatElements.
    
    (** First, we show that the concatenation comprises all the elements of each sequence; 
        i.e. any element contained in one of the sequences will also be an element of the 
        result of the concatenation. *)
    Lemma mem_bigcat_nat:
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
      induction n; first by rewrite big_geq // in IN.
      destruct (leqP m n); last by rewrite big_geq ?in_nil // ltnW in IN.
      rewrite big_nat_recr // /= mem_cat in IN.
      move: IN => /orP [HEAD | TAIL].
      {
        apply IHn in HEAD; destruct HEAD; exists x0.  move: H => [H /andP [H0 H1]].
        split; first by done.
          by apply/andP; split; [by done | by apply ltnW]. }
      {
        exists n; split; first by done.
        apply/andP; split; [by done | by apply ltnSn]. }
    Qed.

    Lemma mem_bigcat_ord:
      forall x n (j: 'I_n) (f: 'I_n -> list T),
        j < n ->
        x \in (f j) ->
        x \in \cat_(i < n) (f i).
    Proof.
      move=> x; elim=> [//|n IHn] j f' Hj Hx.
      rewrite big_ord_recr /= mem_cat; apply /orP.
      move: Hj; rewrite ltnS leq_eqVlt => /orP [/eqP Hj|Hj].
      { by right; rewrite (_ : ord_max = j); [|apply ord_inj]. }
      left.
      apply (IHn (Ordinal Hj)); [by []|].
      by set j' := widen_ord _ _; have -> : j' = j; [apply ord_inj|].
    Qed.

  End BigCatElements.

  (** In this section, we show how we can preserve uniqueness of the elements 
      (i.e. the absence of a duplicate) over a concatenation of sequences. *)
  Section BigCatDistinctElements.

    (** Assume that there are no duplicates in each of the possible
        sequences to concatenate... *)
    Hypothesis H_uniq_seq: forall i, uniq (f i).

    (** ...and that there are no elements in common between the sequences. *)
    Hypothesis H_no_elements_in_common:
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
      induction delta; first by rewrite addn0 big_geq.
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

    (** Conversely, if the concatenation of the sequences has no duplicates, any
        element can only belong to a single sequence. *)
    Lemma bigcat_ord_uniq_reverse :
      forall n (f: 'I_n -> list T),
        uniq (\cat_(i < n) (f i)) ->
        (forall x i1 i2,
           x \in (f i1) -> x \in (f i2) -> i1 = i2).
    Proof.
      case=> [|n]; [by move=> f' Huniq x; case|].
      elim: n => [|n IHn] f' Huniq x i1 i2 Hi1 Hi2.
      { move: i1 i2 {Hi1 Hi2}; case; case=> [i1|//]; case; case=> [i2|//].
        apply f_equal, eq_irrelevance. }
      move: (leq_ord i1); rewrite leq_eqVlt => /orP [H'i1|H'i1];
        move: (leq_ord i2); rewrite leq_eqVlt => /orP [H'i2|H'i2].
      { by apply ord_inj; move: H'i1 H'i2 => /eqP -> /eqP ->. }
      { exfalso.
        move: Huniq; rewrite big_ord_recr cat_uniq => /andP [_ /andP [H _]].
        move: H; apply /negP; rewrite Bool.negb_involutive.
        apply /hasP; exists x => /=.
        { set o := ord_max; suff -> : o = i1; [by []|].
          by apply ord_inj; move: H'i1 => /eqP ->. }
        apply (mem_bigcat_ord _ _ (Ordinal H'i2)) => //.
        by set o := widen_ord _ _; suff -> : o = i2; [|apply ord_inj]. }
      { exfalso.
        move: Huniq; rewrite big_ord_recr cat_uniq => /andP [_ /andP [H _]].
        move: H; apply /negP; rewrite Bool.negb_involutive.
        apply /hasP; exists x => /=.
        { set o := ord_max; suff -> : o = i2; [by []|].
          by apply ord_inj; move: H'i2 => /eqP ->. }
        apply (mem_bigcat_ord _ _ (Ordinal H'i1)) => //.
        by set o := widen_ord _ _; suff -> : o = i1; [|apply ord_inj]. }
      move: Huniq; rewrite big_ord_recr cat_uniq => /andP [Huniq _].
      apply ord_inj; rewrite -(inordK H'i1) -(inordK H'i2); apply f_equal.
      apply (IHn _ Huniq x).
      { set i1' := widen_ord _ _; suff -> : i1' = i1; [by []|].
        by apply ord_inj; rewrite /= inordK. }
      set i2' := widen_ord _ _; suff -> : i2' = i2; [by []|].
      by apply ord_inj; rewrite /= inordK.
    Qed.

  End BigCatDistinctElements.

End BigCatLemmas.
