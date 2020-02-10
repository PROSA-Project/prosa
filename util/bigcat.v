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
    
  End BigCatDistinctElements.
  
End BigCatLemmas.
