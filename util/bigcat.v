Require Export prosa.util.tactics prosa.util.notation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Lemmas about the big concatenation operator. *)
Section BigCatLemmas.

  Lemma mem_bigcat_nat:
    forall (T: eqType) x m n j (f: _ -> list T),
      m <= j < n ->
      x \in (f j) ->
      x \in \cat_(m <= i < n) (f i).
  Proof.
    intros T x m n j f LE IN; move: LE => /andP [LE LE0].
    rewrite -> big_cat_nat with (n := j); simpl; [| by ins | by apply ltnW].
    rewrite mem_cat; apply/orP; right.
    destruct n; first by rewrite ltn0 in LE0.
    rewrite big_nat_recl; last by ins.
    by rewrite mem_cat; apply/orP; left.
  Qed.

  Lemma mem_bigcat_nat_exists :
    forall (T: eqType) x m n (f: nat -> list T),
      x \in \cat_(m <= i < n) (f i) ->
      exists i, x \in (f i) /\
                m <= i < n.
  Proof.
    intros T x m n f IN.
    induction n; first by rewrite big_geq // in IN.
    destruct (leqP m n); last by rewrite big_geq ?in_nil // ltnW in IN.
    rewrite big_nat_recr // /= mem_cat in IN.
    move: IN => /orP [HEAD | TAIL].
    {
      apply IHn in HEAD; destruct HEAD; exists x0.  move: H => [H /andP [H0 H1]].
      split; first by done.
      by apply/andP; split; [by done | by apply ltnW].
    }
    {
      exists n; split; first by done.
      apply/andP; split; [by done | by apply ltnSn].
    }
  Qed.

  Lemma bigcat_nat_uniq :
    forall (T: eqType) n1 n2 (F: nat -> list T),
      (forall i, uniq (F i)) ->
      (forall x i1 i2,
         x \in (F i1) -> x \in (F i2) -> i1 = i2) ->
      uniq (\cat_(n1 <= i < n2) (F i)).
  Proof.
    intros T n1 n2 f SINGLE UNIQ.
    case (leqP n1 n2) => [LE | GT]; last by rewrite big_geq // ltnW.
    rewrite -[n2](addKn n1).
    rewrite -addnBA //; set delta := n2 - n1.
    induction delta; first by rewrite addn0 big_geq.
    rewrite addnS big_nat_recr /=; last by apply leq_addr.
    rewrite cat_uniq; apply/andP; split; first by apply IHdelta.
    apply /andP; split; last by apply SINGLE.
    rewrite -all_predC; apply/allP; intros x INx.
    simpl; apply/negP; unfold not; intro BUG.
    apply mem_bigcat_nat_exists in BUG.
    move: BUG => [i [IN /andP [_ LTi]]].
    apply UNIQ with (i1 := i) in INx; last by done.
    by rewrite INx ltnn in LTi.
  Qed.
  
End BigCatLemmas.
