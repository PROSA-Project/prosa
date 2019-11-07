Require Import rt.util.tactics rt.util.notation rt.util.bigord.
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
  
  Lemma mem_bigcat_ord:
    forall (T: eqType) x n (j: 'I_n) (f: 'I_n -> list T),
      j < n ->
      x \in (f j) ->
      x \in \cat_(i < n) (f i).
  Proof.
    intros T x n j f LE IN; rewrite (big_mkord_ord nil).
    rewrite -(big_mkord (fun x => true)).
    apply mem_bigcat_nat with (j := j);
      [by apply/andP; split | by rewrite eq_fun_ord_to_nat].
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

  Lemma mem_bigcat_ord_exists :
    forall (T: eqType) x n (f: 'I_n -> list T),
      x \in \cat_(i < n) (f i) ->
      exists i, x \in (f i).
  Proof.
    intros T x n f IN.
    induction n; first by rewrite big_ord0 in_nil in IN.
    {
      rewrite big_ord_recr /= mem_cat in IN.
      move: IN => /orP [HEAD | TAIL].
      {
        apply IHn in HEAD; destruct HEAD as [x0 IN].
        by eexists (widen_ord _ x0); apply IN.
      }
      {
        by exists ord_max; desf.
      }
    }
  Qed.

  Lemma bigcat_ord_uniq :
    forall (T: eqType) n (f: 'I_n -> list T),
      (forall i, uniq (f i)) ->
      (forall x i1 i2,
         x \in (f i1) -> x \in (f i2) -> i1 = i2) ->
      uniq (\cat_(i < n) (f i)).
  Proof.
    intros T n f SINGLE UNIQ.
    induction n; first by rewrite big_ord0.
    {
      rewrite big_ord_recr cat_uniq; apply/andP; split.
      {
        apply IHn; first by done.
        intros x i1 i2 IN1 IN2.
        exploit (UNIQ x);
          [by apply IN1 | by apply IN2 | intro EQ; inversion EQ].
        by apply ord_inj.
      }
      apply /andP; split; last by apply SINGLE.
      {
        rewrite -all_predC; apply/allP; intros x INx.

        simpl; apply/negP; unfold not; intro BUG.
        rewrite -big_ord_narrow in BUG.
        rewrite big_mkcond /= in BUG.
        have EX := mem_bigcat_ord_exists T x n.+1 _.
        apply EX in BUG; clear EX; desf.
        apply UNIQ with (i1 := ord_max) in BUG; last by done.
        by desf; unfold ord_max in *; rewrite /= ltnn in Heq.
      }
    }
  Qed.

  Lemma map_bigcat_ord {T} {T'} n (f: 'I_n -> seq T) (g: T -> T') :
    map g (\cat_(i < n) (f i)) = \cat_(i < n) (map g (f i)).
  Proof.
    destruct n; first by rewrite 2!big_ord0. 
    induction n; first by rewrite 2!big_ord_recr 2!big_ord0.
    rewrite big_ord_recr [\cat_(cpu < n.+2)_]big_ord_recr /=.
    by rewrite map_cat; f_equal; apply IHn.
  Qed.

  Lemma size_bigcat_ord {T} n (f: 'I_n -> seq T) :
    size (\cat_(i < n) (f i)) = \sum_(i < n) (size (f i)).
  Proof.
    destruct n; first by rewrite 2!big_ord0.
    induction n; first by rewrite 2!big_ord_recr 2!big_ord0 /= add0n.
    rewrite big_ord_recr [\sum_(i0 < n.+2)_]big_ord_recr size_cat /=.
    by f_equal; apply IHn.
  Qed.

  Lemma size_bigcat_ord_max {T} n (f: 'I_n -> seq T) m :
    (forall x, size (f x) <= m) ->
    size (\cat_(i < n) (f i)) <= m*n.
  Proof.
    intros SIZE.
    rewrite size_bigcat_ord.
    apply leq_trans with (n := \sum_(i0 < n) m);
      last by rewrite big_const_ord iter_addn addn0.
    by apply leq_sum; ins; apply SIZE. 
  Qed.
  
End BigCatLemmas.
