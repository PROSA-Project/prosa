Require Export prosa.util.bigcat.

Require Import prosa.classic.util.tactics prosa.classic.util.notation prosa.classic.util.bigord.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Lemmas about the big concatenation operator. *)
Section BigCatLemmas.
  
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