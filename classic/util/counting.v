Require Export prosa.util.counting.

Require Import prosa.classic.util.tactics prosa.classic.util.ord_quantifier.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Additional lemmas about counting. *)
Section Counting.
  
  Lemma count_or :
    forall (T: eqType) (l: seq T) P Q,
      count (fun x => P x || Q x) l <= count P l + count Q l. 
  Proof.
    intros T l P Q; rewrite -count_predUI.
    apply leq_trans with (n := count (predU P Q) l);
      last by apply leq_addr.
    by apply sub_count; red; unfold predU; simpl.
  Qed.

  Lemma sub_in_count :
    forall (T: eqType) (l: seq T) (P1 P2: T -> bool),
      (forall x, x \in l -> P1 x -> P2 x) ->
      count P1 l <= count P2 l.
  Proof.
    intros T l P1 P2 SUB.
    apply leq_trans with (n := count (fun x => P1 x && (x \in l)) l);
      first by apply eq_leq, eq_in_count; red; move => x INx; rewrite INx andbT.
    by apply sub_count; red; move => x /andP [Px INx]; apply SUB.
  Qed.

  Lemma count_sub_uniqr :
    forall (T: eqType) (l1 l2: seq T) P,
      uniq l1 ->
      {subset l1 <= l2} ->
      count P l1 <= count P l2.
  Proof.
    intros T l1 l2 P UNIQ SUB.
    rewrite -!size_filter uniq_leq_size ?filter_uniq // => x.
    by rewrite !mem_filter =>/andP [-> /SUB].
  Qed.

  Lemma count_pred_inj :
    forall (T: eqType) (l: seq T) (P: T -> bool),
      uniq l ->
      (forall x1 x2, P x1 -> P x2 -> x1 = x2) ->
      count P l <= 1.
  Proof.
    intros T l P UNIQ INJ.
    induction l as [| x l']; [by done | simpl in *].
    {
      move: UNIQ => /andP [NOTIN UNIQ].
      specialize (IHl' UNIQ).
      rewrite leq_eqVlt in IHl'.
      move: IHl' => /orP [/eqP ONE | ZERO]; last first.
      {
        rewrite ltnS leqn0 in ZERO.
        by move: ZERO => /eqP ->; rewrite addn0 leq_b1.
      }
      destruct (P x) eqn:Px; last by rewrite add0n ONE.
      {
        move: ONE => /eqP ONE.
        rewrite eqn_leq in ONE; move: ONE => /andP [_ ONE].
        rewrite -has_count in ONE.
        move: ONE => /hasP ONE; destruct ONE as [y IN Py].
        specialize (INJ x y Px Py); subst.
        by rewrite IN in NOTIN.
      }
    }
  Qed.

  Lemma count_exists :
    forall (T: eqType) (l: seq T) n (P: T -> 'I_n -> bool),
      uniq l ->
      (forall y x1 x2, P x1 y -> P x2 y -> x1 = x2) ->
      count (fun (y: T) => [exists x in 'I_n, P y x]) l <= n.
  Proof.
    intros T l n P UNIQ INJ.
    induction n.
    {
      apply leq_trans with (n := count pred0 l); last by rewrite count_pred0.
      apply sub_count; red; intro x.
      by rewrite exists_ord0 //.
    }
    {
      apply leq_trans with (n := n + 1); last by rewrite addn1.
      apply leq_trans with (n := count (fun y => [exists x in 'I_n, P y (widen_ord (leqnSn n) x)] || P y ord_max) l).
      {
        apply eq_leq, eq_count; red; intro x.
        by rewrite exists_recr //.
      }
      eapply (leq_trans (count_or _ _ _ _)).
      apply leq_add.
      {
        apply IHn.
        {
          intros y x1 x2 P1 P2.
          by specialize (INJ (widen_ord (leqnSn n) y) x1 x2 P1 P2).
        }
      }
      {
        apply count_pred_inj; first by done.
        by intros x1 x2 P1 P2; apply INJ with (y := ord_max). 
      }
    }
  Qed.

End Counting.