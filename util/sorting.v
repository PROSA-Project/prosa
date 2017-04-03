Require Import rt.util.tactics rt.util.induction rt.util.list.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(* Lemmas about sorted lists. *)
Section Sorting.
  
  Lemma prev_le_next :
    forall (T: Type) (F: T->nat) r (x0: T) i k,
      (forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)) ->
      (i + k <= (size r).-1) ->
      F (nth x0 r i) <= F (nth x0 r (i+k)).
  Proof.
    intros T F r x0 i k ALL SIZE.
    generalize dependent i. generalize dependent k.
    induction k; intros; first by rewrite addn0 leqnn.
    specialize (IHk i.+1); exploit IHk; [by rewrite addSnnS | intro LE].
    apply leq_trans with (n := F (nth x0 r (i.+1)));
      last by rewrite -addSnnS.
    apply ALL, leq_trans with (n := i + k.+1); last by ins.
    by rewrite addnS ltnS leq_addr.
  Qed.

  Lemma sort_ordered:
    forall {T: eqType} (leT: rel T) (s: seq T) x0 idx,
      sorted leT s ->
      idx < (size s).-1 ->
      leT (nth x0 s idx) (nth x0 s idx.+1).
  Proof.
    intros T leT s x0 idx SORT LT.
    induction s; first by rewrite /= ltn0 in LT.
    simpl in SORT, LT; move: SORT => /pathP SORT.
    by simpl; apply SORT.
  Qed.
  
  Lemma sorted_rcons_prefix :
    forall {T: eqType} (leT: rel T) s x,
      sorted leT (rcons s x) ->
      sorted leT s.
  Proof.
    intros T leT s x SORT; destruct s; simpl; first by ins.
    rewrite rcons_cons /= rcons_path in SORT.
    by move: SORT => /andP [PATH _].
  Qed.

  Lemma order_sorted_rcons :
    forall {T: eqType} (leT: rel T) (s: seq T) (x last: T),
      transitive leT ->
      sorted leT (rcons s last) ->
      x \in s ->
      leT x last.
  Proof.
    intros T leT s x last TRANS SORT IN.
    induction s; first by rewrite in_nil in IN.
    simpl in SORT; move: IN; rewrite in_cons; move => /orP IN.
    destruct IN as [HEAD | TAIL];
      last by apply IHs; [by apply path_sorted in SORT| by ins].
    move: HEAD => /eqP HEAD; subst a.
    apply order_path_min in SORT; last by ins.
    move: SORT => /allP SORT.
    by apply SORT; rewrite mem_rcons in_cons; apply/orP; left.
  Qed.
  
  Lemma sorted_lt_idx_implies_rel :
    forall {T: eqType} (leT: rel T) (s: seq T) x0 i1 i2,
      transitive leT ->
      sorted leT s ->
      i1 < i2 ->
      i2 < size s ->
      leT (nth x0 s i1) (nth x0 s i2).
  Proof.
    intros T leT s x0 i1 i2 TRANS SORT LE LEsize.
    generalize dependent i2; rewrite leq_as_delta.
    intros delta LT.
    destruct s; first by rewrite ltn0 in LT.
    simpl in SORT.
    induction delta;
      first by rewrite /= addn0 ltnS in LT; rewrite /= -addnE addn0; apply/pathP.
    {
      rewrite /transitive (TRANS (nth x0 (s :: s0) (i1.+1 + delta))) //;
        first by apply IHdelta, leq_ltn_trans with (n := i1.+1 + delta.+1); [rewrite leq_add2l|].
      rewrite -[delta.+1]addn1 addnA addn1.
      move: SORT => /pathP SORT; apply SORT.
      by rewrite /= -[delta.+1]addn1 addnA addn1 ltnS in LT.
    }
  Qed.

  Lemma sorted_rel_implies_le_idx :
    forall {T: eqType} (leT: rel T) (s: seq T) x0 i1 i2,
      uniq s ->
      antisymmetric_over_list leT s ->
      transitive leT ->
      sorted leT s ->
      leT (nth x0 s i1) (nth x0 s i2) ->
      i1 < size s ->
      i2 < size s ->
      i1 <= i2.
  Proof.
    intros T leT s x0 i1 i2 UNIQ ANTI TRANS SORT REL SIZE1 SIZE2.
    generalize dependent i2.
    induction i1; first by done.
    {
      intros i2 REL SIZE2.
      feed IHi1; first by apply ltn_trans with (n := i1.+1).
      apply leq_trans with (n := i1.+1); first by done.
      rewrite ltn_neqAle; apply/andP; split.
      {
        apply/eqP; red; intro BUG; subst.
        assert (REL': leT (nth x0 s i2) (nth x0 s i2.+1)).
          by apply sorted_lt_idx_implies_rel; rewrite // ltnSn.
        rewrite /antisymmetric_over_list in ANTI.
        exploit (ANTI (nth x0 s i2) (nth x0 s i2.+1)); rewrite ?mem_nth //.
        move => /eqP EQ; rewrite nth_uniq in EQ; try (by done).
        by rewrite -[_ == _]negbK in EQ; move: EQ => /negP EQ; apply EQ; apply/eqP.
      }
      {
        apply IHi1; last by done.
        rewrite /transitive (TRANS (nth x0 s i1.+1)) //.
        by apply sorted_lt_idx_implies_rel; try (by done); apply ltnSn.
      }
    }
  Qed.

End Sorting.