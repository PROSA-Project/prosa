Require Export prosa.util.notation.
Require Export prosa.util.nat.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(* Lemmas about sum. *)
Section ExtraLemmas.

  Lemma leq_sum_seq (I: eqType) (r: seq I) (P : pred I) (E1 E2 : I -> nat) :
    (forall i, i \in r -> P i -> E1 i <= E2 i) ->
    \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
  Proof.
    intros LE.
    rewrite big_seq_cond [\sum_(_ <- _| P _)_]big_seq_cond.
      by apply leq_sum; move => j /andP [IN H]; apply LE.
  Qed.

  Lemma eq_sum_seq: forall (I: eqType) (r: seq I) (P: pred I) (E1 E2 : I -> nat), 
      (forall i, i \in r -> P i -> E1 i == E2 i) ->
      \sum_(i <- r | P i) E1 i == \sum_(i <- r | P i) E2 i.
  Proof.
    intros; rewrite eqn_leq; apply/andP; split.
    - apply leq_sum_seq; intros.
        by move: (H i H0 H1) => /eqP EQ; rewrite EQ.
    - apply leq_sum_seq; intros.
        by move: (H i H0 H1) => /eqP EQ; rewrite EQ.
  Qed.  

  Lemma sum_nat_eq0_nat (T : eqType) (F : T -> nat) (r: seq T) :
    all (fun x => F x == 0) r = (\sum_(i <- r) F i == 0).
  Proof.
    destruct (all (fun x => F x == 0) r) eqn:ZERO.
    - move: ZERO => /allP ZERO; rewrite -leqn0.
      rewrite big_seq_cond (eq_bigr (fun x => 0));
        first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
      intro i; rewrite andbT; intros IN.
      specialize (ZERO i); rewrite IN in ZERO.
        by move: ZERO => /implyP ZERO; apply/eqP; apply ZERO.
    - apply negbT in ZERO; rewrite -has_predC in ZERO.
      move: ZERO => /hasP ZERO; destruct ZERO as [x IN NEQ]; simpl in NEQ.
      rewrite (big_rem x) /=; last by done.
      symmetry; apply negbTE; rewrite neq_ltn; apply/orP; right.
      apply leq_trans with (n := F x); last by apply leq_addr.
        by rewrite lt0n.
  Qed.


  Lemma sum_seq_gt0P:
    forall (T:eqType) (r: seq T) (F: T -> nat),
      reflect (exists i, i \in r /\ 0 < F i) (0 < \sum_(i <- r) F i).
  Proof.
    intros; apply: (iffP idP); intros.
    {
      induction r; first by rewrite big_nil in H.
      destruct (F a > 0) eqn:POS.
      exists a; split; [by rewrite in_cons; apply/orP; left | by done].
      apply negbT in POS; rewrite -leqNgt leqn0 in POS; move: POS => /eqP POS.
      rewrite big_cons POS add0n in H. clear POS.
      feed IHr; first by done. move: IHr => [i [IN POS]].
      exists i; split; [by rewrite in_cons; apply/orP;right | by done].
    }
    {
      move: H => [i [IN POS]].
      rewrite (big_rem i) //=.
      apply leq_trans with (F i); [by done | by rewrite leq_addr].
    }
  Qed.

  Lemma sum_notin_rem_eqn:
    forall (T:eqType) (a: T) xs P F,
      a \notin xs ->
      \sum_(x <- xs | P x && (x != a)) F x = \sum_(x <- xs | P x) F x.
  Proof.
    intros ? ? ? ? ? NOTIN.
    induction xs; first by rewrite !big_nil.
    rewrite !big_cons.
    rewrite IHxs; clear IHxs; last first.
    { apply/memPn; intros y IN.
      move: NOTIN => /memPn NOTIN.
        by apply NOTIN; rewrite in_cons; apply/orP; right.
    }
    move: NOTIN => /memPn NOTIN. 
    move: (NOTIN a0) => NEQ.
    feed NEQ; first by (rewrite in_cons; apply/orP; left).
      by rewrite NEQ Bool.andb_true_r.
  Qed.
  
  (* Trivial identity: any sum of zeros is zero. *)
  Lemma sum0 m n:
    \sum_(m <= i < n) 0 = 0.
  Proof.
    by rewrite big_const_nat iter_addn mul0n addn0 //.
  Qed.

  (* A sum of natural numbers equals zero iff all terms are zero. *)
  Lemma big_nat_eq0 m n F:
    \sum_(m <= i < n) F i = 0 <-> (forall i, m <= i < n -> F i = 0).
  Proof.
    split.
    - rewrite /index_iota => /eqP.
      rewrite -sum_nat_eq0_nat => /allP ZERO i.
      rewrite -mem_index_iota /index_iota => IN.
      by apply/eqP; apply ZERO.
    - move=> ZERO.
      have ->: \sum_(m <= i < n) F i = \sum_(m <= i < n) 0
        by apply eq_big_nat => //.
      by apply sum0.
  Qed.

  (* We prove that if any element of a set r is bounded by constant [const], 
     then the sum of the whole set is bounded by [const * size r]. *)
  Lemma sum_majorant_constant:
    forall (T: eqType) (r: seq T) (P: pred T) F const,
      (forall a,  a \in r -> P a -> F a <= const) -> 
      \sum_(j <- r | P j) F j <= const * (size [seq j <- r | P j]).
  Proof.
    clear; intros.
    induction r; first by rewrite big_nil.
    feed IHr.
    { intros; apply H.
      - by rewrite in_cons; apply/orP; right.
      - by done. } 
    rewrite big_cons.
    destruct (P a) eqn:EQ.
    { rewrite -cat1s filter_cat size_cat.
      rewrite mulnDr.
      apply leq_add; last by done.
      rewrite size_filter.
      simpl; rewrite addn0.
      rewrite EQ muln1.
      apply H; last by done. 
        by rewrite in_cons; apply/orP; left. 
    }
    { apply leq_trans with (const * size [seq j <- r | P j]); first by done.
      rewrite leq_mul2l; apply/orP; right.
      rewrite -cat1s filter_cat size_cat.
        by rewrite leq_addl.
    }
  Qed.

  (* We prove that if for any element x of a set [xs] the following two statements hold 
     (1) [F1 x] is less than or equal to [F2 x] and (2) the sum [F1 x_1, ..., F1 x_n] 
     is equal to the sum of [F2 x_1, ..., F2 x_n], then [F1 x] is equal to [F2 x] for 
     any element x of [xs]. *)
  Lemma sum_majorant_eqn:
    forall (T: eqType) xs F1 F2 (P: pred T),
      (forall x, x \in xs -> P x -> F1 x <= F2 x) -> 
      \sum_(x <- xs | P x) F1 x = \sum_(x <- xs | P x) F2 x ->
      (forall x, x \in xs -> P x -> F1 x = F2 x).
  Proof.
    intros T xs F1 F2 P H1 H2 x IN PX.
    induction xs; first by done.
    have Fact: \sum_(j <- xs | P j) F1 j <= \sum_(j <- xs | P j) F2 j.
    { rewrite [in X in X <= _]big_seq_cond [in X in _ <= X]big_seq_cond leq_sum //.
      move => y /andP [INy PY].
      apply: H1; last by done. 
        by rewrite in_cons; apply/orP; right. }
    feed IHxs.
    { intros x' IN' PX'.
      apply H1; last by done.
        by rewrite in_cons; apply/orP; right. }
    rewrite big_cons [RHS]big_cons in H2.
    have EqLeq: forall a b c d, a + b = c + d -> a <= c -> b >= d.
    { clear; intros; ssromega. } 
    move: IN; rewrite in_cons; move => /orP [/eqP EQ | IN]. 
    { subst a.
      rewrite PX in H2.
      specialize (H1 x).
      feed_n 2 H1; [ by rewrite in_cons; apply/orP; left | by done | ].
      move: (EqLeq
               (F1 x) (\sum_(j <- xs | P j) F1 j)
               (F2 x) (\sum_(j <- xs | P j) F2 j) H2 H1) => Q.
      have EQ: \sum_(j <- xs | P j) F1 j = \sum_(j <- xs | P j) F2 j. 
      { by apply/eqP; rewrite eqn_leq; apply/andP; split. }
        by move: H2 => /eqP; rewrite EQ eqn_add2r; move => /eqP EQ'.
    }
    { destruct (P a) eqn:PA; last by apply IHxs.
      apply: IHxs; last by done.
      specialize (H1 a).
      feed_n 2 (H1); [ by rewrite in_cons; apply/orP; left | by done | ].
      move: (EqLeq
               (F1 a) (\sum_(j <- xs | P j) F1 j)
               (F2 a) (\sum_(j <- xs | P j) F2 j) H2 H1) => Q.
        by apply/eqP; rewrite eqn_leq; apply/andP; split.
    }
  Qed.

  (* We prove that the sum of Δ ones is equal to Δ. *)
  Lemma sum_of_ones:
    forall t Δ,
      \sum_(t <= x < t + Δ) 1 = Δ. 
  Proof.
    intros.
    rewrite big_const_nat iter_addn_0 mul1n.
    rewrite addnC -addnBA; last by done.
      by rewrite subnn addn0.  
  Qed.

  (* We show that the fact that the sum is smaller than the range 
     of the summation implies the existence of a zero element. *)
  Lemma sum_le_summation_range :
    forall f t Δ,
      \sum_(t <= x < t + Δ) f x < Δ ->
      exists x, t <= x < t + Δ /\ f x = 0.
  Proof.
    induction Δ; intros; first by rewrite ltn0 in H.
    destruct (f (t + Δ)) eqn: EQ.
    { exists (t + Δ); split; last by done.
        by apply/andP; split; [rewrite leq_addr | rewrite addnS ltnS].
    }
    { move: H; rewrite addnS big_nat_recr //= ?leq_addr // EQ addnS ltnS; move => H.
      feed IHΔ.
      { by apply leq_ltn_trans with (\sum_(t <= i < t + Δ) f i + n); first rewrite leq_addr. }
      move: IHΔ => [z [/andP [LE GE] ZERO]].
      exists z; split; last by done.
      apply/andP; split; first by done.
        by rewrite ltnS ltnW.
    }
  Qed.
  
End ExtraLemmas.

(* Lemmas about arithmetic with sums. *)
Section SumArithmetic.

  Lemma sum_seq_diff:
    forall (T:eqType) (rs: seq T) (F G : T -> nat),
      (forall i : T, i \in rs -> G i <= F i) ->
      \sum_(i <- rs) (F i - G i) = \sum_(i <- rs) F i - \sum_(i <- rs) G i.
  Proof.
    intros.
    induction rs; first by rewrite !big_nil subn0. 
    rewrite !big_cons subh2.
    - apply/eqP; rewrite eqn_add2l; apply/eqP; apply IHrs.
        by intros; apply H; rewrite in_cons; apply/orP; right.
    - by apply H; rewrite in_cons; apply/orP; left.
    - rewrite big_seq_cond [in X in _ <= X]big_seq_cond.
      rewrite leq_sum //; move => i /andP [IN _].
        by apply H; rewrite in_cons; apply/orP; right.
  Qed.
  
  Lemma sum_diff:
    forall n F G,
      (forall i (LT: i < n), F i >= G i) ->
      \sum_(0 <= i < n) (F i - G i) =
      (\sum_(0 <= i < n) (F i)) - (\sum_(0 <= i < n) (G i)).       
  Proof.
    intros n F G ALL.
    rewrite sum_seq_diff; first by done.
    move => i; rewrite mem_index_iota; move => /andP [_ LT].
      by apply ALL.
  Qed.

  Lemma sum_pred_diff:
    forall (T: eqType) (rs: seq T) (P: T -> bool) (F: T -> nat),
      \sum_(r <- rs | P r) F r =
      \sum_(r <- rs) F r - \sum_(r <- rs | ~~ P r) F r.
  Proof.
    clear; intros.
    induction rs; first by rewrite !big_nil subn0.
    rewrite !big_cons !IHrs; clear IHrs.
    case (P a); simpl; last by rewrite subnDl.
    rewrite addnBA; first by done.
    rewrite big_mkcond leq_sum //.
    intros t _.
      by case (P t).
  Qed.
  
End SumArithmetic.