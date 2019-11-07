From rt.util Require Import tactics notation sorting nat ssromega.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(* Lemmas about sum. *)
Section ExtraLemmas.
  
  Lemma extend_sum :
    forall t1 t2 t1' t2' F,
      t1' <= t1 ->
      t2 <= t2' ->
      \sum_(t1 <= t < t2) F t <= \sum_(t1' <= t < t2') F t.
  Proof.
    intros t1 t2 t1' t2' F LE1 LE2.
    destruct (t1 <= t2) eqn:LE12;
      last by apply negbT in LE12; rewrite -ltnNge in LE12; rewrite big_geq // ltnW.
    rewrite -> big_cat_nat with (m := t1') (n := t1); try (by done); simpl;
      last by apply leq_trans with (n := t2).
    rewrite -> big_cat_nat with (p := t2') (n := t2); try (by done); simpl.
      by rewrite addnC -addnA; apply leq_addr.
  Qed.

  Lemma leq_sum_nat m n (P : pred nat) (E1 E2 : nat -> nat) :
    (forall i, m <= i < n -> P i -> E1 i <= E2 i) ->
    \sum_(m <= i < n | P i) E1 i <= \sum_(m <= i < n | P i) E2 i.
  Proof.
    intros LE.
    rewrite big_nat_cond [\sum_(_ <= _ < _| P _)_]big_nat_cond.
      by apply leq_sum; move => j /andP [IN H]; apply LE.
  Qed.

  Lemma leq_sum_seq (I: eqType) (r: seq I) (P : pred I) (E1 E2 : I -> nat) :
    (forall i, i \in r -> P i -> E1 i <= E2 i) ->
    \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
  Proof.
    intros LE.
    rewrite big_seq_cond [\sum_(_ <- _| P _)_]big_seq_cond.
      by apply leq_sum; move => j /andP [IN H]; apply LE.
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
  
  Lemma leq_sum1_smaller_range m n (P Q: pred nat) a b:
    (forall i, m <= i < n /\ P i -> a <= i < b /\ Q i) ->
    \sum_(m <= i < n | P i) 1 <= \sum_(a <= i < b | Q i) 1.
  Proof.
    intros REDUCE.
    rewrite big_mkcond.
    apply leq_trans with (n := \sum_(a <= i < b | Q i) \sum_(m <= i' < n | i' == i) 1).
    {
      rewrite (exchange_big_dep (fun x => true)); [simpl | by done].
      apply leq_sum_nat; intros i LE _.
      case TRUE: (P i); last by done.
      move: (REDUCE i (conj LE TRUE)) => [LE' TRUE'].
      rewrite (big_rem i); last by rewrite mem_index_iota.
        by rewrite TRUE' eq_refl.
    }
    {
      apply leq_sum_nat; intros i LE TRUE.
      rewrite big_mkcond /=.
      destruct (m <= i < n) eqn:LE'; last first.
      {
        rewrite big_nat_cond big1; first by done.
        move => i' /andP [LE'' _]; case EQ: (_ == _); last by done.
          by move: EQ => /eqP EQ; subst; rewrite LE'' in LE'.
      }
      rewrite (bigD1_seq i) /=; [ | by rewrite mem_index_iota | by rewrite iota_uniq ].
      rewrite eq_refl big1; first by done.
        by move => i' /negbTE NEQ; rewrite NEQ.
    }
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

  Lemma leq_pred_sum:
    forall (T:eqType) (r: seq T) (P1 P2: pred T) F, 
      (forall i, P1 i -> P2 i) ->
      \sum_(i <- r | P1 i) F i <=
      \sum_(i <- r | P2 i) F i.
  Proof.
    intros.
    rewrite big_mkcond [in X in _ <= X]big_mkcond//= leq_sum //.
    intros i _. 
    destruct P1 eqn:P1a; destruct P2 eqn:P2a; try done. 
    exfalso.
    move: P1a P2a => /eqP P1a /eqP P2a.
    rewrite eqb_id in P1a; rewrite eqbF_neg in P2a.
    move: P2a => /negP P2a.
      by apply P2a; apply H.
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

  (* We prove that if any element of a set r is bounded by constant const, 
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

  (* We prove that if for any element x of a set xs the following two statements hold 
     (1) [F1 x] is less than or equal to [F2 x] and (2) the sum [F1 x_1, ..., F1 x_n] 
     is equal to the sum of [F2 x_1, ..., F2 x_n], then [F1 x] is equal to [F2 x] for 
     any element x of xs. *)
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
  
  Lemma telescoping_sum :
    forall (T: Type) (F: T->nat) r (x0: T),
      (forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)) ->
      F (nth x0 r (size r).-1) - F (nth x0 r 0) =
      \sum_(0 <= i < (size r).-1) (F (nth x0 r (i.+1)) - F (nth x0 r i)).
  Proof.
    intros T F r x0 ALL.
    have ADD1 := big_add1.
    have RECL := big_nat_recl.
    specialize (ADD1 nat 0 addn 0 (size r) (fun x => true) (fun i => F (nth x0 r i))).
    specialize (RECL nat 0 addn (size r).-1 0 (fun i => F (nth x0 r i))).
    rewrite sum_diff; last by ins.
    rewrite addmovr; last by rewrite -[_.-1]add0n; apply prev_le_next; try rewrite add0n leqnn.
    rewrite subh1; last by apply leq_sum_nat; move => i /andP [_ LT] _; apply ALL.
    rewrite addnC -RECL //.
    rewrite addmovl; last by rewrite big_nat_recr // -{1}[\sum_(_ <= _ < _) _]addn0; apply leq_add.
      by rewrite addnC -big_nat_recr.
  Qed.

  Lemma leq_sum_sub_uniq :
    forall (T: eqType) (r1 r2: seq T) F,
      uniq r1 ->
      {subset r1 <= r2} ->
      \sum_(i <- r1) F i <= \sum_(i <- r2) F i.
  Proof.
    intros T r1 r2 F UNIQ SUB; generalize dependent r2.
    induction r1 as [| x r1' IH]; first by ins; rewrite big_nil.
    {
      intros r2 SUB.
      assert (IN: x \in r2).
        by apply SUB; rewrite in_cons eq_refl orTb.
        simpl in UNIQ; move: UNIQ => /andP [NOTIN UNIQ]; specialize (IH UNIQ).
        destruct (splitPr IN).
        rewrite big_cat 2!big_cons /= addnA [_ + F x]addnC -addnA leq_add2l.
        rewrite mem_cat in_cons eq_refl in IN.
        rewrite -big_cat /=.
        apply IH; red; intros x0 IN0.
        rewrite mem_cat.
        feed (SUB x0); first by rewrite in_cons IN0 orbT.
        rewrite mem_cat in_cons in SUB.
        move: SUB => /orP [SUB1 | /orP [/eqP EQx | SUB2]];
                       [by rewrite SUB1 | | by rewrite SUB2 orbT].
          by rewrite -EQx IN0 in NOTIN.
    }
  Qed.
  
End SumArithmetic.