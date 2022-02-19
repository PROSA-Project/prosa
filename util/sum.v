From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

Require Export prosa.util.notation.
Require Export prosa.util.rel.
Require Export prosa.util.nat.

(* TODO: PR MathComp *)
Lemma leq_sum_subseq (I : eqType) (r r' : seq I) (P : pred I) (F : I -> nat) :
  subseq r r' -> \sum_(i <- r | P i) F i <= \sum_(i <- r' | P i) F i.
Proof.
elim: r r' => [|x r IH] r'; first by rewrite big_nil.
elim: r' => [//|x' r' IH'] /=; have [<- /IH {}IH|_ /IH' {}IH'] := eqP.
  by rewrite !big_cons; case: (P x); rewrite // leq_add2l.
rewrite [X in _ <= X]big_cons; case: (P x') => //.
exact: leq_trans (leq_addl _ _).
Qed.

Section SumsOverSequences.

  (** Consider any type [I] with a decidable equality ... *)
  Variable (I : eqType).

  (** ... and assume we are given a sequence ... *)
  Variable (r : seq I).

  (** ... and a predicate [P]. *)
  Variable (P : pred I).

  (** First, we will show some properties of the sum performed over a single function
      yielding natural numbers. *)
  Section SumOfOneFunction.

    (** Consider any function that yields natural numbers... *)
    Variable (F : I -> nat).

    (** We start showing that having every member of [r] equal to zero is equivalent to
        having the sum of all the elements of [r] equal to zero, and vice-versa. *)
    (* TODO: PR MathComp
       this should probably be named sum_nat_eq0,
       but there is already a sum_nat_eq0 that is less generic? *)
    Lemma sum_nat_eq0_nat :
      (\sum_(i <- r | P i) F i == 0) = all (fun x => F x == 0) [seq x <- r | P x].
    Proof.
      elim: r => [|x r' IH]; rewrite ?big_nil//= big_cons.
      by case: ifP; rewrite ?addn_eq0 IH.
    Qed.

    (** In the same way, if at least one element of [r] is not zero, then the sum of all
        elements of [r] must be strictly positive, and vice-versa. *)
    (* TODO: PR MathComp *)
    Lemma sum_nat_gt0 :
      (0 < \sum_(i <- r | P i) F i) = has (fun x => 0 < F x) [seq x <- r | P x].
    Proof.
      apply/negb_inj; rewrite lt0n negbK sum_nat_eq0_nat -all_predC.
      by apply/eq_all => ?; rewrite /= lt0n negbK.
    Qed.

    (** Next, we show that if a number [a] is not contained in [r], then filtering or not
        filtering [a] when summing leads to the same result. *)
    Lemma sum_notin_rem_eqn a :
      a \notin r ->
      \sum_(x <- r | P x && (x != a)) F x = \sum_(x <- r | P x) F x.
    Proof.
      move=> a_notin_r; rewrite [LHS]big_seq_cond [RHS]big_seq_cond.
      apply: eq_bigl => x; case xinr: (x \in r) => //=.
      have [xa|] := eqP; last by rewrite andbT.
      by move: xinr a_notin_r; rewrite xa => ->.
    Qed.

    (** We prove that if any element of [r] is bounded by constant [c],
        then the sum of the whole set is bounded by [c * size r]. *)
    Lemma sum_majorant_constant c :
      (forall a, a \in r -> P a -> F a <= c) ->
      \sum_(j <- r | P j) F j <= c * (size [seq j <- r | P j]).
    Proof.
      move=> Fa_le_c.
      rewrite -sum1_size big_filter big_distrr/= muln1.
      rewrite big_seq_cond [X in _ <= X]big_seq_cond.
      apply: leq_sum => i /andP[ir Pi]; exact: Fa_le_c.
    Qed.

    (** Next, we show that the sum of the elements in [r] respecting [P] can
        be obtained by removing from the total sum over [r] the sum of the elements
        in [r] not respecting [P]. *)
    Lemma sum_pred_diff:
      \sum_(r <- r | P r) F r = \sum_(r <- r) F r - \sum_(r <- r | ~~ P r) F r.
    Proof. by rewrite [X in X - _](bigID P)/= addnK. Qed.

    (** Summing natural numbers over a superset can only yields a greater sum.
        Requiring the absence of duplicate in [r] is a simple way to
        guarantee that the set inclusion [r <= rs] implies the actually
        required multiset inclusion. *)
    (* TODO: PR MathComp
       - add a condition P i *)
    Lemma leq_sum_sub_uniq (rs : seq I) :
      uniq r -> {subset r <= rs} ->
      \sum_(i <- r) F i <= \sum_(i <- rs) F i.
    Proof.
      move=> uniq_r sub_r_rs.
      rewrite [X in _ <= X](bigID (fun x => x \in r))/=.
      apply: leq_trans (leq_addr _ _).
      rewrite (perm_big (undup [seq x <- rs | x \in r])).
      - rewrite -filter_undup big_filter_cond/=.
        under eq_bigl => ? do rewrite andbT; exact/leq_sum_subseq/undup_subseq.
      - apply: uniq_perm; rewrite ?undup_uniq// => x.
        rewrite mem_undup mem_filter.
        by case xinr: (x \in r); rewrite // (sub_r_rs _ xinr).
    Qed.

  End SumOfOneFunction.
  
  (** In this section, we show some properties of the sum performed over two different functions. *)
  Section SumOfTwoFunctions.

    (** Consider three functions that yield natural numbers. *)
    Variable (E E1 E2 : I -> nat).

    (** Besides earlier introduced predicate [P], we add two additional predicates [P1] and [P2]. *)
    Variable (P1 P2 : pred I).

    (** Assume that [E2] dominates [E1] in all the points contained in the set [r] and respecting
        the predicate [P]. We prove that, if we sum both function over those points, then the sum
        of [E2] will dominate the sum of [E1]. *)
    (* TODO: PR MathComp *)
    Lemma leq_sum_seq :
      (forall i, i \in r -> P i -> E1 i <= E2 i) ->
      \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
    Proof.
      move=> le; rewrite big_seq_cond [X in _ <= X]big_seq_cond.
      apply: leq_sum => i /andP[]; exact: le.
    Qed.

    (** In the same way, if [E1] equals [E2] in all the points considered above, then also the two
        sums will be identical. *)
    (* TODO: PR MathComp
       - generalize as eq_big_seq_cond (nothing specific to addn here)
       - replace == with = ? *)
    Lemma eq_sum_seq:
      (forall i, i \in r -> P i -> E1 i == E2 i) ->
      \sum_(i <- r | P i) E1 i == \sum_(i <- r | P i) E2 i.
    Proof.
      move=> eqE; apply/eqP; rewrite -big_filter -[RHS]big_filter.
      apply: eq_big_seq => x; rewrite mem_filter => /andP[Px xr]; exact/eqP/eqE.
    Qed.

    (** Assume that [P1] implies [P2] in all the points contained in
        the set [r]. We prove that, if we sum both functions over those
        points, then the sum of [E] conditioned by [P2] will dominate
        the sum of [E] conditioned by [P1]. *)
    (* TODO: PR MathComp
       - maybe leq_sum_seq above should be leq_sum_seqr and this one leq_sum_seql *)
    Lemma leq_sum_seq_pred:
      (forall i, i \in r -> P1 i -> P2 i) ->
      \sum_(i <- r | P1 i) E i <= \sum_(i <- r | P2 i) E i.
    Proof.
      move=> imp; rewrite [X in _ <= X](bigID P1)/=.
      rewrite big_seq_cond [X in _ <= X + _]big_seq_cond.
      rewrite (eq_bigl (fun i => [&& i \in r, P2 i & P1 i])) ?leq_addr// => i.
      by case ir: (i \in r); case P1i: (P1 i); rewrite ?andbF //= (imp i).
    Qed.

  End SumOfTwoFunctions.

End SumsOverSequences.

(** We continue establishing properties of sums over sequences, but start a new
    section here because some of the below proofs depend lemmas in the preceding
    section in their full generality. *)
Section SumsOverSequences.

  (** Consider any type [I] with a decidable equality ... *)
  Variable (I : eqType).

  (** ... and assume we are given a sequence ... *)
  Variable (r : seq I).

  (** ... and a predicate [P]. *)
  Variable (P : pred I).

  (** Consider two functions that yield natural numbers. *)
  Variable (E1 E2 : I -> nat).

  (** First, as an auxiliary lemma, we observe that, if [E1 j] is less than [E2
      j] for some element [j] involved in a summation (filtered by [P]), then
      the corresponding totals are not equal. *)
  Lemma ltn_sum_leq_seq j :
    j \in r ->
    P j ->
    E1 j < E2 j ->
    (forall i, i \in r -> P i -> E1 i <= E2 i) ->
    \sum_(x <- r | P x) E1 x < \sum_(x <- r | P x) E2 x.
  Proof.
    move=> jr Pj ltj le.
    rewrite (big_rem j)// [X in _ < X](big_rem j)//= Pj -addSn leq_add//.
    apply: leq_sum_seq => i /mem_rem; exact: le.
  Qed.

  (** Next, we prove that if for any element i of a set [r] the following two
      statements hold (1) [E1 i] is less than or equal to [E2 i] and (2) the sum
      [E1 x_1, ..., E1 x_n] is equal to the sum of [E2 x_1, ..., E2 x_n], then
      [E1 x] is equal to [E2 x] for any element x of [xs]. *)
  Lemma eq_sum_leq_seq :
    (forall i, i \in r -> P i -> E1 i <= E2 i) ->
    \sum_(x <- r | P x) E1 x == \sum_(x <- r | P x) E2 x
      = all (fun x => E1 x == E2 x) [seq x <- r | P x].
  Proof.
    move=> le; rewrite all_filter; case aE: all.
    apply: eq_sum_seq => i ir Pi; move: aE => /allP/(_ i ir)/implyP; exact.
    have [j /andP[jr Pj] ltj] : exists2 j, (j \in r) && P j & E1 j < E2 j.
    have /negbT := aE; rewrite -has_predC => /hasP[j jr /=].
    rewrite negb_imply => /andP[Pj neq].
    - by exists j; first exact/andP; rewrite ltn_neqAle neq le.
    - by apply/negbTE; rewrite neq_ltn (ltn_sum_leq_seq j).
  Qed.

End SumsOverSequences.

(** In this section, we prove a variety of properties of sums performed over ranges. *)
Section SumsOverRanges.

  (** First, we prove that the sum of Δ ones is equal to Δ     . *)
  Lemma sum_of_ones:
    forall t Δ,
      \sum_(t <= x < t + Δ) 1 = Δ.
  Proof. by move=> t Δ; rewrite big_const_nat iter_addn_0 mul1n addKn. Qed.

  (** Next, we show that a sum of natural numbers equals zero if and only
      if all terms are zero. *)
  Lemma big_nat_eq0 m n F:
    \sum_(m <= i < n) F i = 0 <-> (forall i, m <= i < n -> F i = 0).
  Proof.
    split.
    - rewrite /index_iota => /eqP.
      rewrite sum_nat_eq0_nat filter_predT => /allP ZERO i.
      rewrite -mem_index_iota /index_iota => IN.
      by apply/eqP; apply ZERO.
    - move=> ZERO.
      have-> : \sum_(m <= i < n) F i = \sum_(m <= i < n) 0 by apply eq_big_nat.
      exact: big1_eq.
  Qed.

  (** Moreover, the fact that the sum is smaller than the range of the summation
      implies the existence of a zero element. *)
  Lemma sum_le_summation_range:
    forall f t Δ,
      \sum_(t <= x < t + Δ) f x < Δ ->
      exists x, t <= x < t + Δ /\ f x = 0.
  Proof.
    move=> f t; elim=> [|Δ IHΔ] H; first by rewrite ltn0 in H.
    destruct (f (t + Δ)) as [|n] eqn: EQ.
    { exists (t + Δ); split; last by done.
      by apply/andP; split; [rewrite leq_addr | rewrite addnS ltnS]. }
    { move: H; rewrite addnS big_nat_recr //= ?leq_addr // EQ addnS ltnS; move => H.
      have {}/IHΔ [z [/andP[LE GE] ZERO]] : \sum_(t <= t' < t + Δ) f t' < Δ.
      { by apply leq_ltn_trans with (\sum_(t <= i < t + Δ) f i + n); first rewrite leq_addr. }
      by exists z; split=> //; rewrite LE/= ltnS ltnW. }
  Qed.

  (** Next, we prove that the summing over the difference of two functions is
      the same as summing over the two functions separately, and then taking the
      difference of the two sums. Since we are using natural numbers, we have to
      require that one function dominates the other in the summing range. *)
  (* TODO: PR MathComp
     - add a condition P i *)
  Lemma sumnB_nat m n F G :
    (forall i, m <= i < n -> F i >= G i) ->
    \sum_(m <= i < n) (F i - G i) =
      (\sum_(m <= i < n) (F i)) - (\sum_(m <= i < n) (G i)).
  Proof.
    move=> le.
    rewrite big_nat_cond [X in X - _]big_nat_cond [X in _ - X]big_nat_cond.
    rewrite sumnB// => i; rewrite andbT; exact: le.
  Qed.

End SumsOverRanges.

(** In this section, we show how it is possible to equate the result of two sums performed
    on two different functions and on different intervals, provided that the two functions
    match point-wise. *)
Section SumOfTwoIntervals.

  (** Consider two equally-sized intervals <<[t1, t1+d)>> and <<[t2, t2+d)>>... *)
  Variable (t1 t2 : nat).
  Variable (d : nat).

  (** ...and two functions [F1] and [F2]. *)
  Variable (F1 F2 : nat -> nat).

  (** Assume that the two functions match point-wise with each other, with the points taken
      in their respective interval. *)
  Hypothesis equal_before_d: forall g, g < d -> F1 (t1 + g) = F2 (t2 + g).

  (** The then summations of [F1] over <<[t1, t1 + d)>> and [F2] over
      <<[t2, t2 + d)>> are equal. *)
  Lemma big_sum_eq_in_eq_sized_intervals:
    \sum_(t1 <= t < t1 + d) F1 t = \sum_(t2 <= t < t2 + d) F2 t.
  Proof.
    elim: d equal_before_d => [|n IHn] eq; first by rewrite !addn0 !big_geq.
    rewrite !addnS !big_nat_recr => //; try by lia.
    by rewrite IHn.
  Qed.

End SumOfTwoIntervals.


(** In this section, we relate the sum of items with the sum over partitions of those items. *)
Section SumOverPartitions.

  (** Consider an item type [X] and a partition type [Y]. *)
  Variable X Y : eqType.

  (** [x_to_y] is the mapping from an item to the partition it is contained in. *)
  Variable x_to_y : X -> Y.

  (** Consider [f], a function from [X] to [nat]. *)
  Variable f : X -> nat.

  (** Consider an arbitrary predicate [P] on [X]. *)
  Variable P : pred X.

  (** Consider a sequence of items [xs] and a sequence of partitions [ys]. *)
  Variable xs : seq X.
  Variable ys : seq Y.

  (** We assume that any item in [xs] has its corresponding partition in the sequence of partitions [ys]. *)
  Hypothesis H_no_partition_missing : forall x, x \in xs -> P x -> x_to_y x \in ys.

  (** Consider the sum of [f x] over all [x] in a given partition [y]. *)
  Let sum_of_partition y := \sum_(x <- xs | P x && (x_to_y x == y)) f x.

  (** We prove that summation of [f x] over all [x] is less than or equal to the summation of
      [sum_of_partition] over all partitions. *)
  Lemma sum_over_partitions_le :
    \sum_(x <- xs | P x) f x
    <= \sum_(y <- ys) sum_of_partition y.
  Proof.
    rewrite /sum_of_partition.
    induction xs as [| x' xs' LE_TAIL]; first by rewrite big_nil.
    have P_HOLDS: forall i j, true -> P j && (x_to_y j== i) -> P j by move=> ??? /andP [P_HOLDS _].
    have IN_ys: forall x : X, x \in xs' -> P x -> x_to_y x \in ys
      by move=> ??; apply H_no_partition_missing => //;  rewrite in_cons; apply /orP; right.
    move: LE_TAIL; rewrite (exchange_big_dep P) => //= LE_TAIL.
    rewrite (exchange_big_dep P) //= !big_cons.
    case PX: (P x') => //=.
    apply leq_add => //.
    rewrite big_const_seq iter_addn_0.
    apply leq_pmulr; rewrite -has_count.
    apply /hasP; eapply ex_intro2 => //.
    apply H_no_partition_missing => //.
    exact: mem_head.
  Qed.

  (** Consider a partition [y']. *)
  Variable y' : Y.

  (** We prove that the sum of items excluding all items from a partition [y']
      is less-than-or-equal to the sum over all partitions except [y']. *)
  Lemma reorder_summation : \sum_(x <- xs | P x && (x_to_y x != y')) f x <=
                \sum_(y <- ys | y != y') sum_of_partition y.
  Proof.
    rewrite (exchange_big_dep (fun x =>P x && (x_to_y x != y'))) //=.
    - rewrite  big_seq_cond [X in _ <= X]big_seq_cond.
      apply leq_sum => x' /andP [ARRo /andP [Px' NEQ]].
      rewrite (big_rem (x_to_y x')) //=.
      by rewrite Px' eq_refl NEQ andTb andTb leq_addr.
    - move => y_of_x' x' /negP NEQ /andP [EQ1 /eqP EQ2].
      rewrite EQ1 Bool.andb_true_l; apply/negP; intros CONTR.
      apply: NEQ; clear EQ1.
      by rewrite -EQ2.
  Qed.

  (** In this section, we prove a stronger result about the equality between
      the sum over all items and the sum over all partitions of those items. *)
  Section Equality.

    (** In order to prove the stronger result of equality, we additionally
        assume that the sequences [xs] and [ys] are sets, i.e., that each
        element is contained at most once. *)
    Hypothesis H_xs_unique : uniq xs.
    Hypothesis H_ys_unique : uniq ys.

    (** We prove that summation of [f x] over all [x] is equal to the summation of
      [sum_of_partition] over all partitions. *)
    Lemma sum_over_partitions_eq :
      \sum_(x <- xs | P x) f x
      = \sum_(y <- ys) sum_of_partition y.
    Proof.
      rewrite /sum_of_partition.
      induction xs as [|x' xs' LE_TAIL]; first by rewrite big_nil big1_seq //= => ??; rewrite big_nil.
      rewrite //= in LE_TAIL; feed_n 2 LE_TAIL.
      { by move => ??; apply H_no_partition_missing; rewrite in_cons; apply /orP; right. }
      { by move: H_xs_unique; rewrite cons_uniq => /andP [??]. }
      rewrite (exchange_big_dep P) //=; last by move=> ??? /andP[??].
      rewrite !big_cons.
      case PX: (P x'); last by rewrite LE_TAIL (exchange_big_dep P) //=;  move=> ??? /andP[??].
      have -> : \sum_(i <- ys | true && ( x_to_y x' == i)) f x' = f x'.
      { rewrite //= -big_filter.
        have -> : [seq i <- ys | x_to_y x' == i] = [:: x_to_y x']; last by rewrite unlock //= addn0.
        have -> : [seq i <- ys | x_to_y x' == i] = [seq i <- ys | i == x_to_y x'].
        { clear H_no_partition_missing LE_TAIL.
          induction ys as [| y'' ys' LE_TAILy]; first by done.
          feed LE_TAILy; first by move: H_ys_unique; rewrite cons_uniq => /andP [??].
          by rewrite //=  LE_TAILy //= eq_sym. }
        apply filter_pred1_uniq => //.
        apply H_no_partition_missing => //.
        by rewrite in_cons; apply /orP; left.
      }
      apply /eqP; rewrite eqn_add2l; apply /eqP.
      by rewrite LE_TAIL (exchange_big_dep P) //=;  move=> ??? /andP[??].
    Qed.

  End Equality.

End SumOverPartitions.

(** We observe a trivial monotonicity-preserving property with regard to
    [leq]. *)
Section Monotonicity.

  (** Consider any type of indices, any predicate, ... *)
  Variables (I : eqType) (P : pred I).

  (** ... and any function that maps each index to a [nat -> nat] function. *)
  Variable F : I -> nat -> nat.

  (** Consider any set of indices ... *)
  Variable r : seq I.

  (** ... and suppose that [F i] is monotonic with regard to [leq] for every
      index in [r]. *)
  Hypothesis H_mono : forall i, i \in r -> monotone leq (F i).

  (** Consider the sum of [F] over [r], for any given [x]. *)
  Let f x := \sum_(i <- r | P i) F i x.

  (** We note that this sum [f] is monotonic with regard to [leq] in [x]. *)
  Lemma sum_leq_mono :
    monotone leq f.
  Proof.
    move=> x y LEQ.
    rewrite /f big_seq_cond [in X in _ <= X]big_seq_cond.
    apply: leq_sum => i /andP [IN _].
    by apply: H_mono.
  Qed.

End Monotonicity.
