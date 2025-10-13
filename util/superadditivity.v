From mathcomp Require Export ssreflect ssrbool eqtype ssrnat div seq path fintype bigop.
Require Export prosa.util.nat prosa.util.rel prosa.util.list.

(** In the following, we define and prove facts about superadditivity and
    superadditive functions. The definition of superadditivity presented here
    slightly differs from the standard one ([f a + f b <= f (a + b)] for any
    [a] and [b]), but it is proven to be equivalent to it. *)

  (** First, we define subadditivity as a point-wise property; i.e., [f] is
      subadditive at [h] if standard subadditivity holds for any pair [(a,b)]
      that sums to [h]. *)
Definition superadditive_at f h :=
  forall a b,
    a + b = h ->
    f a + f b <= f h.

(** Second, we define the concept of partial subadditivity until a certain
    horizon [h]. This definition is useful when dealing with finite sequences. *)
Definition superadditive_until f h :=
  forall x,
    x < h ->
    superadditive_at f x.

(** Finally, give a definition of subadditive function: [f] is subadditive
    when it is subadditive at any point [h].*)
Definition superadditive f :=
  forall h,
    superadditive_at f h.

(** We show that the proposed definition of subadditivity is equivalent to the
    standard one. *)

(** To this end, we first give a standard definition of subadditivity. *)
Definition superadditive_standard f :=
  forall a b,
    f a + f b <= f (a + b).

(** Then, we prove that the two definitions are implied by each other. *)
Lemma superadditive_standard_equivalence :
  forall f,
    superadditive f <-> superadditive_standard f.
Proof.
  split.
  - move=> SUPER a b.
    by apply SUPER.
  - move=> SUPER h a b AB.
    rewrite -AB.
    by apply SUPER.
Qed.

(** In the following section, we prove some useful facts about superadditivity. *)
Section Facts.

  (** Consider a function [f]. *)
  Variable f : nat -> nat.

  (** First, we show that if [f] is superadditive in zero, then its value in zero must
      also be zero. *)
  Lemma superadditive_first_zero :
    superadditive_at f 0 ->
    f 0 = 0.
  Proof.
    move => SUPER.
    destruct (f 0) eqn:Fx; first by done.
    specialize (SUPER 0 0 (addn0 0)).
    contradict SUPER.
    apply /negP; rewrite -ltnNge.
    by lia.
  Qed.

  (** In this section, we show some of the properties of superadditive functions. *)
  Section SuperadditiveFunctions.

    (** Assume that [f] is superadditive. *)
    Hypothesis h_superadditive : superadditive f.

    (** First, we show that [f] must also be monotone. *)
    Lemma superadditive_monotone :
      monotone leq f.
    Proof.
      move=> x y LEQ.
      apply leq_trans with (f x + f (y - x)).
      - by lia.
      - apply h_superadditive.
        by lia.
    Qed.

    (** Next, we prove that moving any factor [m] outside of the arguments
        of [f] leads to a smaller or equal number. *)
    Lemma superadditive_leq_mul :
      forall n m,
        m * f n <= f (m * n).
    Proof.
      move=> n m.
      elim: m=> [| m IHm]; first by lia.
      rewrite !mulSnr.
      apply leq_trans with (f (m * n) + f n).
      - by rewrite leq_add2r.
      - by apply h_superadditive.
    Qed.

    (** In the next section, we show that any superadditive function that is not
        the zero constant function (i.e., [f x = 0] for any [x]) is forced to grow
        beyond any finite limit. *)
    Section NonZeroSuperadditiveFunctions.

      (** Assume that [f] is not the zero constant function ... *)
      Hypothesis h_non_zero : exists n, f n > 0.

      (** ... then, [f] will eventually grow larger than any number. *)
      Lemma superadditive_unbounded :
        forall t, exists n', t <= f n'.
      Proof.
        move=> t.
        move: h_non_zero => [n LT_n].
        exists (t * n).
        apply leq_trans with (t * f n).
        - by apply leq_pmulr.
        - by apply superadditive_leq_mul.
      Qed.

    End NonZeroSuperadditiveFunctions.

  End SuperadditiveFunctions.

End Facts.

(** In this section, we present the define and prove facts about the minimal
    superadditive extension of superadditive functions. Given a prefix of a
    function, there are many ways to continue the function in order to maintain
    superadditivity. Among these possible extrapolations, there always exists
    a minimal one. *)
Section MinimalExtensionOfSuperadditiveFunctions.

  (** Consider a function [f]. *)
  Variable f : nat -> nat.

  (** First, we define what it means to find the minimal extension once a horizon
      is specified. *)
  Section Definitions.

    (** Consider a horizon [h].. *)
    Variable h : nat.

    (** Then, the minimal superadditive extension will be the maximum sum over
        the pairs that sum to [h]. Note that, in this formula, there are two
        important edge cases: both [h=0] and [h=1], the sequence of valid sums
        will be empty, so their maximum will be [0]. In both cases, the extrapolation
        is nonetheless correct. *)
    Definition minimal_superadditive_extension :=
      max0 [seq f a + f (h-a) | a <- index_iota 1 h].

  End Definitions.

  (** In the following section, we prove some facts about the minimal superadditive
      extension. Note that we currently do not prove that the implemented
      extension is minimal. However, we plan to add this fact in the future. The following
      discussion provides useful information on the subject, including its connection with
      Network Calculus:
      https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/merge_requests/127#note_64177 *)
  Section Facts.

    (** Consider a horizon [h] ... *)
    Variable h : nat.

    (** ... and assume that we know [f] to be superadditive until [h]. *)
    Hypothesis h_superadditive_until : superadditive_until f h.

    (** Moreover, consider a second function, [f'], which is equivalent to
        [f] in all of its points except for [h], in which its value is exactly
        the superadditive extension of [f] in [h]. *)
    Variable f' : nat -> nat.
    Hypothesis h_f'_min_extension :
      forall t,
        f' t = if t == h
               then minimal_superadditive_extension h
               else f t.

    (** First, we prove that [f'] is superadditive also in [h]. *)
    Theorem minimal_extension_superadditive_at_horizon :
      superadditive_at f' h.
    Proof.
      move => a b SUM.
      rewrite !h_f'_min_extension.
      rewrite -SUM.
      destruct a as [|a'] eqn:EQa; destruct b as [|b'] eqn:EQb => //=.
      { rewrite add0n eq_refl superadditive_first_zero; first by rewrite add0n.
        by apply h_superadditive_until; lia. }
      { rewrite addn0 eq_refl superadditive_first_zero; first by rewrite addn0.
        by apply h_superadditive_until; lia. }
      { rewrite -!EQa -!EQb eq_refl //=.
        rewrite -{1}(addn0 a) eqn_add2l {1}EQb //=.
        rewrite -{1}(add0n b) eqn_add2r {2}EQa //=.
        rewrite /minimal_superadditive_extension.
        apply in_max0_le.
        apply /mapP; exists a.
        - by rewrite mem_iota; lia.
        - by have -> : a + b - a = b by lia. }
    Qed.

    (** And finally, we prove that [f'] is superadditive until [h.+1]. *)
    Lemma minimal_extension_superadditive_until :
      superadditive_until f' h.+1.
    Proof.
      move=> t LEQh a b SUM.
      destruct (ltngtP t h) as [LT | GT | EQ].
      - rewrite !h_f'_min_extension.
        rewrite !ltn_eqF; try lia.
        by apply h_superadditive_until.
      - by lia.
      - rewrite EQ in SUM; rewrite EQ.
        by apply minimal_extension_superadditive_at_horizon.
    Qed.

  End Facts.

End MinimalExtensionOfSuperadditiveFunctions.

