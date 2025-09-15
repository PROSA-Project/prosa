From mathcomp Require Export ssreflect ssrbool eqtype ssrnat div seq path fintype bigop.

(** In this section, we define and prove facts about subadditivity and
    subadditive functions. The definition of subadditivity presented here
    slightly differs from the standard one ([f (a + b) <= f a + f b] for any
    [a] and [b]), but it is proven to be equivalent to it. *)
Section Subadditivity.

  (** First, we define subadditivity as a point-wise property; i.e., [f] is
      subadditive at [h] if standard subadditivity holds for any pair [(a,b)]
      that sums to [h]. *)
  Definition subadditive_at f h :=
    forall a b,
      a + b = h ->
      f h <= f a + f b.

  (** Second, we define the concept of partial subadditivity until a certain
      horizon [h]. This definition is useful when dealing with finite sequences. *)
  Definition subadditive_until f h :=
    forall x,
      x < h ->
      subadditive_at f x.

  (** Finally, give a definition of subadditive function: [f] is subadditive
      when it is subadditive at any point [h].*)
  Definition subadditive f :=
    forall h,
      subadditive_at f h.

  (** In this section, we show that the proposed definition of subadditivity is
      equivalent to the standard one. *)
  Section EquivalenceWithStandardDefinition.

    (** First, we give a standard definition of subadditivity. *)
    Definition subadditive_standard f :=
      forall a b,
        f (a + b) <= f a + f b.

    (** Then, we prove that the two definitions are implied by each other. *)
    Lemma subadditive_standard_equivalence :
      forall f,
        subadditive f <-> subadditive_standard f.
    Proof.
      split.
      - move=> SUB a b.
        by apply SUB.
      - move=> SUB h a b AB.
        rewrite -AB.
        by apply SUB.
    Qed.

  End EquivalenceWithStandardDefinition.

  (** In the following section, we prove some useful facts about subadditivity. *)
  Section Facts.

    (** Consider a function [f]. *)
    Variable f : nat -> nat.

    (** In this section, we show some of the properties of subadditive functions. *)
    Section SubadditiveFunctions.

      (** Assume that [f] is subadditive. *)
      Hypothesis h_subadditive : subadditive f.

      (** Then, we prove that moving any non-zero factor [m] outside of the arguments
          of [f] leads to a bigger or equal number. *)
      Lemma subadditive_leq_mul :
        forall n m,
          0 < m ->
          f (m * n) <= m * f n.
      Proof.
        move=> n [// | m] _.
        elim: m => [ | m IHm]; first by rewrite !mul1n.
        rewrite mulSnr [X in _ <= X]mulSnr.
        move: IHm; rewrite -(leq_add2r (f n)).
        exact /leq_trans/h_subadditive.
      Qed.

    End SubadditiveFunctions.

  End Facts.

End Subadditivity.

