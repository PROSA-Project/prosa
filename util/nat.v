Require Export prosa.util.tactics prosa.util.ssromega.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

(* Additional lemmas about natural numbers. *)
Section NatLemmas.

  Lemma subh1 :
    forall m n p,
      m >= n ->
      m - n + p = m + p - n.
  Proof. by ins; ssromega. Qed.

  Lemma subh2 :
    forall m1 m2 n1 n2,
      m1 >= m2 ->
      n1 >= n2 ->
      (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2).
  Proof. by ins; ssromega. Qed.
  
  Lemma subh3:
    forall m n p,
      m + p <= n ->
      m <= n - p.
  Proof.
    clear.
    intros.
    rewrite <- leq_add2r with (p := p).
    rewrite subh1 //.
    - by rewrite -addnBA // subnn addn0.
    - by apply leq_trans with (m+p); first rewrite leq_addl.
  Qed.

  (* Simplify [n + a - b + b - a = n] if [n >= b]. *)
  Lemma subn_abba:
    forall n a b,
      n >= b ->
      n + a - b + b - a = n.
  Proof.
    move=> n a b le_bn.
    rewrite subnK;
      first by rewrite -addnBA // subnn addn0 //.
    rewrite -[b]addn0.
    apply leq_trans with (n := n + 0); rewrite !addn0 //.
    apply leq_addr.
  Qed.

  Lemma add_subC:
    forall a b c,
      a >= c ->
      b >=c ->
      a + (b - c ) = a - c + b.
  Proof.
    intros* AgeC BgeC.
    induction b;induction c;intros;try ssromega.
  Qed.

  (* TODO: remove when mathcomp minimum required version becomes 1.10.0 *)
  Lemma ltn_subLR:
    forall a b c,
      a - c < b ->
      a < b + c.
  Proof.
    intros* AC. ssromega.
  Qed.

  (* We can drop additive terms on the lesser side of an inequality. *)
  Lemma leq_addk:
    forall m n k,
      n + k <= m ->
      n <= m.
  Proof.
    move=> m n p.
    apply leq_trans.
    by apply leq_addr.
  Qed.

End NatLemmas.

Section Interval.

  (* Trivially, points before the start of an interval, or past the end of an
     interval, are not included in the interval. *)
  Lemma point_not_in_interval:
    forall t1 t2 t',
      t2 <= t' \/ t' < t1 ->
      forall t,
        t1 <= t < t2
        -> t <> t'.
  Proof.
    move=> t1 t2 t' EXCLUDED t /andP [GEQ_t1 LT_t2] EQ.
    subst.
    case EXCLUDED => [INEQ | INEQ];
      eapply leq_ltn_trans in INEQ; eauto;
      by rewrite ltnn in INEQ.
  Qed.

End Interval.

Section NatOrderLemmas.

  (* Mimic the way implicit arguments are used in [ssreflect]. *)
  Set Implicit Arguments.
  Unset Strict Implicit.

  (* [ltn_leq_trans]: Establish that [m < p] if [m < n] and [n <= p], to mirror the
     lemma [leq_ltn_trans] in [ssrnat].

     NB: There is a good reason for this lemma to be "missing" in [ssrnat] --
     since [m < n] is defined as [m.+1 <= n], [ltn_leq_trans] is just
     [m.+1 <= n -> n <= p -> m.+1 <= p], that is [@leq_trans n m.+1 p].

     Nonetheless we introduce it here because an additional (even though
     arguably redundant) lemma doesn't hurt, and for newcomers the apparent
     absence of the mirror case of [leq_ltn_trans] can be somewhat confusing.  *)
  Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p.
  Proof. exact (@leq_trans n m.+1 p). Qed.

End NatOrderLemmas.
