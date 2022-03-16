From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.
Require Export mathcomp.zify.zify.

Require Export prosa.util.tactics.

(** Additional lemmas about natural numbers. *)
Section NatLemmas.

  (** First, we show that, given [m1 >= m2] and [n1 >= n2], an
      expression [(m1 + n1) - (m2 + n2)] can be transformed into
      expression [(m1 - m2) + (n1 - n2)]. *)
  Lemma subnD:
    forall m1 m2 n1 n2,
      m1 >= m2 ->
      n1 >= n2 ->
      (m1 + n1) - (m2 + n2) = (m1 - m2) + (n1 - n2).
  Proof. by ins; lia. Qed.
  
  (** Next, we show that [m + p <= n] implies that [m <= n - p]. Note
      that this lemma is similar to ssreflect's lemma [leq_subRL];
      however, the current lemma has no precondition [n <= p], since it
      has only one direction. *)
  Lemma leq_subRL_impl:
    forall m n p,
      m + n <= p ->
      m <= p - n.
  Proof. by intros; lia. Qed.
    
  (** Simplify [n + a - b + b - a = n] if [n >= b]. *)
  Lemma subn_abba:
    forall n a b,
      n >= b ->
      n + a - b + b - a = n.
  Proof. by intros; lia. Qed.
  
  (** We can drop additive terms on the lesser side of an inequality. *)
  Lemma leq_addk:
    forall m n k,
      n + k <= m ->
      n <= m.
  Proof. by intros; lia. Qed.
    
  (** For any numbers [a], [b], and [m], either there exists a number
      [n] such that [m = a + n * b] or [m <> a + n * b] for any [n]. *)
  Lemma exists_or_not_add_mul_cases:
    forall a b m,
      (exists n, m = a + n * b) \/
      (forall n, m <> a + n * b).
  Proof.
    move=> a b m.
    case: (leqP a  m) => LE.
    { case: (boolP(b %| (m - a))) => DIV; [left | right].
      { exists ((m - a) %/ b).
        by rewrite divnK // subnKC //. }
      { move => n EQ.
        move: DIV => /negP DIV; apply DIV.
        rewrite EQ.
        rewrite -addnBAC // subnn add0n.
        apply dvdn_mull.
        by apply dvdnn. }
    }
    { right; move=> n EQ.
      move: LE; rewrite EQ.
      by rewrite -ltn_subRL subnn //.
    }
  Qed.  

  (** The expression [n2 * a + b] can be written as [n1 * a + b + (n2 - n1) * a]
      for any integer [n1] such that [n1 <= n2]. *)
  Lemma add_mul_diff:
    forall n1 n2 a b,
      n1 <= n2 ->
      n2 * a + b = n1 * a + b + (n2 - n1) * a.
  Proof.
    intros * LT.
    rewrite mulnBl.
    rewrite addnBA; first by lia.
    destruct a; first by lia.
    by rewrite leq_pmul2r.
  Qed.

  (** Given constants [a, b, c, z] such that [b <= a], if there is no
      constant [m] such that [a = b + m * c], then it holds that there
      is no constant [n] such that [a + z * c = b + n * c]. *)
  Lemma mul_add_neq: 
    forall a b c z,
      b <= a ->
      (forall m, a <> b + m * c) -> 
      forall n, a + z * c <> b + n * c.
  Proof.
    intros * LTE NEQ n EQ.
    specialize (NEQ (n - z)).
    rewrite mulnBl in NEQ.
    by lia.
  Qed.
  
End NatLemmas.

(** In this section, we prove a lemma about intervals of natural
    numbers. *)
Section Interval.
  
  (** Trivially, points before the start of an interval, or past the
      end of an interval, are not included in the interval. *)
  Lemma point_not_in_interval:
    forall t1 t2 t',
      t2 <= t' \/ t' < t1 ->
      forall t,
        t1 <= t < t2 ->
        t <> t'.
  Proof.
    move=> t1 t2 t' EXCLUDED t /andP [GEQ_t1 LT_t2] EQ; subst.
    by case EXCLUDED => [INEQ | INEQ];
      eapply leq_ltn_trans in INEQ; eauto;
        rewrite ltnn in INEQ.
  Qed.

End Interval.

(* [ltn_leq_trans]: Establish that [m < p] if [m < n] and [n <= p], to mirror the
   lemma [leq_ltn_trans] in [ssrnat].

   NB: There is a good reason for this lemma to be "missing" in [ssrnat] --
   since [m < n] is defined as [m.+1 <= n], [ltn_leq_trans] is just
   [m.+1 <= n -> n <= p -> m.+1 <= p], that is [@leq_trans n m.+1 p].

   Nonetheless we introduce it here because an additional (even though
   arguably redundant) lemma doesn't hurt, and for newcomers the apparent
   absence of the mirror case of [leq_ltn_trans] can be somewhat confusing.  *)
Lemma ltn_leq_trans_deprecated [n m p] : m < n -> n <= p -> m < p.
Proof. exact: leq_trans. Qed.
#[deprecated(since="0.4",note="Use leq_trans instead since n < m is just a notation for n.+1 <= m (c.f., comment in util/nat.v).")]
Notation ltn_leq_trans := ltn_leq_trans_deprecated.
