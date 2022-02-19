From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.
Require Export mathcomp.zify.zify.

Require Export prosa.util.tactics.

(** Additional lemmas about natural numbers. *)
Section NatLemmas.

  (** First, we show that, given [m >= p] and [n >= q], an
      expression [(m + n) - (p + q)] can be transformed into
      expression [(m - p) + (n - q)]. *)
  Lemma subnACA m n p q : p <= m -> q <= n ->
    (m + n) - (p + q) = (m - p) + (n - q).
  Proof. by move=> plem qlen; rewrite subnDA addnBAC// addnBA// subnAC. Qed.

  (** Next, we show that [m + p <= n] implies that [m <= n - p]. Note
      that this lemma is similar to ssreflect's lemma [leq_subRL];
      however, the current lemma has no precondition [n <= p], since it
      has only one direction. *)
  Lemma leq_subRL_impl m n p : m + n <= p -> n <= p - m.
  Proof.
    have [mlep|pltm] := leqP m p; first by rewrite leq_subRL.
    by move=> /(leq_trans (ltn_addr _ pltm)); rewrite ltnn.
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
