From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
Require Export prosa.util.notation prosa.util.nat prosa.util.list.

(** Additional lemmas about [BigMax]. *)
Section ExtraLemmas.

  (** Given a function [F], a predicate [P], and a sequence [xs], we
      show that [F x <= max { F i | ∀ i ∈ xs, P i}] for any [x] in
      [xs]. *)
  Lemma leq_bigmax_cond_seq :
    forall {X : eqType} (F : X -> nat) (P : pred X) (xs : seq X) (x : X),
      x \in xs -> P x -> F x <= \max_(i <- xs | P i) F i.
  Proof. by intros * IN Px; rewrite (big_rem x) //= Px leq_maxl. Qed.

  (** Next, we show that the fact [max { F i | ∀ i ∈ xs, P i} <= m] for
      some [m] is equivalent to the fact that [∀ x ∈ xs, P x -> F x <= m]. *)
  Lemma bigmax_leq_seqP : 
    forall {X : eqType} (F : X -> nat) (P : pred X) (xs : seq X) (m : nat),
      reflect (forall x, x \in xs -> P x -> F x <= m)
              (\max_(x <- xs | P x) F x <= m).
  Proof.
    intros *.
    apply: (iffP idP) => leFm => [i IINR Pi|].
    - by apply: leq_trans leFm; apply leq_bigmax_cond_seq.
    - rewrite big_seq_cond; elim/big_ind: _ => // m1 m2.
      + by intros; rewrite geq_max; apply/andP; split. 
      + by move: m2 => /andP [M1IN Pm1]; apply: leFm.
  Qed.

  (** Given two functions [F1] and [F2], a predicate [P], and sequence
      [xs], we show that if [F1 x <= F2 x] for any [x \in xs] such that
      [P x], then [max] of [{F1 x | ∀ x ∈ xs, P x}] is bounded by the
      [max] of [{F2 x | ∀ x ∈ xs, P x}]. *)
  Lemma leq_big_max :
    forall {X : eqType} (F1 F2 : X -> nat) (P : pred X) (xs : seq X), 
      (forall x, x \in xs -> P x -> F1 x <= F2 x) ->
      \max_(x <- xs | P x) F1 x <= \max_(x <- xs | P x) F2 x.
  Proof.
    intros * ALL; apply /bigmax_leq_seqP; intros * IN Px.
    specialize (ALL x); feed_n 2 ALL; try done.
    rewrite (big_rem x) //=; rewrite Px.
    by apply leq_trans with (F2 x); [ | rewrite leq_maxl].
  Qed.

  (** We show that for a positive [n], [max] of [{0, …, n-1}] is
      smaller than [n]. *)
  Lemma bigmax_ord_ltn_identity :
    forall (n : nat), 
      n > 0 ->
      \max_(i < n) i < n.
  Proof.
    intros [ | n] POS; first by rewrite ltn0 in POS.
    clear POS; induction n; first by rewrite big_ord_recr /= big_ord0 maxn0.
    rewrite big_ord_recr /=.
    by rewrite /maxn IHn.
  Qed.

  (** We state the next lemma in terms of _ordinals_.  Given a natural
      number [n], a predicate [P], and an ordinal [i0 ∈ {0, …, n-1}]
      satisfying [P], we show that [max {i | P i} < n].  Note that the
      element satisfying [P] is needed to prove that [{i | P i}] is
      not empty. *)
  Lemma bigmax_ltn_ord :
    forall (n : nat) (P : pred nat) (i0 : 'I_n), 
    P i0 ->
    \max_(i < n | P i) i < n.
  Proof.
    intros n P i0 Pi.
    destruct n; first by destruct i0 as [i0 P0]; move: (P0) => P0'; rewrite ltn0 in P0'.
    rewrite big_mkcond.
    apply leq_ltn_trans with (n := \max_(i < n.+1) i).
    - apply/bigmax_leqP; ins.
      destruct (P i); last by done.
      by apply leq_bigmax_cond.
    - by apply bigmax_ord_ltn_identity.
  Qed.

  (** Finally, we show that, given a natural number [n], a predicate
      [P], and an ordinal [i0 ∈ {0, …, n-1}] satisfying [P], 
      [max {i | P i} < n] also satisfies [P]. *) 
  Lemma bigmax_pred :
    forall (n : nat) (P : pred nat) (i0 : 'I_n), 
      P i0 ->
      P (\max_(i < n | P i) i).
  Proof.
    intros * Pi0.
    induction n.
    { by destruct i0 as [i0 P0]; move: (P0) => P1; rewrite ltn0 in P1. }
    { rewrite big_mkcond big_ord_recr /=.
      destruct (P n) eqn:Pn.
      { destruct n; first by rewrite big_ord0 maxn0.
        unfold maxn at 1.
        destruct (\max_(i < n.+1) (match P (@nat_of_ord (S n) i) return nat with
                                   | true => @nat_of_ord (S n) i
                                   | false => O
                                   end) < n.+1) eqn:Pi; first by rewrite Pi.
        exfalso.
        apply negbT in Pi; move: Pi => /negP BUG; apply: BUG. 
        apply leq_ltn_trans with (n := \max_(i < n.+1) i).
        { apply/bigmax_leqP; rewrite //= => i _. 
          by destruct (P i); first apply leq_bigmax_cond.
        }
        { by apply bigmax_ord_ltn_identity. } 
      }
      { rewrite maxn0 -big_mkcond /=.
        have LT: i0 < n; last by rewrite (IHn (Ordinal LT)).
        rewrite ltn_neqAle; apply/andP; split;
          last by rewrite -ltnS; apply ltn_ord.
        apply/negP; move => /eqP BUG.
        by rewrite -BUG Pi0 in Pn.
      }
    }
  Qed.
  
End ExtraLemmas.
