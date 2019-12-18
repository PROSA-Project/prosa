Require Export prosa.util.notation prosa.util.nat prosa.util.list.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Additional lemmas about max. *)
Section ExtraLemmas.

  Lemma leq_bigmax_cond_seq (T : eqType) (P : pred T) (r : seq T) F i0 :
    i0 \in r -> P i0 -> F i0 <= \max_(i <- r | P i) F i.
  Proof.
    intros IN0 Pi0; by rewrite (big_rem i0) //= Pi0 leq_maxl.
  Qed.

  Lemma bigmax_sup_seq:
    forall (T: eqType) (i: T) r (P: pred T) m F,
      i \in r -> P i -> m <= F i -> m <= \max_(i <- r| P i) F i.
  Proof.
    intros.
    induction r.
    - by rewrite in_nil  in H.
      move: H; rewrite in_cons; move => /orP [/eqP EQA | IN].
      {
        clear IHr; subst a.
        rewrite (big_rem i) //=; last by rewrite in_cons; apply/orP; left.
        apply leq_trans with (F i); first by done.
          by rewrite H0 leq_maxl.
      }
      {
        apply leq_trans with (\max_(i0 <- r | P i0) F i0); first by apply IHr.
        rewrite [in X in _ <= X](big_rem a) //=; last by rewrite in_cons; apply/orP; left.

        have Ob: a == a; first by done.
          by rewrite Ob leq_maxr.
      }
  Qed.

  Lemma bigmax_leq_seqP (T : eqType) (P : pred T) (r : seq T) F m :
    reflect (forall i, i \in r -> P i -> F i <= m)
            (\max_(i <- r | P i) F i <= m).
  Proof.
    apply: (iffP idP) => leFm => [i IINR Pi|];
      first by apply: leq_trans leFm; apply leq_bigmax_cond_seq.
    rewrite big_seq_cond; elim/big_ind: _ => // m1 m2.
      by intros; rewrite geq_max; apply/andP; split. 
      by move: m2 => /andP [M1IN Pm1]; apply: leFm.
  Qed.

  Lemma leq_big_max (T : eqType) (P : pred T) (r : seq T) F1 F2 :
    (forall i, i \in r -> P i -> F1 i <= F2 i) ->
    \max_(i <- r | P i) F1 i <= \max_(i <- r | P i) F2 i.
  Proof.
    intros; apply /bigmax_leq_seqP; intros.
    specialize (H i); feed_n 2 H; try(done).
    rewrite (big_rem i) //=; rewrite H1.
      by apply leq_trans with (F2 i); [ | rewrite leq_maxl].
  Qed.

  Lemma bigmax_ord_ltn_identity n :
    n > 0 ->
    \max_(i < n) i < n.
  Proof.
    intros LT.
    destruct n; first by rewrite ltn0 in LT.
    clear LT.
    induction n; first by rewrite big_ord_recr /= big_ord0 maxn0.
    rewrite big_ord_recr /=.
      by unfold maxn at 1; rewrite IHn.
  Qed.
    
  Lemma bigmax_ltn_ord n (P : pred nat) (i0: 'I_n) :
    P i0 ->
    \max_(i < n | P i) i < n.
  Proof.
    intros LT.
    destruct n; first by destruct i0 as [i0 P0]; move: (P0) => P0'; rewrite ltn0 in P0'.
    rewrite big_mkcond.
    apply leq_ltn_trans with (n := \max_(i < n.+1) i).
    {
      apply/bigmax_leqP; ins.
      destruct (P i); last by done.
      by apply leq_bigmax_cond.
    }
    by apply bigmax_ord_ltn_identity.
  Qed.

  Lemma bigmax_pred n (P : pred nat) (i0: 'I_n) :
    P (i0) ->
    P (\max_(i < n | P i) i).
  Proof.
    intros PRED.
    induction n.
    {
      destruct i0 as [i0 P0].
      by move: (P0) => P1; rewrite ltn0 in P1. 
    }
    rewrite big_mkcond big_ord_recr /=. destruct (P n) eqn:Pn.
    {
      destruct n; first by rewrite big_ord0 maxn0.
      unfold maxn at 1.
      destruct (\max_(i < n.+1) (match P (@nat_of_ord (S n) i) return nat with
                    | true => @nat_of_ord (S n) i
                    | false => O
                                 end) < n.+1) eqn:Pi; first by rewrite Pi.
      exfalso.
      apply negbT in Pi; move: Pi => /negP BUG.
      apply BUG. 
      apply leq_ltn_trans with (n := \max_(i < n.+1) i).
      {
        apply/bigmax_leqP; ins.
        destruct (P i); last by done.
        by apply leq_bigmax_cond.
      }
      by apply bigmax_ord_ltn_identity.
    }
    {
      rewrite maxn0.
      rewrite -big_mkcond /=.
      have LT: i0 < n.
      {
        rewrite ltn_neqAle; apply/andP; split;
          last by rewrite -ltnS; apply ltn_ord.
        apply/negP; move => /eqP BUG.
        by rewrite -BUG PRED in Pn.
      }
      by rewrite (IHn (Ordinal LT)).
    }
  Qed.
    
End ExtraLemmas.