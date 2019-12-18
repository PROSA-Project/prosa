Require Export prosa.util.sum.
Require Export prosa.util.ssromega.

Require Import prosa.classic.util.tactics.
Require Import prosa.classic.util.notation.
Require Import prosa.classic.util.sorting.
Require Import prosa.classic.util.nat.
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