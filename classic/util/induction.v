Require Import prosa.classic.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Induction lemmas for natural numbers. *)
Section NatInduction.
  
  Lemma strong_ind :
    forall (P: nat -> Prop),
      (forall n, (forall k, k < n -> P k) -> P n) ->
      forall n, P n.
  Proof.
    intros P ALL n; apply ALL.
    induction n; first by ins; apply ALL.
    intros k LTkSn; apply ALL.
    by intros k0 LTk0k; apply IHn, leq_trans with (n := k).
  Qed.

  Lemma leq_as_delta :
    forall x1 (P: nat -> Prop),
      (forall x2, x1 <= x2 -> P x2) <->
      (forall delta, P (x1 + delta)).
  Proof.
    ins; split; last by intros ALL x2 LE; rewrite -(subnK LE) addnC; apply ALL.
    {
      intros ALL; induction delta.
        by rewrite addn0; apply ALL, leqnn. 
        by apply ALL; rewrite -{1}[x1]addn0; apply leq_add; [by apply leqnn | by ins]. 
    }
  Qed.
  
End NatInduction.