Require Import prosa.classic.util.tactics prosa.classic.util.induction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Section FixedPoint.
  
  Lemma iter_fix T (F : T -> T) x k n :
    iter k F x = iter k.+1 F x ->
    k <= n ->
    iter n F x = iter n.+1 F x.
  Proof.
    move => e. elim: n. rewrite leqn0. by move/eqP<-.
    move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
    move/IH => /= IHe. by rewrite -!IHe.
  Qed.

  Lemma fun_mon_iter_mon :
    forall (f: nat -> nat) x0 x1 x2,
      x1 <= x2 ->
      f x0 >= x0 ->
      (forall x1 x2, x1 <= x2 -> f x1 <= f x2) ->
      iter x1 f x0 <= iter x2 f x0.
  Proof.
    intros f x0 x1 x2 LE MIN MON.
    revert LE; revert x2; rewrite leq_as_delta; intros delta.
    induction x1; try rewrite add0n.
    {
      induction delta; first by apply leqnn.
      apply leq_trans with (n := iter delta f x0); first by done.
      clear IHdelta.
      induction delta; first by done.
      {
        rewrite 2!iterS; apply MON.
        apply IHdelta.
      }
    }
    {
      rewrite iterS -addn1 -addnA [1 + delta]addnC addnA addn1 iterS.
      by apply MON, IHx1.
    }
  Qed.

  Lemma fun_mon_iter_mon_helper :
    forall T (f: T -> T) (le: rel T) x0 x1,
      reflexive le ->
      transitive le ->
      (forall x2, le x0 (iter x2 f x0)) ->
      (forall x1 x2, le x0 x1 -> le x1 x2 -> le (f x1) (f x2)) ->
      le (iter x1 f x0) (iter x1.+1 f x0).
  Proof.
    intros T f le x0 x1 REFL TRANS MIN MON.
    generalize dependent x0.
    induction x1; first by ins; apply (MIN 1).
    by ins; apply MON; [by apply MIN | by apply IHx1].
  Qed.

  Lemma fun_mon_iter_mon_generic :
    forall T (f: T -> T) (le: rel T) x0 x1 x2,
      reflexive le ->
      transitive le ->
      x1 <= x2 ->
      (forall x1 x2, le x0 x1 -> le x1 x2 -> le (f x1) (f x2)) ->
      (forall x2 : nat, le x0 (iter x2 f x0)) ->
      le (iter x1 f x0) (iter x2 f x0).
  Proof.
    intros T f le x0 x1 x2 REFL TRANS LE MON MIN.
    revert LE; revert x2; rewrite leq_as_delta; intros delta.
    induction delta; first by rewrite addn0; apply REFL.
    apply (TRANS) with (y := iter (x1 + delta) f x0);
      first by apply IHdelta.
    by rewrite addnS; apply fun_mon_iter_mon_helper.
  Qed.

End FixedPoint.

(* In this section, we define some properties of relations
   that are important for fixed-point iterations. *)
Section Relations.

  Context {T: Type}.
  Variable R: rel T.
  Variable f: T -> T.
  
  Definition monotone (R: rel T) :=
    forall x y, R x y -> R (f x) (f y).

End Relations.

(* In this section we define a fixed-point iteration function
   that stops as soon as it finds the solution. If no solution
   is found, the function returns None. *)
Section Iteration.

  Context {T : eqType}.
  Variable f: T -> T.

  Fixpoint iter_fixpoint max_steps (x: T) :=
    if max_steps is step.+1 then
      let x' := f x in
        if x == x' then
          Some x
        else iter_fixpoint step x'
    else None.

  Section BasicLemmas.

    (* We prove that iter_fixpoint either returns either None
       or Some y, where y is a fixed point. *)
    Lemma iter_fixpoint_cases :
      forall max_steps x0,
        iter_fixpoint max_steps x0 = None \/
        exists y,
          iter_fixpoint max_steps x0 = Some y /\
          y = f y. 
    Proof.
      induction max_steps.
      {
        by ins; simpl; destruct (x0 == f x0); left. 
      }
      {
        intros x0; simpl.
        destruct (x0 == f x0) eqn:EQ1;
          first by right; exists x0; split; last by apply/eqP.
        by destruct (IHmax_steps (f x0)) as [NONE | FOUND].
      }
    Qed. 

    (* We also show that any inductive property P is propagated
       through the fixed-point iteration. *)
    Lemma iter_fixpoint_ind:
      forall max_steps x0 x,
        iter_fixpoint max_steps x0 = Some x ->
        forall P,
          P x0 ->
          (forall x, P x -> P (f x)) ->
          P x.
    Proof.
      induction max_steps; first by done.
      intros x0 x SOME P P0 ALL.
      move: SOME; simpl.
      case EQ: (_ == _).
      {
        move: EQ => /eqP EQ.
        case => SAME; subst.
        by rewrite EQ; apply ALL.
      }
      {
        intros SOME; clear EQ.
        apply (IHmax_steps (f x0) x SOME P); first by apply ALL.
        by apply ALL.
      }
    Qed.
      
  End BasicLemmas.

  Section RelationLemmas.

    Variable R: rel T.
    Hypothesis H_reflexive: reflexive R.
    Hypothesis H_transitive: transitive R.
    Hypothesis H_monotone: monotone f R.

    Lemma iter_fixpoint_ge_min:
      forall max_steps x0 x1 x,
        iter_fixpoint max_steps x1 = Some x ->
        R x0 x1 ->
        R x1 (f x1) ->
        R x0 x.
    Proof.
      induction max_steps; first by done.
      {
        intros x0 x1 x SOME MIN BOT; simpl in SOME.
        destruct (x1 == f x1) eqn:EQ1;
          first by inversion SOME; subst.
        apply IHmax_steps with (x0 := x0) in SOME; first by done.
        - by apply (@H_transitive x1).
        - by apply H_monotone.
      }
    Qed.

    Lemma iter_fixpoint_ge_bottom:
      forall max_steps x0 x,
        iter_fixpoint max_steps x0 = Some x ->
        R x0 (f x0) ->
        R x0 x.
    Proof.
      intros max_steps x0 x SOME BOT.
      by apply iter_fixpoint_ge_min with (max_steps := max_steps) (x1 := x0). 
    Qed.
    
  End RelationLemmas.
  
End Iteration.