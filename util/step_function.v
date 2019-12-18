Require Import prosa.util.tactics prosa.util.notation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.

Section StepFunction.

  Section Defs.

    (* We say that a function f... *)
    Variable f: nat -> nat.

    (* ...is a step function iff the following holds. *)
    Definition is_step_function :=
      forall t, f (t + 1) <= f t + 1.

  End Defs.

  Section Lemmas.

    (* Let f be any step function over natural numbers. *)
    Variable f: nat -> nat.
    Hypothesis H_step_function: is_step_function f.

    (* In this section, we prove a result similar to the intermediate
       value theorem for continuous functions. *)
    Section ExistsIntermediateValue.

      (* Consider any interval [x1, x2]. *)
      Variable x1 x2: nat.
      Hypothesis H_is_interval: x1 <= x2.

      (* Let t be any value such that f x1 < y < f x2. *)
      Variable y: nat.
      Hypothesis H_between: f x1 <= y < f x2.

      (* Then, we prove that there exists an intermediate point x_mid such that
         f x_mid = y. *)
      Lemma exists_intermediate_point:
        exists x_mid, x1 <= x_mid < x2 /\ f x_mid = y.
      Proof.
        rename H_is_interval into INT, H_step_function into STEP, H_between into BETWEEN.
        move: x2 INT BETWEEN; clear x2.
        suff DELTA:
          forall delta,
            f x1 <= y < f (x1 + delta) ->
            exists x_mid, x1 <= x_mid < x1 + delta /\ f x_mid = y.
        { move => x2 LE /andP [GEy LTy].
          exploit (DELTA (x2 - x1));
            first by apply/andP; split; last by rewrite addnBA // addKn.
            by rewrite addnBA // addKn.
        }
        induction delta.
        { rewrite addn0; move => /andP [GE0 LT0].
            by apply (leq_ltn_trans GE0) in LT0; rewrite ltnn in LT0.
        }
        { move => /andP [GT LT].
          specialize (STEP (x1 + delta)); rewrite leq_eqVlt in STEP.
          have LE: y <= f (x1 + delta).
          { move: STEP => /orP [/eqP EQ | STEP];
              first by rewrite !addn1 in EQ; rewrite addnS EQ ltnS in LT.
            rewrite [X in _ < X]addn1 ltnS in STEP.
            apply: (leq_trans _ STEP).
              by rewrite addn1 -addnS ltnW.
          } clear STEP LT.
          rewrite leq_eqVlt in LE.
          move: LE => /orP [/eqP EQy | LT].
          { exists (x1 + delta); split; last by rewrite EQy.
              by apply/andP; split; [by apply leq_addr | by rewrite addnS].
          }
          { feed (IHdelta); first by apply/andP; split.
            move: IHdelta => [x_mid [/andP [GE0 LT0] EQ0]].
            exists x_mid; split; last by done.
            apply/andP; split; first by done.
              by apply: (leq_trans LT0); rewrite addnS.
          }  
        }
      Qed.

    End ExistsIntermediateValue.

  End Lemmas.

  (* In this section, we prove an analogue of the intermediate
     value theorem, but for predicates of natural numbers. *) 
  Section ExistsIntermediateValuePredicates. 

    (* Let P be any predicate on natural numbers. *)
    Variable P : nat -> bool.

    (* Consider a time interval [t1,t2] such that ... *)
    Variables t1 t2 : nat.
    Hypothesis H_t1_le_t2 : t1 <= t2.

    (* ... P doesn't hold for t1 ... *)
    Hypothesis H_not_P_at_t1 : ~~ P t1.

    (* ... but holds for t2. *)
    Hypothesis H_P_at_t2 : P t2.
    
    (* Then we prove that within time interval [t1,t2] there exists time 
       instant t such that t is the first time instant when P holds. *)
    Lemma exists_first_intermediate_point:
      exists t, (t1 < t <= t2) /\ (forall x, t1 <= x < t -> ~~ P x) /\ P t.
    Proof.
      have EX: exists x, P x && (t1 < x <= t2).
      { exists t2.
        apply/andP; split; first by done.
        apply/andP; split; last by done.
        move: H_t1_le_t2; rewrite leq_eqVlt; move => /orP [/eqP EQ | NEQ1]; last by done.
          by exfalso; subst t2; move: H_not_P_at_t1 => /negP NPt1. 
      }
      have MIN := ex_minnP EX.
      move: MIN => [x /andP [Px /andP [LT1 LT2]] MIN]; clear EX.
      exists x; repeat split; [ apply/andP; split | | ]; try done.
      move => y /andP [NEQ1 NEQ2]; apply/negPn; intros Py.
      feed (MIN y). 
      { apply/andP; split; first by done.
        apply/andP; split.
        - move: NEQ1. rewrite leq_eqVlt; move => /orP [/eqP EQ | NEQ1]; last by done.
            by exfalso; subst y; move: H_not_P_at_t1 => /negP NPt1. 
        - by apply ltnW, leq_trans with x.
      }
        by move: NEQ2; rewrite ltnNge; move => /negP NEQ2.
    Qed.
    
  End ExistsIntermediateValuePredicates.  

End StepFunction.