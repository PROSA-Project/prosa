Require Import rt.util.tactics rt.util.notation.
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

End StepFunction.