Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we show how to compute the time instant after the last
   execution of a job and prove several lemmas about that instant. This
   notion is crucial for defining suspension intervals. *)
Module LastExecution.

  Export Job UniprocessorSchedule.

  (* In this section we define the time after the last execution of a job (if exists). *)
  Section TimeAfterLastExecution.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Consider any uniprocessor schedule. *)
    Variable sched: schedule Job.

    (* For simplicity, let's define some local names. *)
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.

    Section Defs.
      
      (* Let j be any job in the arrival sequence. *)
      Variable j: Job.

      (* Next, we will show how to find the time after the most recent
         execution of a given job j in the interval [job_arrival j, t).
         (Note that this instant can be time t itself.) *)
      Variable t: time.
      
      (* Let scheduled_before denote whether job j was scheduled in the interval [0, t). *)
      Let scheduled_before :=
        [exists t0: 'I_t, job_scheduled_at j t0].

      (* In case j was scheduled before, we define the last time in which j was scheduled. *)
      Let last_time_scheduled :=
        \max_(t_last < t | job_scheduled_at j t_last) t_last.

      (* Then, the time after the last execution of job j in the interval [0, t), if exists,
         occurs:
           (a) immediately after the last time in which job j was scheduled, or,
           (b) if j was never scheduled, at the arrival time of j. *)
      Definition time_after_last_execution :=
        if scheduled_before then
          last_time_scheduled + 1
        else job_arrival j.

    End Defs.

    (* Next, we prove lemmas about the time after the last execution. *)
    Section Lemmas.

      (* Assume that jobs do not execute before they arrived. *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched.
        
      (* Let j be any job. *)
      Variable j: Job.

      (* In this section, we show that the time after the last execution occurs
           no earlier than the arrival of the job. *)
      Section JobHasArrived.

        (* Then, the time following the last execution of job j in the
             interval [0, t) occurs no earlier than the arrival of j. *)
        Lemma last_execution_after_arrival:
          forall t,
            has_arrived job_arrival j (time_after_last_execution j t).
        Proof.
          unfold time_after_last_execution, has_arrived; intros t.
          case EX: [exists _, _]; last by done.
          move: EX => /existsP [t0 SCHED].
          apply leq_trans with (n := t0 + 1);
            last by rewrite leq_add2r; apply leq_bigmax_cond.
          apply leq_trans with (n := t0); last by rewrite addn1.
            by apply H_jobs_must_arrive_to_execute.
        Qed.

      End JobHasArrived.

      (* Next, we establish the monotonicity of the function. *)
      Section Monotonicity.

        (* Let t1 be any time no earlier than the arrival of job j. *)
        Variable t1: time.
        Hypothesis H_after_arrival: has_arrived job_arrival j t1.

        (* Then, (time_after_last_execution j) grows monotonically
             after that point. *)
        Lemma last_execution_monotonic:
          forall t2,
            t1 <= t2 ->
            time_after_last_execution j t1 <= time_after_last_execution j t2.
        Proof.
          rename H_jobs_must_arrive_to_execute into ARR.
          intros t2 LE12.
          rewrite /time_after_last_execution.
          case EX1: [exists _, _].
          {
            move: EX1 => /existsP [t0 SCHED0].
            have EX2: [exists t:'I_t2, job_scheduled_at j t].
            {
              have LT: t0 < t2 by apply: (leq_trans _ LE12).
                by apply/existsP; exists (Ordinal LT).
            }
            rewrite EX2 2!addn1.
            set m1 := \max_(_ < t1 | _)_.
            have LTm1: m1 < t2.
            {
              apply: (leq_trans _ LE12).
                by apply bigmax_ltn_ord with (i0 := t0).
            }
            apply leq_ltn_trans with (n := Ordinal LTm1); first by done.
              by apply leq_bigmax_cond, (bigmax_pred _ _ t0).
          }
          {
            case EX2: [exists _, _]; last by done.
            move: EX2 => /existsP [t0 SCHED0].
            set m2 := \max_(_ < t2 | _)_.
            rewrite addn1 ltnW // ltnS.
            have SCHED2: scheduled_at sched j m2 by apply (bigmax_pred _ _ t0).
              by apply ARR in SCHED2.
          }
        Qed.

      End Monotonicity.

      (* Next, we prove that the function is idempotent. *)
      Section Idempotence.
        
        (* The time after the last execution of job j is an idempotent function. *)
        Lemma last_execution_idempotent:
          forall t,
            time_after_last_execution j (time_after_last_execution j t)
            = time_after_last_execution j t.
        Proof.
          rename H_jobs_must_arrive_to_execute into ARR.
          intros t.
          rewrite {2 3}/time_after_last_execution.
          case EX: [exists _,_].
          {
            move: EX => /existsP [t0 SCHED].
            rewrite /time_after_last_execution.
            set ex := [exists t0, _].
            have EX': ex.
            {
              apply/existsP; rewrite addn1.
              exists (Ordinal (ltnSn _)).
                by apply bigmax_pred with (i0 := t0).
            }
            rewrite EX'; f_equal.
            rewrite addn1; apply/eqP.
            set m := \max_(_ < t | _)_.
            have LT: m < m.+1 by done.
            rewrite eqn_leq; apply/andP; split.
            {
              rewrite -ltnS; apply bigmax_ltn_ord with (i0 := Ordinal LT).
                by apply bigmax_pred with (i0 := t0).
            }
            {
              apply leq_trans with (n := Ordinal LT); first by done.
                by apply leq_bigmax_cond, bigmax_pred with (i0 := t0).
            }
          }
          {
            apply negbT in EX; rewrite negb_exists in EX.
            move: EX => /forallP EX.
            rewrite /time_after_last_execution.
            set ex := [exists _, _].
            suff EX': ex = false; first by rewrite EX'.
            apply negbTE; rewrite negb_exists; apply/forallP.
            intros x.
            apply/negP; intro SCHED.
            apply ARR in SCHED.
              by apply leq_ltn_trans with (p := job_arrival j) in SCHED;
                first by rewrite ltnn in SCHED.
          }
        Qed.

      End Idempotence.

      (* Next, we show that time_after_last_execution is bounded by the identity function. *)
      Section BoundedByIdentity.
        
        (* Let t be any time no earlier than the arrival of j. *)
        Variable t: time.
        Hypothesis H_after_arrival: has_arrived job_arrival j t.

        (* Then, the time following the last execution of job j in the interval [0, t)
           occurs no later than time t. *)
        Lemma last_execution_bounded_by_identity:
          time_after_last_execution j t <= t.
        Proof.
          unfold time_after_last_execution.
          case EX: [exists _, _]; last by done.
          move: EX => /existsP [t0 SCHED].
            by rewrite addn1; apply bigmax_ltn_ord with (i0 := t0).
        Qed.

      End BoundedByIdentity.

      (* In this section, we show that if the service received by a job
           remains the same, the time after last execution also doesn't change. *)
      Section SameLastExecution.
        
        (* Consider any time instants t and t'... *)
        Variable t t': time.

        (* ...in which job j has received the same amount of service. *)
        Hypothesis H_same_service: service sched j t = service sched j t'.

        (* Then, we prove that the times after last execution relative to
             instants t and t' are exactly the same. *)
        Lemma same_service_implies_same_last_execution:
          time_after_last_execution j t = time_after_last_execution j t'.
        Proof.
          rename H_same_service into SERV.
          have IFF := same_service_implies_scheduled_at_earlier_times
                        sched j t t' SERV.
          rewrite /time_after_last_execution.
          rewrite IFF; case EX2: [exists _, _]; [f_equal | by done].
          have EX1: [exists x: 'I_t, job_scheduled_at j x] by rewrite IFF.
          clear IFF.
          move: t t' SERV EX1 EX2 => t1 t2; clear t t'.
          wlog: t1 t2 / t1 <= t2 => [EQ SERV EX1 EX2 | LE].
            by case/orP: (leq_total t1 t2); ins; [|symmetry]; apply EQ.
            
            set m1 := \max_(t < t1 | job_scheduled_at j t) t.
            set m2 := \max_(t < t2 | job_scheduled_at j t) t.
            move => SERV /existsP [t1' SCHED1'] /existsP [t2' SCHED2'].
            apply/eqP; rewrite eqn_leq; apply/andP; split.
            {
              have WID := big_ord_widen_cond t2
                                             (fun x => job_scheduled_at j x) (fun x => x).
                          rewrite /m1 /m2 {}WID //.
                          rewrite big_mkcond [\max_(t < t2 | _) _]big_mkcond.
                          apply leq_big_max; intros i _.
                          case AND: (_ && _); last by done.
                            by move: AND => /andP [SCHED _]; rewrite SCHED.
            }
            {
              destruct (leqP t2 m1) as [GEm1 | LTm1].
              {
                apply leq_trans with (n := t2); last by done.
                  by apply ltnW, bigmax_ltn_ord with (i0 := t2').
              }
              destruct (ltnP m2 t1) as [LTm2 | GEm2].
              {
                apply leq_trans with (n := Ordinal LTm2); first by done.
                  by apply leq_bigmax_cond, bigmax_pred with (i0 := t2').
              }
              have LTm2: m2 < t2 by apply bigmax_ltn_ord with (i0 := t2').
              have SCHEDm2: job_scheduled_at j m2 by apply bigmax_pred with (i0 := t2').
              exfalso; move: SERV => /eqP SERV.
              rewrite -[_ == _]negbK in SERV.
              move: SERV => /negP SERV; apply SERV; clear SERV.
              rewrite neq_ltn; apply/orP; left.
              rewrite /service /service_during.
              rewrite -> big_cat_nat with (n := m2) (p := t2);
                [simpl | by done | by apply ltnW].
              rewrite -addn1; apply leq_add; first by apply extend_sum. 
              destruct t2; first by rewrite ltn0 in LTm1.
              rewrite big_nat_recl; last by done.
                by rewrite /service_at -/job_scheduled_at SCHEDm2.
            }
        Qed.

      End SameLastExecution.

      (* In this section, we show that the service received by a job
         does not change since the last execution. *)
      Section SameService.

        (* We prove that, for any time t, the service received by job j
           before (time_after_last_execution j t) is the same as the service
           by j before time t. *)
        Lemma same_service_since_last_execution:
          forall t,
            service sched j (time_after_last_execution j t) = service sched j t.
        Proof.
          intros t; rewrite /time_after_last_execution.
          case EX: [exists _, _].
          {
            move: EX => /existsP [t0 SCHED0].
            set m := \max_(_ < _ | _) _; rewrite addn1.
            have LTt: m < t by apply: (bigmax_ltn_ord _ _ t0).
            rewrite leq_eqVlt in LTt.
            move: LTt => /orP [/eqP EQ | LTt]; first by rewrite EQ.
            rewrite {2}/service/service_during.
            rewrite -> big_cat_nat with (n := m.+1);
              [simpl | by done | by apply ltnW].
            rewrite [X in _ + X]big_nat_cond [X in _ + X]big1 ?addn0 //.
            move => i /andP [/andP [GTi LTi] _].
            apply/eqP; rewrite eqb0; apply/negP; intro BUG.
            have LEi: (Ordinal LTi) <= m by apply leq_bigmax_cond.
              by apply (leq_ltn_trans LEi) in GTi; rewrite ltnn in GTi.
          }
          {
            apply negbT in EX; rewrite negb_exists in EX.
            move: EX => /forallP ALL.
            rewrite /service /service_during.
            rewrite (ignore_service_before_arrival job_arrival) // big_geq //.
            rewrite big_nat_cond big1 //; move => i /andP [/= LTi _].
            by apply/eqP; rewrite eqb0; apply (ALL (Ordinal LTi)).
          }
        Qed.

      End SameService.

      (* In this section, we show that for any smaller value of service, we can
         always find the last execution that corresponds to that service. *)
      Section ExistsIntermediateExecution.

        (* Assume that job j has completed by time t. *)
        Variable t: time.
        Hypothesis H_j_has_completed: completed_by job_cost sched j t.

        (* Then, for any value of service less than the cost of j, ...*)
        Variable s: time.
        Hypothesis H_less_than_cost: s < job_cost j.

        (* ...there exists a last execution where the service received
           by job j equals s. *)
        Lemma exists_last_execution_with_smaller_service:
          exists t0,
            service sched j (time_after_last_execution j t0) = s.
        Proof.
          have SAME := same_service_since_last_execution.
          rename H_jobs_must_arrive_to_execute into ARR.
          move: H_j_has_completed => COMP.
          feed (exists_intermediate_point (service sched j));
            first by apply service_is_a_step_function.
          move => EX; feed (EX (job_arrival j) t).
          { feed (cumulative_service_implies_scheduled sched j 0 t).
            apply leq_ltn_trans with (n := s); first by done.
            apply leq_trans with (job_cost j); by done.
            move => [t' [/= LTt SCHED]].
            apply leq_trans with (n := t'); last by apply ltnW.
              by apply ARR in SCHED.
          }
          feed (EX s).
          { apply/andP; split. 
            - rewrite /service /service_during.
                by rewrite (ignore_service_before_arrival job_arrival) // big_geq.
            - apply leq_ltn_trans with (n := s); first by done.
                by apply leq_trans with (job_cost j).
          }
          move: EX => [x_mid [_ SERV]]; exists x_mid.
          by rewrite -SERV SAME.
        Qed.

      End ExistsIntermediateExecution.

      (* In this section we prove that before the last execution the job
         must have received strictly less service. *)
      Section LessServiceBeforeLastExecution.

        (* Let t be any time... *)
        Variable t: time.

        (* ...and consider any earlier time t0 no earlier than the arrival of job j... *)
        Variable t0: time.
        Hypothesis H_no_earlier_than_arrival: has_arrived job_arrival j t0.

        (* ...and before the last execution of job j (with respect to time t). *)
        Hypothesis H_before_last_execution: t0 < time_after_last_execution j t.

        (* Then, we can prove that the service received by j before time t0
           is strictly less than the service received by j before time t. *)
        Lemma less_service_before_start_of_suspension:
          service sched j t0 < service sched j t.
        Proof.
          rename H_no_earlier_than_arrival into ARR, H_before_last_execution into LT.
          set ex := time_after_last_execution in LT.
          set S := service sched.
          case EX:([exists t0:'I_t, scheduled_at sched j t0]); last first.
          {
            rewrite /ex /time_after_last_execution EX in LT.
            apply leq_trans with (p := t0) in LT; last by done.
            by rewrite ltnn in LT.
          }
          {
            rewrite /ex /time_after_last_execution EX in LT.
            set m := (X in _ < X + 1) in LT.
            apply leq_ltn_trans with (n := S j m);
              first by rewrite -/m addn1 ltnS in LT; apply extend_sum.
            move: EX => /existsP [t' SCHED'].
            have LTt: m < t by apply bigmax_ltn_ord with (i0 := t').
            rewrite /S /service /service_during.
            rewrite -> big_cat_nat with (p := t) (n := m); [simpl | by done | by apply ltnW].
            rewrite -addn1 leq_add2l; destruct t; first by done.
            rewrite big_nat_recl //.
            apply leq_trans with (n := scheduled_at sched j m); last by apply leq_addr.
            rewrite lt0n eqb0 negbK.
            by apply bigmax_pred with (i0 := t').
          }
        Qed.

      End LessServiceBeforeLastExecution.
      
    End Lemmas.
      
  End TimeAfterLastExecution.

End LastExecution.