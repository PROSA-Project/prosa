Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
Require Import prosa.classic.analysis.uni.jitter.workload_bound_fp
               prosa.classic.analysis.uni.jitter.fp_rta_comp.
Require Import prosa.classic.implementation.uni.jitter.job
               prosa.classic.implementation.uni.jitter.task
               prosa.classic.implementation.uni.jitter.arrival_sequence
               prosa.classic.implementation.uni.jitter.schedule.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Module ResponseTimeAnalysisFP.

  Import JobWithJitter UniprocessorScheduleWithJitter SporadicTaskset Priority Schedulability
         WorkloadBoundFP ResponseTimeIterationFP.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  (* In this section, we test the jitter-aware FP RTA on a simple task set
     to show that the theorems contain no contradictory assumptions. *)
  Section ExampleRTA.

    Let tsk1 := {| task_id := 1; task_cost := 1; task_period := 5;
                                 task_deadline := 6; task_jitter := 1 |}.
    Let tsk2 := {| task_id := 2; task_cost := 1; task_period := 5;
                                 task_deadline := 6; task_jitter := 0|}.
    Let tsk3 := {| task_id := 3; task_cost := 1; task_period := 6;
                                 task_deadline := 6; task_jitter := 1|}.

    (* Let ts be a task set containing these three tasks, ... *)
    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.

    (* ...which can be shown to have valid parameters. *)
    Remark ts_has_positive_costs:
      forall tsk, tsk \in ts -> task_cost tsk > 0.
    Proof.
      intros tsk IN.
      by repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
    Qed.
    Remark ts_has_positive_periods:
      forall tsk, tsk \in ts -> task_period tsk > 0.
    Proof.      
      intros tsk IN.
      repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
    Qed.
    
    (* Next, recall the FP RTA schedulability test using RM as the FP policy. *)
    Let RTA_claimed_bounds :=
      fp_claimed_bounds task_cost task_period task_deadline task_jitter (RM task_period).
    Let schedulability_test :=
      fp_schedulable task_cost task_period task_deadline task_jitter (RM task_period).

    (* First, we show that the schedulability test returns the following bounds.
       (Note that although we check the task jitter, these values only include the
        response-time bounds.) *)
    Fact RTA_yields_these_bounds :
      RTA_claimed_bounds ts = Some [:: (tsk1, 2); (tsk2, 2); (tsk3, 3)].
    Proof.
      rewrite /RTA_claimed_bounds /fp_claimed_bounds.
      set RESP := [seq _ | tsk <- ts].
      suff EQ: RESP = [:: (tsk1, Some 2); (tsk2, Some 2); (tsk3, Some 3)].
        by rewrite EQ; compute.
      rewrite /RESP /ts /=; do 2 f_equal.
      {
        rewrite /per_task_rta /=.
        have WORK: total_workload_bound_fp task_cost task_period task_jitter (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk1 1 = 2.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp task_cost task_period task_jitter (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk1 2 = 2.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=.
      }
      f_equal.
      {
        rewrite /per_task_rta /=.
        have WORK: total_workload_bound_fp task_cost task_period task_jitter (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk2 1 = 2.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp task_cost task_period task_jitter (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk2 2 = 2.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=.
      }
      do 2 f_equal.
      {
        rewrite /per_task_rta /=.
        have WORK: total_workload_bound_fp task_cost task_period task_jitter (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk3 1 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp task_cost task_period task_jitter (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk3 3 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=; clear WORK.
      }
    Qed.

    (* Since the response-time bounds plus task jitter are no larger than task deadlines,
       the schedulability test indeed returns true. *)
    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      rewrite /schedulability_test /fp_schedulable -/RTA_claimed_bounds.
      by rewrite RTA_yields_these_bounds.
    Qed.

    (* Now, let's show that the task set is schedulable. *)

    (* Let arr_seq be the periodic arrival sequence from ts... *)
    Let arr_seq := periodic_arrival_sequence ts.

    (* ...subject to rate-monotonic priority. *)
    Let higher_eq_priority := FP_to_JLDP job_task (RM task_period).

    (* Assume that jobs have jitter that is no larger than the jitter of their tasks. *)
     Variable job_jitter: concrete_job -> time.
     Hypothesis H_jitter_is_bounded:
       forall j,
         arrives_in arr_seq j ->
         job_jitter_leq_task_jitter task_jitter job_jitter job_task j.

    (* Next, let sched be the jitter-aware RM schedule with those jitter values. *)
    Let sched := scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority.

    (* To conclude, based on the definition of deadline miss,... *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.

    (* ...we use the result of the jitter-aware FP RTA to conclude that
       no task misses its deadline. *)
    Corollary ts_is_schedulable:
      forall tsk,
        tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
      rename H_jitter_is_bounded into JIT.
      intros tsk IN.
      unfold valid_sporadic_job, valid_realtime_job in *; des.
      apply taskset_schedulable_by_fp_rta with (task_cost := task_cost)
                (task_period := task_period) (task_deadline := task_deadline) (ts0 := ts)
                (higher_eq_priority0 := RM task_period) (job_jitter0 := job_jitter)
                (task_jitter := task_jitter); try (by done).
      - by apply ts_has_positive_costs.
      - by apply ts_has_positive_periods.
      - by apply periodic_arrivals_are_consistent.
      - - apply periodic_arrivals_is_a_set.
      - by apply periodic_arrivals_all_jobs_from_taskset.
      - by apply periodic_arrivals_are_sporadic.
      - by apply periodic_arrivals_job_cost_le_task_cost.
      - by apply periodic_arrivals_job_deadline_eq_task_deadline.
      - by apply RM_is_reflexive.
      - by apply RM_is_transitive.
      - by apply scheduler_jobs_come_from_arrival_sequence.
      - by apply scheduler_jobs_execute_after_jitter.
      - by apply scheduler_completed_jobs_dont_execute.
      - by apply scheduler_work_conserving, periodic_arrivals_are_consistent.
      - apply scheduler_respects_policy; first by apply periodic_arrivals_are_consistent.
        -- by intros t; apply RM_is_transitive.
        -- intros j1 j2 t ARR1 ARR2; apply leq_total.
      - by apply schedulability_test_succeeds.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisFP.