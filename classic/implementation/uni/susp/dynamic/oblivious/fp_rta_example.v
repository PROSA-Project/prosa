Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.schedulability.
Require Import rt.model.schedule.uni.susp.suspension_intervals.
Require Import rt.analysis.uni.basic.workload_bound_fp.
Require Import rt.analysis.uni.susp.dynamic.oblivious.fp_rta.
Require Import rt.implementation.uni.susp.dynamic.job
               rt.implementation.uni.susp.dynamic.task
               rt.implementation.uni.susp.dynamic.arrival_sequence.
Require Import rt.implementation.uni.susp.schedule.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Module ResponseTimeAnalysisFP.

  Import Job UniprocessorSchedule SporadicTaskset Priority Schedulability
         SuspensionIntervals SuspensionObliviousFP WorkloadBoundFP.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  (* In this section, we run the suspension-oblivious FP RTA on a simple task set
     to show that the theorems contain no contradictory assumptions. *)
  Section ExampleRTA.

    Let tsk1 := {| task_id := 1; task_cost := 1; task_period := 5;
                                 task_deadline := 5; task_suspension_bound := 1 |}.
    Let tsk2 := {| task_id := 2; task_cost := 1; task_period := 5;
                                 task_deadline := 5; task_suspension_bound := 0|}.
    Let tsk3 := {| task_id := 3; task_cost := 1; task_period := 6;
                                 task_deadline := 6; task_suspension_bound := 1|}.

    (* Let ts be a task set containing these three tasks, ... *)
    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.

    (* ...which can be shown to have valid parameters. *)
    Fact ts_has_valid_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Proof.
      intros tsk IN.
      repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
    Qed.
    
    (* Now let's inflate the task costs with the suspension-bounds. *)
    Let inflated_cost := inflated_task_cost task_cost task_suspension_bound.

    (* After the inflation, note that the task costs are no larger than deadlines and periods. *)
    Fact inflated_cost_le_deadline_and_period:
      forall tsk,
        tsk \in ts ->
          inflated_cost tsk <= task_deadline tsk /\
          inflated_cost tsk <= task_period tsk.
    Proof.
      intros tsk IN.
      repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
    Qed.
    
    (* Next, recall the FP RTA schedulability test using RM as the FP policy
       and the inflated task costs. *)
    Let RTA_claimed_bounds :=
      fp_claimed_bounds inflated_cost task_period task_deadline (RM task_period).
    Let schedulability_test :=
      fp_schedulable inflated_cost task_period task_deadline (RM task_period).

    (* First, we show that the schedulability test returns the following bounds, ... *)
    Fact RTA_yields_these_bounds :
      RTA_claimed_bounds ts = Some [:: (tsk1, 3); (tsk2, 3); (tsk3, 5)].
    Proof.
      rewrite /RTA_claimed_bounds /fp_claimed_bounds /inflated_cost /inflated_task_cost.
      set RESP := [seq _ | tsk <- ts].
      suff EQ: RESP = [:: (tsk1, Some 3); (tsk2, Some 3); (tsk3, Some 5)] by rewrite EQ; compute.
      rewrite /RESP /ts /=; do 2 f_equal.
      {
        rewrite /per_task_rta /= addn1.
        have WORK: total_workload_bound_fp inflated_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk1 2 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp inflated_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk1 3 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=.
      }
      f_equal.
      {
        rewrite /per_task_rta /= addn0.
        have WORK: total_workload_bound_fp inflated_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk2 1 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp inflated_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk2 3 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=.
      }
      do 2 f_equal.
      {
        rewrite /per_task_rta /= addn1.
        have WORK: total_workload_bound_fp inflated_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk3 2 = 5.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp inflated_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk3 5 = 5.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=; clear WORK.
      }
    Qed.

    (* ...so the schedulability test indeed returns true. *)
    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      rewrite /schedulability_test /fp_schedulable -/RTA_claimed_bounds.
      by rewrite RTA_yields_these_bounds.
    Qed.

    (* Now, let's show that the task set is schedulable. *)

    (* Let arr_seq be the periodic arrival sequence from ts... *)
    Let arr_seq := periodic_arrival_sequence ts.
    
    (* ...where jobs have total suspension times that are no larger than
       the suspension bound of their tasks. *)
     Variable next_suspension: job_suspension concrete_job_eqType.
     Hypothesis H_dynamic_suspensions:
       dynamic_suspension_model job_cost job_task next_suspension task_suspension_bound.

    (* Also assume rate-monotonic priorities. *)
    Let higher_eq_priority := FP_to_JLDP job_task (RM task_period).
     
    (* Next, let sched be the suspension-aware RM schedule with those job suspension times. *)
    Let sched := scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority.

    (* To conclude, based on the definition of deadline miss,... *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.

    (* ...we use the result of the suspension-oblivious FP RTA to conclude that
       no task misses its deadline. *)
    Corollary ts_is_schedulable:
      forall tsk,
        tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
      intros tsk IN.
      have VALID := periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters.
      have TSVALID := ts_has_valid_parameters.
      unfold valid_sporadic_job, valid_realtime_job in *; des.
      apply suspension_oblivious_fp_rta_implies_schedulability with (task_cost := task_cost)
                (task_period := task_period) (task_deadline := task_deadline) (ts0 := ts)
                (higher_eq_priority0 := RM task_period) (next_suspension0 := next_suspension)
                (task_suspension_bound := task_suspension_bound); try (by done).
      - by apply periodic_arrivals_are_consistent.
      - by apply periodic_arrivals_is_a_set.
      - by apply periodic_arrivals_all_jobs_from_taskset.
      - by apply periodic_arrivals_are_sporadic.
      - by apply RM_is_reflexive.
      - by apply RM_is_transitive.
      - by intros tsk_a tsk_b INa INb; apply/orP; apply leq_total.
      - by apply inflated_cost_le_deadline_and_period.
      - by apply scheduler_jobs_come_from_arrival_sequence, periodic_arrivals_are_consistent.
      - by apply scheduler_jobs_must_arrive_to_execute, periodic_arrivals_are_consistent.
      - by apply scheduler_completed_jobs_dont_execute, periodic_arrivals_are_consistent.
      - by apply scheduler_work_conserving, periodic_arrivals_are_consistent.
      - apply scheduler_respects_policy; first by apply periodic_arrivals_are_consistent.
        -- by intros t; apply RM_is_transitive.
        -- by intros j1 j2 _ _ _; apply leq_total.
      - by apply scheduler_respects_self_suspensions, periodic_arrivals_are_consistent.
      - by apply schedulability_test_succeeds.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisFP.