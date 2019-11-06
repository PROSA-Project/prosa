Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.schedulability.
Require Import rt.analysis.uni.basic.workload_bound_fp
               rt.analysis.uni.basic.fp_rta_comp.
Require Import rt.implementation.job rt.implementation.task
               rt.implementation.arrival_sequence.
Require Import rt.implementation.uni.basic.schedule.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Module ResponseTimeAnalysisFP.

  Import Job UniprocessorSchedule SporadicTaskset Priority Schedulability
         WorkloadBoundFP ResponseTimeIterationFP.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  (* In this section, we run the FP RTA on a simple task set to show that the theorems
     contain no contradictory assumptions. *)
  Section ExampleRTA.

    Let tsk1 := {| task_id := 1; task_cost := 1; task_period := 4; task_deadline := 5|}.
    Let tsk2 := {| task_id := 2; task_cost := 1; task_period := 6; task_deadline := 5|}.
    Let tsk3 := {| task_id := 3; task_cost := 1; task_period := 6; task_deadline := 6|}.

    (* Let ts be a task set containing these three tasks.
       (Note that periods are not unique and one of the tasks has an arbitrary deadline.) *)
    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.


    (* Also note that the task set has valid parameters. *)
    Fact ts_has_valid_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Proof.
      intros tsk IN.
      repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
    Qed.

    (* Next, recall the FP RTA schedulability test using RM as the FP policy. *)
    Let RTA_claimed_bounds :=
      fp_claimed_bounds task_cost task_period task_deadline (RM task_period).
    Let schedulability_test :=
      fp_schedulable task_cost task_period task_deadline (RM task_period).

    (* First, we show that the schedulability test returns the following bounds, ... *)
    Fact RTA_yields_these_bounds :
      RTA_claimed_bounds ts = Some [:: (tsk1, 1); (tsk2, 3); (tsk3, 3)].
    Proof.
      rewrite /RTA_claimed_bounds /fp_claimed_bounds.
      set RESP := [seq _ | tsk <- ts].
      suff EQ: RESP = [:: (tsk1, Some 1); (tsk2, Some 3); (tsk3, Some 3)] by rewrite EQ; compute.
      rewrite /RESP /ts /=; do 2 f_equal.
      {
        rewrite /per_task_rta /=.
        have WORK: total_workload_bound_fp task_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk1 1 = 1.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=.
      }
      f_equal.
      {
        rewrite /per_task_rta /=.
        have WORK: total_workload_bound_fp task_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk2 1 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp task_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk2 3 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        by rewrite !WORK /=.
      }
      do 2 f_equal.
      {
        rewrite /per_task_rta /=.
        have WORK: total_workload_bound_fp task_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk3 1 = 3.
        {
          by compute; rewrite unlock; compute.
        }
        rewrite !WORK /=; clear WORK.
        have WORK: total_workload_bound_fp task_cost task_period (RM task_period)
                                                 [:: tsk1; tsk2; tsk3] tsk3 3 = 3.
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

    (* Let arr_seq be the periodic arrival sequence from ts. *)
    Let arr_seq := periodic_arrival_sequence ts.
    
    (* Assume rate-monotonic priorities... *)
    Let higher_eq_priority := FP_to_JLDP job_task (RM task_period).

    (* ... and recall that this priority assignment is total. *)
    Fact priority_is_total:
      forall t, total (higher_eq_priority t).
    Proof.
      rewrite /higher_eq_priority /FP_to_JLDP /RM /FP_to_JLFP.
      intros t x y; apply/orP.
      case LEQ: (_ <= _); first by left.
      apply negbT in LEQ; rewrite -ltnNge in LEQ.
      by right; apply ltnW.
    Qed.
      
    (* Let sched be the work-conserving RM scheduler. *)
    Let sched := scheduler job_arrival job_cost arr_seq higher_eq_priority.

    (* Recall the definition of deadline miss. *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.

    (* Next, by using the result of the RTA, we prove that the task set is schedulable. *)
    Corollary ts_is_schedulable:
      forall tsk,
        tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
      intros tsk IN.
      have VALID := periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters.
      have TSVALID := ts_has_valid_parameters.
      unfold valid_sporadic_job, valid_realtime_job in *; des.
      apply taskset_schedulable_by_fp_rta with (task_cost := task_cost)
       (task_period := task_period) (task_deadline := task_deadline)
       (ts0 := ts) (higher_eq_priority0 := RM task_period); try (by done).
      - by apply periodic_arrivals_are_consistent.
      - by apply periodic_arrivals_is_a_set.
      - by apply periodic_arrivals_all_jobs_from_taskset.
      - by apply periodic_arrivals_are_sporadic.
      - by apply RM_is_reflexive.
      - by apply RM_is_transitive.
      - by apply scheduler_jobs_come_from_arrival_sequence, periodic_arrivals_are_consistent.
      - by apply scheduler_jobs_must_arrive_to_execute, periodic_arrivals_are_consistent.
      - apply scheduler_completed_jobs_dont_execute, periodic_arrivals_are_consistent.
      - by apply scheduler_work_conserving, periodic_arrivals_are_consistent.
      - apply scheduler_respects_policy; first by apply periodic_arrivals_are_consistent.
        -- by intros t; apply RM_is_transitive.
        -- by apply priority_is_total. 
      - by apply schedulability_test_succeeds.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisFP.