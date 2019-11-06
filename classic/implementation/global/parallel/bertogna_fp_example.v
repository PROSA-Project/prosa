Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.priority.
Require Import rt.model.schedule.global.schedulability.
Require Import rt.model.schedule.global.basic.schedule rt.model.schedule.global.basic.platform
               rt.model.schedule.global.basic.interference.
Require Import rt.analysis.global.parallel.workload_bound
               rt.analysis.global.parallel.interference_bound_fp
               rt.analysis.global.parallel.bertogna_fp_comp.
Require Import rt.implementation.job rt.implementation.task
               rt.implementation.arrival_sequence.
Require Import rt.implementation.global.basic.schedule. (* Use sequential scheduler. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Module ResponseTimeAnalysisFP.

  Import Job Schedule SporadicTaskset Priority Schedulability Platform
         Interference InterferenceBoundFP WorkloadBound
         ResponseTimeIterationFP.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  (* In this section, we instantiate a simple example to show that the theorems
     contain no contradictory assumptions. *)
  Section ExampleRTA.

    Let tsk1 := {| task_id := 1; task_cost := 2; task_period := 6; task_deadline := 6|}.
    Let tsk2 := {| task_id := 2; task_cost := 3; task_period := 8; task_deadline := 6|}.
    Let tsk3 := {| task_id := 3; task_cost := 2; task_period := 12; task_deadline := 12|}.

    (* Let ts be a task set containing these three tasks (sorted by rate-monotonic priority). *)
    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.

    Section FactsAboutTaskset.

      Fact ts_has_valid_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.
      Proof.
        intros tsk IN.
        repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
      Qed.

      Fact ts_has_constrained_deadlines:
        forall tsk,
          tsk \in ts ->
          task_deadline tsk <= task_period tsk.
      Proof.
        intros tsk IN.
        repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
      Qed.
      
    End FactsAboutTaskset.

    (* Assume there are two processors. *)
    Let num_cpus := 2.

    (* Recall the FP RTA schedulability test. *)
    Let schedulability_test :=
      fp_schedulable task_cost task_period task_deadline num_cpus.

    (* Now we show that the schedulability test returns true. *)
    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      unfold schedulability_test, fp_schedulable, fp_claimed_bounds; simpl.
      unfold total_interference_bound_fp, div_floor.
      rewrite big_nil div0n addn0 /=.
      unfold div_floor; simpl.
      set I2 := total_interference_bound_fp task_cost task_period [:: (tsk1, 2)].
      assert (H1: I2 3 = 2).
      {
        by rewrite /I2 /total_interference_bound_fp big_cons big_nil; compute.
      }
      assert (H2: I2 4 = 2).
      {
        by rewrite /I2 /total_interference_bound_fp big_cons big_nil; compute.
      }
      rewrite H1 H2.
      have H3: 3 + 2 %/ num_cpus = 4 by compute.
      rewrite H3 H2 H3 H2 H3.
      have H4: 3 < 6 by compute.
      rewrite H4; clear H4 H2 H1 I2.
      unfold fp_bound_of_task.
      have H5: per_task_rta task_cost task_period num_cpus tsk3 [:: (tsk1, 2); (tsk2, 4)] (max_steps task_cost task_deadline tsk3) = 4.
      {
        Ltac g := rewrite /total_interference_bound_fp /interference_bound_generic
          /W /max_jobs /div_floor /div_ceil !big_cons big_nil /= /higher_priority_task /= ?addn0; compute.
        rewrite /per_task_rta iterSr /div_floor.
        set x10 := total_interference_bound_fp  _ _ _ _.
        have I10: x10 = 5 by unfold x10; g.
        rewrite I10 iterSr.
        set x9 := total_interference_bound_fp  _ _ _ _.
        have I9: x9 = 5 by unfold x9; g.
        rewrite I9 iterSr.
        set x8 := total_interference_bound_fp  _ _ _ _.
        have I8: x8 = 5 by unfold x8; g.
        rewrite I8 iterSr.
        set x7 := total_interference_bound_fp  _ _ _ _.
        have I7: x7 = 5 by unfold x7; g.
        rewrite I7 iterSr.
        set x6 := total_interference_bound_fp  _ _ _ _.
        have I6: x6 = 5 by unfold x6; g.
        rewrite I6 iterSr.
        set x5 := total_interference_bound_fp  _ _ _ _.
        have I5: x5 = 5 by unfold x5; g.
        rewrite I5 iterSr.
        set x4 := total_interference_bound_fp  _ _ _ _.
        have I4: x4 = 5 by unfold x4; g.
        rewrite I4 iterSr.
        set x3 := total_interference_bound_fp  _ _ _ _.
        have I3: x3 = 5 by unfold x3; g.
        rewrite I3 iterSr.
        set x2 := total_interference_bound_fp  _ _ _ _.
        have I2: x2 = 5 by unfold x2; g.
        rewrite I2 iterSr.
        set x1 := total_interference_bound_fp  _ _ _ _.
        have I1: x1 = 5 by unfold x1; g.
        rewrite I1 iterSr.
        set x0 := total_interference_bound_fp  _ _ _ _.
        have I0: x0 = 5 by unfold x0; g.
        by rewrite /= I0; compute.
      }
      by rewrite H5.
    Qed.

    (* Let arr_seq be the periodic arrival sequence from ts. *)
    Let arr_seq := periodic_arrival_sequence ts.

    (* Assume rate-monotonic priorities. *)
    Let higher_priority := FP_to_JLDP job_task (RM task_period).

    Section FactsAboutPriorityOrder.

      Lemma ts_has_unique_priorities :
        FP_is_antisymmetric_over_task_set (RM task_period) ts.
      Proof.
        unfold RM; intros tsk tsk' IN IN' HP HP'.
        have EQ: task_period tsk = task_period tsk' by apply/eqP; rewrite eqn_leq HP HP'.
        clear HP HP'.
        rewrite !in_cons 2!in_nil 2!orbF in IN IN'; des; rewrite IN IN'; try (by done);
        subst tsk tsk'; simpl in *; by done.
      Qed.

      Lemma priority_is_total :
        FP_is_total_over_task_set (RM task_period) ts.
      Proof.
        unfold RM; intros tsk tsk' IN IN'.
        destruct (leqP (task_period tsk) (task_period tsk'));
          [by left | by right; apply ltnW].
      Qed.
      
    End FactsAboutPriorityOrder.
      
    (* Let sched be the work-conserving RM scheduler. *)
    Let sched := scheduler job_arrival job_cost num_cpus arr_seq higher_priority.

    (* Recall the definition of deadline miss. *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.

    (* Next, we prove that ts is schedulable with the result of the test. *)
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
       (ts0 := ts) (higher_priority0 := RM task_period); try (by done).
      - by apply ts_has_constrained_deadlines.
      - by apply ts_has_unique_priorities.
      - by apply priority_is_total.
      - by apply RM_is_transitive.
      - by apply periodic_arrivals_all_jobs_from_taskset.
      - by apply periodic_arrivals_are_sporadic.
      - by apply scheduler_jobs_come_from_arrival_sequence.
      - by apply scheduler_jobs_must_arrive_to_execute.
      - apply scheduler_completed_jobs_dont_execute.
        -- by apply periodic_arrivals_are_consistent.
        -- by apply periodic_arrivals_is_a_set.
      - by apply scheduler_work_conserving, periodic_arrivals_are_consistent.
      - apply scheduler_respects_policy.
        -- by apply periodic_arrivals_are_consistent.
        -- by intros t; apply RM_is_transitive.
        -- by intros t x y; apply leq_total.
      - by apply schedulability_test_succeeds.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisFP.