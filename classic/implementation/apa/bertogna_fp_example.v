Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.priority.
Require Import rt.model.schedule.global.schedulability.
Require Import rt.model.schedule.global.basic.schedule.
Require Import rt.model.schedule.apa.affinity rt.model.schedule.apa.interference rt.model.schedule.apa.platform.
Require Import rt.analysis.apa.workload_bound
               rt.analysis.apa.interference_bound_fp
               rt.analysis.apa.bertogna_fp_comp.
Require Import rt.implementation.apa.job
               rt.implementation.apa.task
               rt.implementation.apa.schedule
               rt.implementation.apa.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype fintype seq bigop div.

Module ResponseTimeAnalysisFP.

  Import Job Schedule SporadicTaskset Priority Schedulability Platform
         Interference InterferenceBoundFP WorkloadBound
         ResponseTimeIterationFP Affinity.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  (* In this section, we instantiate a simple example to show that the theorems
     contain no contradictory assumptions. *)  
  Section ExampleRTA.

    (* Assume there are two processors. *)
    Let num_cpus := 2.

    (* Let (cpu j) denote the j-th processor *)
    Let cpu j := @Ordinal num_cpus j.

    (* Define alpha1 := {cpu 0, cpu 1} with the two processors. *)
    Program Let alpha1 : affinity num_cpus :=
      (Build_set [:: cpu 0 _; cpu 1 _] _).

    (* Define the singleton affinity alpha2 := {cpu 0}. *)
    Program Let alpha2 : affinity num_cpus :=
      (Build_set [:: cpu 0 _] _).

    (* Define the singleton affinity alpha3 := {cpu 1}. *)
    Program Let alpha3 : affinity num_cpus :=
      (Build_set [:: cpu 1 _] _).

    (* Now we create three tasks using the affinities above ... *)
    Let tsk1 := {| task_id := 1; task_cost := 3; task_period := 5;
                   task_deadline := 3; task_affinity := alpha1|}.
    Let tsk2 := {| task_id := 2; task_cost := 2; task_period := 6;
                   task_deadline := 5; task_affinity  := alpha2|}.
    Let tsk3 := {| task_id := 3; task_cost := 2; task_period := 12;
                   task_deadline := 11; task_affinity := alpha3|}.

    (* ... and group these tasks into task set ts. *)
    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.

    (* In this section, we let Coq compute a few properties about ts. *)
    Section FactsAboutTaskset.

      (* There are no empty affinities. *)
      Fact ts_non_empty_affinities:
        forall tsk, 
          tsk \in ts -> #|task_affinity tsk| > 0.
      Proof.
        intros tsk IN.
        by repeat (move: IN => /orP [/eqP EQ | IN]; subst; rewrite ?set_card; compute).
      Qed.

      (* The tasks have valid parameters (e.g., cost > 0). *)
      Fact ts_has_valid_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.
      Proof.
        intros tsk IN.
        by repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute).
      Qed.

      (* The task set has constrained deadlines. *)
      Fact ts_has_constrained_deadlines:
        forall tsk,
          tsk \in ts ->
          task_deadline tsk <= task_period tsk.
      Proof.
        intros tsk IN.
        by repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute).
      Qed.

    End FactsAboutTaskset.

    (* Then, let arr_seq be the periodic arrival sequence from ts. *)
    Let arr_seq := periodic_arrival_sequence ts.

    (* Assume rate-monotonic priorities. *) 
    Let higher_priority : JLDP_policy (@concrete_job_eqType num_cpus) :=
      FP_to_JLDP job_task (RM task_period).

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
    
    (* Next, recall the FP RTA schedulability test for APA scheduling.
       Note that the task functions (from implementation/apa/task.v)
       require num_cpus as a parameter, so we leave a blank space so that
       can be inferred automatically. *)
    Let schedulability_test :=
      fp_schedulable (@task_cost _) (@task_period _) (@task_deadline _)
                     num_cpus (RM task_period) task_affinity
                     task_affinity. (* For simplicity, we use subaffinity alpha' = alpha. *)

    (* Now we show that the schedulability test returns true. *)
    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      unfold schedulability_test, fp_schedulable, fp_claimed_bounds; simpl.
      unfold total_interference_bound_fp, div_floor.
      rewrite big_nil div0n addn0 /=.
      unfold div_floor; rewrite !set_card /=.   

      set I2 := total_interference_bound_fp task_cost task_period
                        task_affinity tsk2 alpha2  [:: (tsk1, 3)].

      assert (H1: I2 2 (RM task_period) = 1).
      {
        unfold I2, total_interference_bound_fp; rewrite big_cons big_nil.
        unfold higher_priority_task_in; simpl.
        by rewrite /affinity_intersects; simpl_exists_ord; compute.
      }
      rewrite H1 !divn1 !addn1; clear H1.
      assert (H1: I2 3 (RM task_period) = 2).
      {
        unfold I2, total_interference_bound_fp; rewrite big_cons big_nil.
        unfold higher_priority_task_in; simpl.
        by rewrite /affinity_intersects; simpl_exists_ord; compute.
      }
      rewrite H1 !addn2; clear H1.
      assert (H1: I2 4 (RM task_period) = 3).
      {
        unfold I2, total_interference_bound_fp; rewrite big_cons big_nil.
        unfold higher_priority_task_in; simpl.
        by rewrite /affinity_intersects; simpl_exists_ord; compute.
      }
      rewrite H1 !addn3; clear H1.
      assert (H1: I2 5 (RM task_period) = 3).
      {
        unfold I2, total_interference_bound_fp; rewrite big_cons big_nil.
        unfold higher_priority_task_in; simpl.
        by rewrite /affinity_intersects; simpl_exists_ord; compute.
      }
      rewrite H1 !addn3; clear H1.
      have H2: 4 < 5 by compute.
      rewrite H2; clear H2 I2.
      unfold fp_bound_of_task.

      Ltac f := unfold div_floor;
                rewrite !big_cons big_nil /= /higher_priority_task_in /=
                        /affinity_intersects !addn0 /= ?set_card ?divn1 ?addn0;
                unfold interference_bound_generic, W, max_jobs, div_floor;
                rewrite addn1 ?addn0.

      have H4: per_task_rta task_cost task_period num_cpus (RM task_period) task_affinity task_affinity tsk3 [:: (tsk1, 3); (tsk2, 5)]
                            (max_steps task_cost task_deadline tsk3) = 5.
      {
        rewrite /per_task_rta iterSr /div_floor set_card.
        Ltac g :=
            rewrite /total_interference_bound_fp /interference_bound_generic
                    /W /max_jobs /div_floor !big_cons big_nil /= /higher_priority_task_in /=
                    /affinity_intersects.

        set x9 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I9: x9 = 1 by unfold x9; g; simpl_exists_ord; compute.
        rewrite I9 iterSr.
        set x8 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I8: x8 = 2 by unfold x8; g; simpl_exists_ord; compute.
        rewrite I8 iterSr.
        set x7 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I7: x7 = 3 by unfold x7; g; simpl_exists_ord; compute.
        rewrite I7 iterSr.
        set x6 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I6: x6 = 3 by unfold x6; g; simpl_exists_ord; compute.
        rewrite I6 iterSr.
        set x5 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I5: x5 = 3 by unfold x5; g; simpl_exists_ord; compute.
        rewrite I5 iterSr.
        set x4 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I4: x4 = 3 by unfold x4; g; simpl_exists_ord; compute.
        rewrite I4 iterSr.
        set x3 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I3: x3 = 3 by unfold x3; g; simpl_exists_ord; compute.
        rewrite I3 iterSr.
        set x2 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I2: x2 = 3 by unfold x2; g; simpl_exists_ord; compute.
        rewrite I2 iterSr.
        set x1 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I1: x1 = 3 by unfold x1; g; simpl_exists_ord; compute.
        rewrite I1 iterSr /=.
        set x0 := total_interference_bound_fp _ _ _ _ _ _ _ _.
        have I0: x0 = 3 by unfold x0; g; simpl_exists_ord; compute.
        by rewrite I0; compute.
      }
      by rewrite H4.
    Qed.

    (* Let sched be the work-conserving RM APA scheduler. *)
    Let sched :=
      scheduler job_arrival job_cost job_task num_cpus arr_seq task_affinity higher_priority.

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
       (ts0 := ts) (higher_priority0 := RM task_period)
       (alpha := task_affinity) (alpha' := task_affinity); try (by done).
      - by apply ts_has_constrained_deadlines.
      - by apply ts_non_empty_affinities.
      - by ins.
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
      - apply scheduler_sequential_jobs.
        -- by apply periodic_arrivals_are_consistent.
        -- by apply periodic_arrivals_is_a_set. 
      - by apply scheduler_respects_affinity.
      - apply scheduler_apa_work_conserving.
        -- by apply periodic_arrivals_are_consistent.
        -- by apply periodic_arrivals_is_a_set.
        -- by intros t; apply RM_is_transitive.
        -- by intros t x y; apply leq_total.
      - apply scheduler_respects_policy.
        -- by apply periodic_arrivals_are_consistent.
        -- by apply periodic_arrivals_is_a_set.
        -- by intros t; apply RM_is_transitive.
        -- by intros t x y; apply leq_total.
      - by apply schedulability_test_succeeds.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisFP.