Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.priority.
Require Import rt.model.schedule.global.schedulability.
Require Import rt.model.schedule.global.basic.schedule.
Require Import rt.model.schedule.apa.affinity rt.model.schedule.apa.interference rt.model.schedule.apa.platform.
Require Import rt.analysis.apa.workload_bound
               rt.analysis.apa.interference_bound_edf
               rt.analysis.apa.bertogna_edf_comp.
Require Import rt.implementation.apa.job
               rt.implementation.apa.task
               rt.implementation.apa.schedule
               rt.implementation.apa.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype bigop div.

Module ResponseTimeAnalysisEDF.

  Import Job Schedule SporadicTaskset Priority Schedulability
         Affinity Platform InterferenceBoundEDF WorkloadBound
         Interference ResponseTimeIterationEDF.
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
          tsk \in ts ->
          #|task_affinity tsk| > 0.
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

    (* Next, recall the EDF RTA schedulability test for APA scheduling.
       Note that the task functions (from implementation/apa/task.v)
       require num_cpus as a parameter, so we leave a blank space so that
       can be inferred automatically. *)
    Let schedulability_test :=
      edf_schedulable (@task_cost _) (@task_period _)
                      (@task_deadline _) num_cpus task_affinity
                      task_affinity. (* For simplicity, we use subaffinity alpha' = alpha. *)

    (* Now, we guide Coq to compute the schedulability test function
       and show it returns true. *)
    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      unfold schedulability_test, edf_schedulable, edf_claimed_bounds; desf.
      apply negbT in Heq; move: Heq => /negP ALL.
      exfalso; apply ALL; clear ALL.
      assert (STEPS: \sum_(tsk <- ts) (task_deadline tsk - task_cost tsk) + 1 = 13).
      {
        by rewrite unlock; compute.
      } rewrite STEPS; clear STEPS.

      Local Ltac f :=
        unfold edf_rta_iteration; simpl;
        unfold edf_response_time_bound, div_floor, total_interference_bound_edf, interference_bound_edf, interference_bound_generic, W, edf_specific_interference_bound, different_task_in, affinity_intersects; simpl;
        rewrite !addnE !set_card !big_cons ?big_nil /=.

      Local Ltac g := destruct master_key; f; simpl_exists_ord.      
      rewrite [edf_rta_iteration]lock; simpl.
      unfold locked at 13; g.
      unfold locked at 12; g.
      unfold locked at 11; g.
      unfold locked at 10; g.
      unfold locked at 9; g.
      unfold locked at 8; g.
      unfold locked at 7; g.
      unfold locked at 6; g.
      unfold locked at 5; g.
      unfold locked at 4; g.
      unfold locked at 3; g.
      unfold locked at 2; g.
      by unfold locked at 1; g.
    Qed.

    (* Let arr_seq be the periodic arrival sequence from ts. *)
    Let arr_seq := periodic_arrival_sequence ts.

    (* Let sched be the weak APA EDF scheduler. *)
    Let sched := scheduler job_arrival job_cost job_task num_cpus arr_seq task_affinity
                           (JLFP_to_JLDP (EDF job_arrival job_deadline)).

    (* Recall the definition of deadline miss. *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.

    (* To show that the RTA works, we infer the schedulability of the task
       set from the result of the RTA procedure. *)
    Corollary ts_is_schedulable:
      forall tsk,
        tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
      intros tsk IN.
      have VALID := periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters.
      have VALIDTS := ts_has_valid_parameters.
      unfold valid_sporadic_job, valid_realtime_job in *; des.
      apply taskset_schedulable_by_edf_rta with (task_cost := task_cost) (task_period := task_period)
        (task_deadline := task_deadline) (alpha := task_affinity) (alpha' := task_affinity)
        (ts0 := ts); try (by done).
      - by apply ts_has_constrained_deadlines.
      - by apply ts_non_empty_affinities.
      - by ins.
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

End ResponseTimeAnalysisEDF.