Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.apa.interference prosa.classic.model.schedule.apa.affinity prosa.classic.model.schedule.apa.platform.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module ConstrainedDeadlines.

  Import Job SporadicTaskset ScheduleOfSporadicTask SporadicTaskset
         TaskArrival Interference Priority Affinity Platform.
  
  Section Lemmas.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence ... *)
    Variable arr_seq: arrival_sequence Job.

    (* ... and any schedule of this arrival sequence. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.

    (* Assume that every task has a processor affinity alpha. *)
    Variable alpha: task_affinity sporadic_task num_cpus.
    
    (* Assume all jobs have valid parameters, ...*)
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* In this section we prove the absence of multiple jobs of the same
       task when constrained deadlines are assumed.  *)
    Section NoMultipleJobs.

      (* Assume any work-conserving priority-based scheduler. *)
      Variable higher_eq_priority: JLDP_policy Job.
      Hypothesis H_work_conserving:
        apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha.
      Hypothesis H_respects_JLDP_policy:
        respects_JLDP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
                                            sched alpha higher_eq_priority.

      (* Consider task set ts. *)
      Variable ts: taskset_of sporadic_task.

      (* Assume that all jobs come from the taskset. *)
      Hypothesis H_all_jobs_from_taskset:
        forall j, arrives_in arr_seq j -> job_task j \in ts.

      (* Suppose that jobs are sequential, ...*)
      Hypothesis H_sequential_jobs: sequential_jobs sched.
      (* ... jobs only execute after they arrive, ... *)
      Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
      (* ... and jobs do not execute after completion. *)
      Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

      (* Assume that the schedule satisfies the sporadic task model ...*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period job_arrival job_task arr_seq. 

      (* Consider a valid task tsk, ...*)
      Variable tsk: sporadic_task.
      Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.

      (*... whose job j ... *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (*... is backlogged at time t. *)
      Variable t: time.
      Hypothesis H_j_backlogged: backlogged job_arrival job_cost sched j t.

      (* Assume that any previous jobs of tsk have completed by the period. *)
      Hypothesis H_all_previous_jobs_completed :
        forall j_other tsk_other,
          arrives_in arr_seq j_other ->
          job_task j_other = tsk_other ->
          job_arrival j_other + task_period tsk_other <= t ->
          completed job_cost sched j_other (job_arrival j_other + task_period (job_task j_other)).

      Let scheduled_task_other_than (tsk tsk_other: sporadic_task) :=
        task_is_scheduled job_task sched tsk_other t && (tsk_other != tsk).

      (* Then, there can be at most one pending job of each task at time t. *)
      Lemma platform_at_most_one_pending_job_of_each_task :
        forall j1 j2,
          arrives_in arr_seq j1 ->
          arrives_in arr_seq j2 ->
          pending job_arrival job_cost sched j1 t ->
          pending job_arrival job_cost sched j2 t ->
          job_task j1 = job_task j2 ->
          j1 = j2.
      Proof.
        rename H_sporadic_tasks into SPO, H_all_previous_jobs_completed into PREV.
        intros j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF. 
        move: PENDING1 PENDING2 => /andP [ARRIVED1 /negP NOTCOMP1] /andP [ARRIVED2 /negP NOTCOMP2].
        destruct (leqP (job_arrival j1) (job_arrival j2)) as [BEFORE1 | BEFORE2].
        {
          specialize (SPO j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1).
          assert (LEt: job_arrival j1 + task_period (job_task j1) <= t).
          {
            by apply leq_trans with (n := job_arrival j2); first by done.
          }
          exploit (PREV j1 (job_task j1)); try (by done).
          intros COMP1; apply NOTCOMP1.
          by apply completion_monotonic with (t0 := job_arrival j1 + task_period (job_task j1)). 
        }
        {
          apply ltnW in BEFORE2.
          exploit (SPO j2 j1); try (by done); [by red; ins; subst | intro SPO'].
          assert (LEt: job_arrival j2 + task_period (job_task j2) <= t).
          {
            by apply leq_trans with (n := job_arrival j1); first by done.
          }
          exploit (PREV j2 (job_task j2)); try (by done).
          intros COMP2; apply NOTCOMP2.
          by apply completion_monotonic with (t0 := job_arrival j2 + task_period (job_task j2)).
        }
      Qed.

    End NoMultipleJobs.

    (* In this section we also prove the absence of multiple jobs of the same
       task when constrained deadlines are assumed, but in the specific case
       of fixed-priority scheduling.  *)
    Section NoMultipleJobsFP.

      (* Assume any work-conserving priority-based scheduler. *)
      Variable higher_eq_priority: FP_policy sporadic_task.
      Hypothesis H_work_conserving: apa_work_conserving job_arrival job_cost job_task
                                                        arr_seq sched alpha.
      Hypothesis H_respects_JLDP_policy:
        respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
                                          sched alpha higher_eq_priority.

      (* Consider any task set ts. *)
      Variable ts: taskset_of sporadic_task.

      (* Assume that all jobs come from the taskset. *)
      Hypothesis H_all_jobs_from_taskset:
        forall j, arrives_in arr_seq j -> job_task j \in ts.

      (* Suppose that jobs are sequential, ...*)
      Hypothesis H_sequential_jobs: sequential_jobs sched.
      (* ... jobs only execute after the jitter, ... *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched.
      (* ... and jobs do not execute after completion. *)
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      (* Assume that the schedule satisfies the sporadic task model ...*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period job_arrival job_task arr_seq.

      (* Consider a valid task tsk, ...*)
      Variable tsk: sporadic_task.
      Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.

      (*... whose job j ... *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Variable H_job_of_tsk: job_task j = tsk.

      (*... is backlogged at time t <= job_arrival j + task_period tsk. *)
      Variable t: time.
      Hypothesis H_j_backlogged: backlogged job_arrival job_cost sched j t.
      Hypothesis H_t_before_period: t < job_arrival j + task_period tsk.

      (* Recall the definition of a higher-priority task in affinity (alpha' tsk). *)
      Let hp_task_in alpha' := higher_priority_task_in alpha higher_eq_priority tsk alpha'.

      (* Assume that any jobs of higher-priority tasks complete by their period. *)
      Hypothesis H_all_previous_jobs_completed :
        forall j_other tsk_other,
          arrives_in arr_seq j_other ->
          job_task j_other = tsk_other ->
          hp_task_in (alpha tsk) tsk_other ->
          completed job_cost sched j_other (job_arrival j_other + task_period tsk_other).

      (* Assume that any jobs of tsk prior to j complete by their period. *)
      Hypothesis H_all_previous_jobs_of_tsk_completed :
        forall j0,
          arrives_in arr_seq j0 ->
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + task_period tsk).
      
      Definition scheduled_task_with_higher_eq_priority (tsk tsk_other: sporadic_task) :=
        task_is_scheduled job_task sched tsk_other t &&
        hp_task_in (alpha tsk) tsk_other.
                             
      (* Then, there can be at most one pending job of higher-priority tasks at time t. *)
      Lemma platform_fp_no_multiple_jobs_of_interfering_tasks :
          forall j1 j2,
            arrives_in arr_seq j1 ->
            arrives_in arr_seq j2 ->
            pending job_arrival job_cost sched j1 t ->
            pending job_arrival job_cost sched j2 t ->
            job_task j1 = job_task j2 ->
            hp_task_in (alpha tsk) (job_task j1) ->
            j1 = j2.
      Proof.
        unfold sporadic_task_model in *.
        rename H_sporadic_tasks into SPO, H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_all_previous_jobs_completed into PREV.
        intros j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk INTERF.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF.
        move: PENDING1 PENDING2 => /andP [ARRIVED1 /negP NOTCOMP1] /andP [ARRIVED2 /negP NOTCOMP2].
        destruct (leqP (job_arrival j1) (job_arrival j2)) as [BEFORE1 | BEFORE2].
        {
          specialize (SPO j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1).
          assert (LEt: job_arrival j1 + task_period (job_task j1) <= t).
            by apply leq_trans with (n := job_arrival j2).
          exploit (PREV j1 (job_task j1) ARR1); [by done | by apply INTERF | intros COMP1].
          apply NOTCOMP1.
          by apply completion_monotonic with (t0 := job_arrival j1 + task_period (job_task j1)). 
        }
        {
          apply ltnW in BEFORE2.
          exploit (SPO j2 j1); try (by done); [by red; ins; subst j2 | intro SPO'].
          assert (LEt: job_arrival j2 + task_period (job_task j2) <= t).
            by apply leq_trans with (n := job_arrival j1).
          exploit (PREV j2 (job_task j2) ARR2);
            [by done | by rewrite -SAMEtsk | intro COMP2 ].
          apply NOTCOMP2.
          by apply completion_monotonic with (t0 := job_arrival j2 + task_period (job_task j2)).
        }
      Qed.
      
      (* Also, there can be at most one pending job of tsk at time t. *)
      Lemma platform_fp_no_multiple_jobs_of_tsk :
        forall j',
          arrives_in arr_seq j' ->
          pending job_arrival job_cost sched j' t ->
          job_task j' = tsk ->
          j' = j.
      Proof.
        unfold sporadic_task_model in *.
        rename H_sporadic_tasks into SPO,
               H_valid_task into PARAMS,
               H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_all_previous_jobs_completed into PREV,
               H_j_backlogged into BACK, H_job_of_tsk into JOBtsk.
        intros j' ARR' PENDING' SAMEtsk.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF.
        move: BACK PENDING' => /andP [/andP [ARRIVED /negP NOTCOMP] NOTSCHED]
                               /andP [ARRIVED' /negP NOTCOMP'].
        destruct (leqP (job_arrival j') (job_arrival j)) as [BEFORE | BEFORE'].
        {
          exploit (SPO j' j DIFF ARR' H_j_arrives); [by rewrite JOBtsk | by done | intro SPO'].
          assert (LEt: job_arrival j' + task_period tsk <= t).
            by apply leq_trans with (n := job_arrival j); first by rewrite -SAMEtsk.
          apply NOTCOMP'.
          apply completion_monotonic with (t0 := job_arrival j' + task_period tsk); [by done |].
          apply PREVtsk; try (by done).
          apply leq_trans with (n := job_arrival j' + task_period tsk); last by rewrite -SAMEtsk.
          rewrite -addn1; apply leq_add; first by done.
          by unfold is_valid_sporadic_task in *; des.
        }
        {
          unfold has_arrived in *.
          rewrite leqNgt in ARRIVED'; move: ARRIVED' => /negP BUG; apply BUG.
          apply leq_trans with (n := job_arrival j + task_period tsk); first by done.
          by rewrite -JOBtsk; apply SPO; try (by done);
            [by red; ins; subst j' | by rewrite SAMEtsk | by apply ltnW].
        }
      Qed.
      
    End NoMultipleJobsFP.
    
  End Lemmas.

End ConstrainedDeadlines.