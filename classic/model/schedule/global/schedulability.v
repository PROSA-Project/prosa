Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.global.basic.schedule.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq bigop.

(* Definitions of deadline miss. *)
Module Schedulability.

  Import Schedule SporadicTaskset Job.

  Section SchedulableDefs.

    Context {sporadic_task: eqType}.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any multiprocessor schedule of these jobs. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    Section ScheduleOfJobs.

      (* Let j be any job. *)
      Variable j: Job.

      (* We say that job j misses no deadline in sched if it completed by its absolute deadline. *)
      Definition job_misses_no_deadline :=
        completed job_cost sched j (job_arrival j + job_deadline j).

    End ScheduleOfJobs.

    Section ScheduleOfTasks.

      (* Consider any task tsk. *)
      Variable tsk: sporadic_task.

      (* Task tsk doesn't miss its deadline iff all of its jobs don't miss their deadline. *)
      Definition task_misses_no_deadline :=
        forall j,
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_misses_no_deadline j.

      (* Task tsk doesn't miss its deadline before time t' iff all of its jobs don't miss
         their deadline by that time. *)
      Definition task_misses_no_deadline_before (t': time) :=
        forall j,
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_arrival j + job_deadline j < t' ->
          job_misses_no_deadline j.

    End ScheduleOfTasks.

  End SchedulableDefs.

  Section BasicLemmas.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any schedule of these jobs... *)
    Context {num_cpus : nat}.
    Variable sched: schedule Job num_cpus.

    (* ... where jobs dont execute after completion. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    Section SpecificJob.

      (* Then, for any job j ...*)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.

      (* ...that doesn't miss a deadline in this schedule, ... *)
      Hypothesis no_deadline_miss:
        job_misses_no_deadline job_arrival job_cost job_deadline sched j.

      (* the service received by j at any time t' after its deadline is 0. *)
      Lemma service_after_job_deadline_zero :
        forall t',
          t' >= job_arrival j + job_deadline j ->
          service_at sched j t' = 0.
      Proof.
        intros t' LE.
        rename no_deadline_miss into RT,
               H_completed_jobs_dont_execute into EXEC.
        unfold job_misses_no_deadline, completed, completed_jobs_dont_execute in *.
        apply/eqP; rewrite -leqn0.
        eapply completion_monotonic in RT; eauto 2.
        apply completed_implies_not_scheduled in RT; eauto 2.
          by move: RT; rewrite not_scheduled_no_service; move => /eqP RT; rewrite RT.
      Qed.

      (* The same applies for the cumulative service of job j. *)
      Lemma cumulative_service_after_job_deadline_zero :
        forall t' t'',
          t' >= job_arrival j + job_deadline j ->
          \sum_(t' <= t < t'') service_at sched j t = 0.
      Proof.
        ins; apply/eqP; rewrite -leqn0.
        rewrite big_nat_cond; rewrite -> eq_bigr with (F2 := fun i => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
        intro i; rewrite andbT; move => /andP [LE _].
        by rewrite service_after_job_deadline_zero;
          [by ins | by apply leq_trans with (n := t')].
      Qed.
      
    End SpecificJob.
    
    Section AllJobs.

      (* Consider any task tsk ...*)
      Variable tsk: sporadic_task.

      (* ... that doesn't miss any deadline. *)
      Hypothesis no_deadline_misses:
        task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.

      (* Then, for any valid job j of this task, ...*)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_task: job_task j = tsk.
      Hypothesis H_valid_job:
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
      
      (* the service received by job j at any time t' after the deadline is 0. *)
      Lemma service_after_task_deadline_zero :
        forall t',
          t' >= job_arrival j + task_deadline tsk ->
          service_at sched j t' = 0.
      Proof.
        rename H_valid_job into PARAMS; unfold valid_sporadic_job in *; des; intros t'.
        rewrite -H_job_of_task -PARAMS1.
        by apply service_after_job_deadline_zero, no_deadline_misses.
      Qed.

      (* The same applies for the cumulative service of job j. *)
      Lemma cumulative_service_after_task_deadline_zero :
        forall t' t'',
          t' >= job_arrival j + task_deadline tsk ->
          \sum_(t' <= t < t'') service_at sched j t = 0.
      Proof.
        rename H_valid_job into PARAMS; unfold valid_sporadic_job in *; des; intros t' t''.
        rewrite -H_job_of_task -PARAMS1.
        by apply cumulative_service_after_job_deadline_zero, no_deadline_misses.
      Qed.
      
    End AllJobs.

  End BasicLemmas.

End Schedulability.