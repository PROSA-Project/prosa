Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.basic.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Definition of response-time bound and some simple lemmas. *)
Module ResponseTime.

  Import Schedule SporadicTaskset TaskArrival.
  
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any multiprocessor schedule of these jobs. *)
    Context {num_cpus : nat}.
    Variable sched: schedule Job num_cpus.

    (* For simplicity, let's define some local names.*)
    Let job_has_completed_by := completed job_cost sched.

    Section Definitions.
      
      (* Given a task tsk...*)
      Variable tsk: sporadic_task.

      (* ... we say that R is a response-time bound of tsk in this schedule ... *)
      Variable R: time.

      (* ... iff any job j of tsk in this arrival sequence has completed by (job_arrival j + R). *)
      Definition is_response_time_bound_of_task :=
        forall j,
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_has_completed_by j (job_arrival j + R).

    End Definitions.
    
    Section BasicLemmas.

      (* Assume that jobs dont execute after completion. *)
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      Section SpecificJob.

        (* Then, for any job j ...*)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.

        (* ...with response-time bound R in this schedule, ... *)
        Variable R: time.
        Hypothesis response_time_bound:
          job_has_completed_by j (job_arrival j + R). 

        (* ...the service received by j at any time t' after its response time is 0. *)
        Lemma service_after_job_rt_zero :
          forall t',
            t' >= job_arrival j + R ->
            service_at sched j t' = 0.
        Proof.
          rename response_time_bound into RT,
                 H_completed_jobs_dont_execute into EXEC; ins.
          unfold is_response_time_bound_of_task, completed,
                 completed_jobs_dont_execute in *.
          apply/eqP; rewrite -leqn0.
          eapply completion_monotonic in RT; eauto 2.
          apply completed_implies_not_scheduled in RT; eauto 2.
            by move: RT; rewrite not_scheduled_no_service; move => /eqP RT; rewrite RT.
        Qed.

        (* The same applies for the cumulative service of job j. *)
        Lemma cumulative_service_after_job_rt_zero :
          forall t' t'',
            t' >= job_arrival j + R ->
            \sum_(t' <= t < t'') service_at sched j t = 0.
        Proof.
          ins; apply/eqP; rewrite -leqn0.
          rewrite big_nat_cond; rewrite -> eq_bigr with (F2 := fun i => 0);
            first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
          intro i; rewrite andbT; move => /andP [LE _].
          by rewrite service_after_job_rt_zero;
            [by ins | by apply leq_trans with (n := t')].
        Qed.

      End SpecificJob.

      Section AllJobs.

        (* Consider any task tsk ...*)
        Variable tsk: sporadic_task.

        (* ... for which a response-time bound R is known. *)
        Variable R: time.
        Hypothesis response_time_bound:
          is_response_time_bound_of_task tsk R.

        (* Then, for any job j of this task, ...*)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_task: job_task j = tsk.

        (* ...the service received by job j at any time t' after the response time is 0. *)
        Lemma service_after_task_rt_zero :
          forall t',
            t' >= job_arrival j + R ->
            service_at sched j t' = 0.
        Proof.
          by ins; apply service_after_job_rt_zero with (R := R); [apply response_time_bound |].
        Qed.

        (* The same applies for the cumulative service of job j. *)
        Lemma cumulative_service_after_task_rt_zero :
          forall t' t'',
            t' >= job_arrival j + R ->
            \sum_(t' <= t < t'') service_at sched j t = 0.
        Proof.
          by ins; apply cumulative_service_after_job_rt_zero with (R := R);
            first by apply response_time_bound. 
        Qed.

      End AllJobs.

    End BasicLemmas.

  End ResponseTimeBound.

End ResponseTime.