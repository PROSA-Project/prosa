Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.global.jitter.job prosa.classic.model.arrival.basic.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Require prosa.classic.model.schedule.global.basic.schedule.

(* Definition, properties and lemmas about schedules. *)
Module ScheduleWithJitter.

  (* We import the original schedule module and redefine whatever is required. *)
  Export prosa.classic.model.schedule.global.basic.schedule.
  Export ArrivalSequence Schedule.
  
  (* We need to redefine the properties of a job that depend on the arrival time. *)
  Section ArrivalDependentProperties.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any schedule of these jobs. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* In this section we define properties of a job in the schedule. *)
    Section JobProperties.

      (* Let j be any job. *)
      Variable j: Job.

      (* We define the actual arrival of job j as the time when the jitter ends. *)
      Definition actual_arrival := job_arrival j + job_jitter j.

      (* Next, we define whether job j's jitter has passed by time t... *)
      Definition jitter_has_passed (t: time) := actual_arrival <= t.

      (* ...and whether job j actually arrived before time t. *)
      Definition actual_arrival_before (t: time) := actual_arrival < t.

      (* We say that job j is pending at time t iff the jitter has passed but j has not completed. *)
      Definition pending (t: time) := jitter_has_passed t && ~~ completed job_cost sched j t.

      (* We say that job j is backlogged at time t iff it is pending and not scheduled. *)
      Definition backlogged (t: time) := pending t && ~~ scheduled sched j t.

    End JobProperties.

    Section ScheduleProperties.

      (* In a valid schedule, a job can only be scheduled after the jitter has passed. *)
      Definition jobs_execute_after_jitter :=
        forall j t,
          scheduled sched j t -> jitter_has_passed j t.

    End ScheduleProperties.
    
    Section BasicLemmas.

      (* Assume that jobs can only execute after the jitter. *)
      Hypothesis H_jobs_execute_after_jitter:
        jobs_execute_after_jitter.

      Section Pending.
      
        (* Assume that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.

        (* Then, if job j is scheduled, it must be pending. *)
        Lemma scheduled_implies_pending:
          forall j t,
            scheduled sched j t ->
            pending j t.
        Proof.
          rename H_jobs_execute_after_jitter into JITTER,
                 H_completed_jobs into COMP.
          unfold jobs_execute_after_jitter, completed_jobs_dont_execute in *.
          intros j t SCHED.
          unfold pending; apply/andP; split; first by apply JITTER.
          apply/negP; unfold not; intro COMPLETED.
          have BUG := COMP j t.+1.
          rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
          unfold service; rewrite -addn1 big_nat_recr // /=.
          apply leq_add; first by done.
          rewrite lt0n; apply/eqP; red; move => /eqP NOSERV.
          rewrite -not_scheduled_no_service in NOSERV.
          by rewrite SCHED in NOSERV.
        Qed.

      End Pending.

      Section Service.
      
        (* First, we prove that if a job cannot execute before the jitter has passed,
           then it cannot execute before its arrival time. *)
        Lemma arrival_before_jitter :
          jobs_must_arrive_to_execute job_arrival sched.
        Proof.
          unfold jobs_execute_after_jitter, jobs_must_arrive_to_execute.
          intros j t SCHED; unfold ArrivalSequence.has_arrived.
          rewrite -(leq_add2r (job_jitter j)).
          by apply leq_trans with (n := t);
            [by apply H_jobs_execute_after_jitter | by apply leq_addr].
        Qed.

        (* Next, we show that the service received before the jitter is zero. *)
        Lemma service_before_jitter_zero :
          forall j t,
            t < job_arrival j + job_jitter j ->
            service_at sched j t = 0.
        Proof.
          rename H_jobs_execute_after_jitter into AFTER; intros j t LT.
          apply/eqP; rewrite -not_scheduled_no_service; apply/negP; red; intro SCHED.
          by apply AFTER, (leq_trans LT) in SCHED; rewrite ltnn in SCHED.
        Qed.

        (* The same applies to the cumulative service. *)
        Lemma cumulative_service_before_jitter_zero :
          forall j t1 t2,
            t2 <= job_arrival j + job_jitter j ->
            \sum_(t1 <= t < t2) service_at sched j t = 0.
        Proof.
          intros j t1 t2 LE.
          apply/eqP; rewrite -leqn0.
          apply leq_trans with (n := \sum_(t1 <= t < t2) 0);
            last by rewrite big_const_nat iter_addn mul0n addn0.
          rewrite big_nat_cond [\sum_(_ <= _ < _)_]big_nat_cond.
          apply leq_sum; move => t /andP [/andP [_ LT] _].
          rewrite leqn0; apply/eqP; apply service_before_jitter_zero.
          by apply (leq_trans LT).
        Qed.

      End Service.
      
    End BasicLemmas.

  End ArrivalDependentProperties.

End ScheduleWithJitter.

(* Specific properties of a schedule of sporadic jobs. *)
Module ScheduleOfSporadicTaskWithJitter.

  Import SporadicTask Job.
  Export ScheduleWithJitter.

  Section ScheduledJobs.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> sporadic_task.
    
    (* Consider any multiprocessor schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* Given a task tsk, ...*)
    Variable tsk: sporadic_task.

    (* ..., we can state that tsk is scheduled on cpu at time t as follows. *)
    Definition task_scheduled_on (cpu: processor num_cpus) (t: time) :=
      if (sched cpu t) is Some j then
        (job_task j == tsk)
      else false.

    (* Likewise, we can state that tsk is scheduled on some processor. *)
      Definition task_is_scheduled (t: time) :=
        [exists cpu, task_scheduled_on cpu t].
    
    (* We also define the list of jobs scheduled during [t1, t2). *)
    Definition jobs_of_task_scheduled_between (t1 t2: time) :=
      filter (fun j => job_task j == tsk)
             (jobs_scheduled_between sched t1 t2).
    
  End ScheduledJobs.
  
  Section ScheduleProperties.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.    
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* Next we define intra-task parallelism. *)
    Definition jobs_of_same_task_dont_execute_in_parallel :=
      forall j j' t,
        job_task j = job_task j' ->
        scheduled sched j t ->
        scheduled sched j' t ->
        j = j'.
    
  End ScheduleProperties.

  Section BasicLemmas.

    (* Assume the job cost and task are known. *)
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.    
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any schedule of these jobs. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* Assume that jobs do not execute after completion.*)
    Hypothesis jobs_dont_execute_after_completion :
       completed_jobs_dont_execute job_cost sched.

    (* Let tsk be any task...*)
    Variable tsk: sporadic_task.

    (* ...and let j be any valid job of this task. *)
    Variable j: Job.
    Hypothesis H_j_arrives: arrives_in arr_seq j.
    Hypothesis H_job_of_task: job_task j = tsk.
    Hypothesis valid_job:
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    
    (* Then, we can prove that the service received by j is no larger than the cost
       of its task. *)
    Lemma cumulative_service_le_task_cost :
        forall t t',
          service_during sched j t t' <= task_cost tsk.
    Proof.
      rename valid_job into VALID; unfold valid_sporadic_job in *; ins; des.
      apply leq_trans with (n := job_cost j);
        last by rewrite -H_job_of_task; apply VALID0.
      by apply cumulative_service_le_job_cost.
    Qed.

  End BasicLemmas.
  
End ScheduleOfSporadicTaskWithJitter.