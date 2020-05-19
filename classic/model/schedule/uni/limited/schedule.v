Require Import prosa.classic.util.all. 
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.schedule.

(* Let's import definition of nonpreemptive schedule. *)
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.


From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we provide additional definitions and 
   lemmas about lock-in-serivce-compliant schedules. *)
  Import Job Service UniprocessorSchedule.

  Section Definitions.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.    

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule. *)
    Variable sched: schedule Job.

    (* We define the notion of lock-in service: lock-in service is the amount of service 
       after which a job cannot be preempted until its completion. *)
    Variable job_lock_in_service: Job -> time.

    (* We require the lock-in service to be positive for any job, i.e., in order to 
       become non-preemptive a job must receive at least one unit of service. *)
    Definition job_lock_in_service_positive :=
      forall j,
        arrives_in arr_seq j ->
        job_cost_positive job_cost j -> 
        0 < job_lock_in_service j.
 
    (* We also require a job's lock-in service to be at most the cost of the job. *)
    Definition job_lock_in_service_le_job_cost :=
      forall j,
        arrives_in arr_seq j ->
        job_cost_positive job_cost j -> 
        job_lock_in_service j <= job_cost j.

    (* In order to get a consistent schedule, the scheduler should respect the notion of 
       lock-in service. We assume that, after a job reaches its lock-in service, it 
       cannot be preempted until its completion. *)
    Definition job_nonpreemptive_after_lock_in_service :=
      forall j t t',
        arrives_in arr_seq j ->
        t <= t' ->
        job_lock_in_service j <= service sched j t ->
        ~~ completed_by job_cost sched j t' ->
        scheduled_at sched j t'.

    (* We say that job_lock_in_service is a proper job lock-in service iff for all jobs in the 
       arrival sequence the lock-in service is (1) positive, (2) no bigger than the costs of
       the corresponding jobs, and (3) a job becomes nonpreemptive after it reaches the
       lock-in service. *)
    Definition proper_job_lock_in_service :=
      job_lock_in_service_positive /\ 
      job_lock_in_service_le_job_cost /\ 
      job_nonpreemptive_after_lock_in_service.
      
    (* Similarly, we define the notion of task lock-in service: task lock-in service is the
       amount of service after which any job from a task reaches its lock-in service. *)
    Variable task_lock_in_service: Task -> time.

    (* A task's lock-in service should be at most the cost of the task. *)
    Definition task_lock_in_service_le_task_cost tsk :=
      task_lock_in_service tsk <= task_cost tsk.
    
    (* We say that the lock-in service of a task tsk bounds the job lock-in service iff for any 
       job j of task tsk the job lock-in service is less-than-or-equal to the task lock-in 
       service. *) 
    Definition task_lock_in_service_bounds_job_lock_in_service tsk :=
      forall j,
        arrives_in arr_seq j ->
        job_task j = tsk ->
        job_lock_in_service j <= task_lock_in_service tsk.

    (* We say that task_lock_in_service is a proper task lock-in service for some task tsk
       iff [task_lock_in_service tsk] is (1) no bigger than tsk's cost, (2) for any job of 
       task tsk job_lock_in_service is bounded by task_lock_in_service. *)
    Definition proper_task_lock_in_service tsk :=
      task_lock_in_service_le_task_cost tsk /\
      task_lock_in_service_bounds_job_lock_in_service tsk.
    
  End Definitions.

  Section Examples.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Consider any arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule. *)
    Variable sched: schedule Job.

    (* Assume that completed jobs do not execute. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* In this section we prove that in case of the fully preemptive scheduling model 
       the job_nonpreemptive_after_lock_in_service hypothesis becomes trivial. *)
    Section FullyPreemptiveModel.

      (* In the fully preemptive model any job can be preempted at any moment. *)
      Let job_lock_in_service (j: Job) := job_cost j.

      (* Then, we prove that the job_nonpreemptive_after_lock_in_service hypothesis is trivial. *)
      Lemma job_nonpreemptive_after_lock_in_service_trivial:
         job_nonpreemptive_after_lock_in_service job_cost arr_seq sched job_lock_in_service .
      Proof.
        intros j ? ? ARR LE SERV NCOMP.
        move: NCOMP => /negP NCOMP; exfalso; apply: NCOMP.
        move: (H_completed_jobs_dont_execute j t) => SERV2.
          by apply completion_monotonic with t.
      Qed.

    End FullyPreemptiveModel. 
 
    (* In this section we prove that in case of the fully nonpreemptive scheduling model 
       the job_nonpreemptive_after_lock_in_service hypothesis holds. *)
    Section FullyNonPreemptiveModel.

      (* In fully nonpreemptive model any job becomes nonpreemptive as soon as it receives one unit of service. *)
      Let job_lock_in_service (j: Job) := ε.

      (* Next, we assume that the schedule is fully nonpreemptive. *) 
      Hypothesis H_is_nonpreemptive_schedule: 
        NonpreemptiveSchedule.is_nonpreemptive_schedule job_cost sched.

      (* Then, we prove that the job_nonpreemptive_after_lock_in_service hypothesis holds. *)
      Lemma property_last_segment_is_nonpreemptive_holds:
        job_nonpreemptive_after_lock_in_service job_cost arr_seq sched job_lock_in_service .
      Proof.
        unfold NonpreemptiveSchedule.is_nonpreemptive_schedule in *. 
        intros j ? ? ARR LE NEQ NCOMPL; unfold job_lock_in_service in *.
        have POS: 0 < job_cost j.
        { rewrite -[0 < _]Bool.negb_involutive -eqn0Ngt; apply/negP; intros ZERO.
          move: ZERO => /eqP ZERO.
          rewrite /completed_by in NCOMPL.
          rewrite ZERO -lt0n in NCOMPL.
          move: (H_completed_jobs_dont_execute j t') => NN.
            by rewrite ZERO leqNgt in NN; move: NN => /negP NN; apply: NN.
        }
        move: NEQ => /sum_seq_gt0P [ts [IN SCHED]].
        rewrite lt0b in SCHED.
        apply H_is_nonpreemptive_schedule with ts; try done.
        apply ltnW, leq_trans with t; last by done.
          by rewrite mem_iota add0n subn0 in IN; move: IN => /andP [_ IN].
      Qed.

    End FullyNonPreemptiveModel.
    
  End Examples.
 
