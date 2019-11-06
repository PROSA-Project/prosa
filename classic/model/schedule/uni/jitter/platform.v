Require Import rt.util.all.
Require Import rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.priority rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.uni.jitter.schedule.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(* In this file, we define properties about the platform in jitter-aware schedules. *)
Module Platform.

  Import Job SporadicTaskset UniprocessorScheduleWithJitter Priority.

  Section Properties.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.    
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Consider any jitter-aware uniprocessor schedule. *)
    Variable arr_seq: arrival_sequence Job.
    Variable sched: schedule Job.

    (* First, we define properties related to execution. *)
    Section Execution.

      (* We say that a scheduler is work-conserving iff whenever a job j
         is backlogged, the processor is always busy with another job.
         (Note that the definition of backlogged depends on the jitter.) *)
      Definition work_conserving :=
        forall j t,
          arrives_in arr_seq j ->          
          backlogged job_arrival job_cost job_jitter sched j t ->
          exists j_other, scheduled_at sched j_other t.

    End Execution.

    (* Next, we define properties related to FP scheduling. *)
    Section FP.

      (* We say that an FP policy...*)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* ...is respected by the schedule iff a scheduled task has
         higher (or same) priority than (as) any backlogged task.
         (Note that the definition of backlogged depends on the jitter.) *)
      Definition respects_FP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->          
          backlogged job_arrival job_cost job_jitter sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority (job_task j_hp) (job_task j).

    End FP.
    
    (* Next, we define properties related to JLFP policies. *)
    Section JLFP.

      (* We say that a JLFP policy ...*)
      Variable higher_eq_priority: JLFP_policy Job.

      (* ... is respected by the scheduler iff a scheduled job has
         higher (or same) priority than (as) any backlogged job.
         (Note that the definition of backlogged depends on the jitter.) *)
      Definition respects_JLFP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->          
          backlogged job_arrival job_cost job_jitter sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority j_hp j.
      
    End JLFP.

    (* Next, we define properties related to JLDP policies. *)
    Section JLDP.

      (* We say that a JLFP/JLDP policy ...*)
      Variable higher_eq_priority: JLDP_policy Job.

      (* ... is respected by the scheduler iff at any time t, a scheduled job
         has higher (or same) priority than (as) any backlogged job.
         (Note that the definition of backlogged depends on the jitter.) *)
      Definition respects_JLDP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost job_jitter sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority t j_hp j.
      
    End JLDP.

  End Properties.

End Platform.