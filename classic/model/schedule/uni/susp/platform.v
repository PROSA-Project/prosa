Require Import rt.util.all.
Require Import rt.model.arrival.basic.arrival_sequence rt.model.suspension
               rt.model.priority.
Require Import rt.model.schedule.uni.susp.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module PlatformWithSuspensions.

  Export ScheduleWithSuspensions Priority.

  Section Definitions.
    
    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Assume that job suspension times are given. *)
    Variable next_suspension: job_suspension Job.

    (* Consider any job arrival sequence ...*)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* For simplicity, let's recall the definitions of pending, scheduled, and backlogged job.
       Note that this notion of backlogged is specific for suspension-aware schedulers. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_backlogged_at := backlogged job_arrival job_cost next_suspension sched.
    
    (* In this section, we define schedule constraints for suspension-aware schedules. *)
    Section ScheduleConstraints.

      (* First, we consider constraints related to execution. *)
      Section Execution.

        (* We say that a scheduler is work-conserving iff whenever a job j
           is backlogged, the processor is always busy with another job. *)
        Definition work_conserving :=
          forall j t,
            arrives_in arr_seq j ->
            job_backlogged_at j t ->
            exists j_other, job_scheduled_at j_other t.

      End Execution.

      (* Next, we consider constraints related to FP policies. *)
      Section FP.

        (* We say that an FP policy...*)
        Variable higher_eq_priority: FP_policy Task.

        (* ... is respected by the scheduler iff at any time t, a scheduled job
           has higher (or same) priority than (as) any backlogged job. *)
        Definition respects_FP_policy :=
          forall j j_hp t,
            arrives_in arr_seq j ->
            job_backlogged_at j t ->
            job_scheduled_at j_hp t ->
            higher_eq_priority (job_task j_hp) (job_task j).
      
      End FP.

      (* Next, we consider constraints related to JLFP policies. *)
      Section JLFP.

        (* We say that a JLFP policy ...*)
        Variable higher_eq_priority: JLFP_policy Job.

        (* ... is respected by the scheduler iff every scheduled job
           has higher (or same) priority than (as) any backlogged job. *)
        Definition respects_JLFP_policy :=
          forall j j_hp t,
            arrives_in arr_seq j ->
            job_backlogged_at j t ->
            job_scheduled_at j_hp t ->
            higher_eq_priority j_hp j.
      
      End JLFP.

      (* Next, we consider constraints related to JLDP policies. *)
      Section JLDP.

        (* We say that a JLDP policy ...*)
        Variable higher_eq_priority: JLDP_policy Job.

        (* ... is respected by the scheduler iff at any time t, a scheduled job
           has higher (or same) priority than (as) any backlogged job. *)
        Definition respects_JLDP_policy :=
          forall j j_hp t,
            arrives_in arr_seq j ->
            job_backlogged_at j t ->
            job_scheduled_at j_hp t ->
            higher_eq_priority t j_hp j.
      
      End JLDP.

    End ScheduleConstraints.

  End Definitions.
  
End PlatformWithSuspensions.