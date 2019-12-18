Require Import  prosa.classic.util.all.
Require Import  prosa.classic.model.arrival.basic.task 
                prosa.classic.model.arrival.basic.job prosa.classic.model.priority 
                prosa.classic.model.arrival.basic.task_arrival
                prosa.classic.model.schedule.uni.schedule.
Require Import  prosa.classic.model.policy_tdma.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform_TDMA.

  Import Job  UniprocessorSchedule div.
  Export PolicyTDMA.

  (* In this section, we define properties of the processor platform for TDMA. *)
  Section Properties.
    
    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ..., any uniprocessor... *)
    Variable sched: schedule Job.

    (* ... and any sporadic task set. *)
    Variable ts: {set sporadic_task}.

    (* Consider any TDMA slot assignment... *)
    Variable time_slot: TDMA_slot sporadic_task.

    (* ... and any slot order. *)
    Variable slot_order: TDMA_slot_order sporadic_task.

    (* In order to characterize a TDMA policy, we first define whether a job is executing its TDMA slot at time t. *)
    Let job_in_time_slot (job:Job) (t:instant):= 
        Task_in_time_slot ts slot_order (job_task job) time_slot t. 
     
    (* We say that a TDMA policy is respected by the schedule iff 
       1. when a job is scheduled at time t, then the corresponding task 
          is also in its own time slot... *)
    Definition sched_implies_in_slot j t:=
      (scheduled_at sched j t -> job_in_time_slot j t).

    (* 2. when a job is backlogged at time t,the corresponding task 
          isn't in its own time slot or another previous job of the same task is scheduled *)
    Definition backlogged_implies_not_in_slot_or_other_job_sched j t:=
      (backlogged job_arrival job_cost sched j t -> 
        ~ job_in_time_slot j t \/ 
        (exists j_other, arrives_in arr_seq j_other/\
                         job_arrival j_other < job_arrival j/\
                         job_task j = job_task j_other/\
                         scheduled_at sched j_other t)).

    Definition Respects_TDMA_policy:=
      forall (j:Job) (t:time),
        arrives_in arr_seq j ->
        sched_implies_in_slot j t /\ backlogged_implies_not_in_slot_or_other_job_sched j t.

  End Properties.

End Platform_TDMA.
