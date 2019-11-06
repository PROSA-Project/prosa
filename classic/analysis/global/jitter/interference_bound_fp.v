Require Import rt.util.all.
Require Import rt.model.priority.
Require Import rt.model.schedule.global.workload.
Require Import rt.model.schedule.global.jitter.schedule rt.model.schedule.global.jitter.interference.
Require Import rt.analysis.global.jitter.workload_bound rt.analysis.global.jitter.interference_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module InterferenceBoundFP.

  Import ScheduleWithJitter WorkloadBoundJitter Priority Interference.
  Export InterferenceBoundJitter.

    Section Definitions.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    Variable task_jitter: sporadic_task -> time.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.
      
    (* Assume an FP policy. *)
    Variable higher_eq_priority: FP_policy sporadic_task.

    (* Recall the interference bound. *)
    Let total_interference_bound := interference_bound_generic task_cost task_period task_jitter tsk delta.
    
    (* The total interference incurred by tsk is bounded by the sum
       of individual task interferences. *)
    Definition total_interference_bound_fp :=
      \sum_((tsk_other, R_other) <- R_prev)
         total_interference_bound (tsk_other, R_other).
      
  End Definitions.

End InterferenceBoundFP.