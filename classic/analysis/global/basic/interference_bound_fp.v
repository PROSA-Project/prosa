Require Import rt.util.all.
Require Import rt.model.priority.
Require Import rt.model.schedule.global.workload.
Require Import rt.model.schedule.global.basic.schedule rt.model.schedule.global.basic.interference.
Require Import rt.analysis.global.basic.workload_bound
               rt.analysis.global.basic.interference_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module InterferenceBoundFP.

  Import Schedule WorkloadBound Priority Interference.
  Export InterferenceBoundGeneric.

    Section Definitions.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each higher-priority task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... in any interval of length delta. *)
    Variable delta: time.
      
    (* Assume an FP policy. *)
    Variable higher_eq_priority: FP_policy sporadic_task.

    (* Recall the generic interference bound. *)
    Let total_interference_bound := interference_bound_generic task_cost task_period tsk delta.
    
    (* The total interference incurred by tsk is bounded by the sum
       of individual task interferences. *)
    Definition total_interference_bound_fp :=
      \sum_((tsk_other, R_other) <- R_prev)
         total_interference_bound (tsk_other, R_other).
      
  End Definitions.

End InterferenceBoundFP.