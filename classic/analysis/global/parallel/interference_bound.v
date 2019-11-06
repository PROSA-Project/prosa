Require Import rt.util.all.
Require Import rt.model.schedule.global.basic.schedule.
Require Import rt.analysis.global.parallel.workload_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module InterferenceBoundGeneric.

  Section Definitions.

    Import Schedule WorkloadBound.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section PerTask.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.
    
      (* Based on the workload bound, Bertogna and Cirinei define the
         following interference bound for a task. *)
      Definition interference_bound_generic :=
        W task_cost task_period tsk_other R_other delta.

    End PerTask.

  End Definitions.

End InterferenceBoundGeneric.