Require Import rt.util.all.
Require Import rt.model.priority.
Require Import rt.model.schedule.global.workload.
Require Import rt.model.schedule.global.basic.schedule.
Require Import rt.model.schedule.apa.interference rt.model.schedule.apa.affinity.
Require Import rt.analysis.apa.workload_bound rt.analysis.apa.interference_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module InterferenceBoundFP.

  Import Schedule WorkloadBound Priority Interference Affinity.
  Export InterferenceBoundGeneric.

    Section Definitions.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    (* Assume that each task has a processor affinity alpha. *)
    Context {num_cpus: nat}.
    Variable alpha: task_affinity sporadic_task num_cpus.

    (* Let tsk be the task to be analyzed ... *)
    Variable tsk: sporadic_task.

    (* ... under subaffinity alpha'. *)
    Variable alpha': affinity num_cpus.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.
      
    (* Assume an FP policy. *)
    Variable higher_eq_priority: FP_policy sporadic_task.

    (* Recall the generic interference bound. *)
    Let total_interference_bound := interference_bound_generic task_cost task_period tsk delta.

    (* Let (hp_task_in alpha') denote the higher-priority tasks that can execute on alpha'. *)
    Let hp_task_in alpha' := higher_priority_task_in alpha higher_eq_priority tsk alpha'.
    
    (* The total interference incurred by tsk is bounded by the sum
       of individual task interferences of tasks in (hp_task_in alpha'). *)
    Definition total_interference_bound_fp :=
      \sum_((tsk_other, R_other) <- R_prev | hp_task_in alpha' tsk_other)
         total_interference_bound (tsk_other, R_other).
      
  End Definitions.

End InterferenceBoundFP.