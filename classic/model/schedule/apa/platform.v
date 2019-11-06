Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.priority rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.global.basic.schedule.
Require Import rt.model.schedule.apa.interference rt.model.schedule.apa.affinity.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import Job SporadicTaskset ScheduleOfSporadicTask SporadicTaskset
         TaskArrival Interference Priority Affinity.

  Section Properties.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence ... *)
    Variable arr_seq: arrival_sequence Job.

    (* ... and any schedule of this arrival sequence. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* Assume that every task has a processor affinity alpha. *)
    Variable alpha: task_affinity sporadic_task num_cpus.
    
    Section Execution.

      (* A schedule is work-conserving iff when a job j is backlogged, all
         processors *on which j can be scheduled* are busy with other jobs. *)
      Definition apa_work_conserving :=
        forall j t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          forall cpu,
            can_execute_on alpha (job_task j) cpu ->
            exists j_other,
              scheduled_on sched j_other cpu t.

      (* In a schedule that respects affinities, a job is scheduled
         only if its affinity allows it. *)
      Definition respects_affinity :=
        forall j cpu t,
          scheduled_on sched j cpu t ->
          can_execute_on alpha (job_task j) cpu.

    End Execution.

    Section FP.

      (* An FP policy ...*)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* ... is respected by a weak APA scheduler iff for any
         backlogged job j, if there is another job j_hp
         executing on j's affinity, then j_hp's task priority
         must be as high as j's task priority. *)
      Definition respects_FP_policy_under_weak_APA :=
        forall j j_hp cpu t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_on sched j_hp cpu t ->
          can_execute_on alpha (job_task j) cpu ->
          higher_eq_priority (job_task j_hp) (job_task j).

    End FP.

    Section JLFP.

      (* A JLFP policy ...*)
      Variable higher_eq_priority: JLFP_policy Job.

      (* ... is respected by a weak APA scheduler iff for
         any backlogged job j, if there is another job j_hp
         executing on j's affinity, then j_hp's priority
         must be as high as j's priority. *)
      Definition respects_JLFP_policy_under_weak_APA :=
        forall j j_hp cpu t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_on sched j_hp cpu t ->
          can_execute_on alpha (job_task j) cpu ->
          higher_eq_priority j_hp j.
      
    End JLFP.

    Section JLDP.

      (* A JLFP/JLDP policy ...*)
      Variable higher_eq_priority: JLDP_policy Job.

      (* ... is respected by a weak APA scheduler iff at any time t,
         for any backlogged job j, if there is another job j_hp
         executing on j's affinity, then j_hp's priority must be
         as high as j's priority. *)
      Definition respects_JLDP_policy_under_weak_APA :=
        forall j j_hp cpu t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_on sched j_hp cpu t ->
          can_execute_on alpha (job_task j) cpu ->
          higher_eq_priority t j_hp j.
      
    End JLDP.
    
  End Properties.
  
End Platform.