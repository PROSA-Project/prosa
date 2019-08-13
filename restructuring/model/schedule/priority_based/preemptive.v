From rt.restructuring.behavior Require Export schedule arrival_sequence.
From rt.restructuring.model Require Export priorities.

(* We now define what it means for a schedule to respect a priority *)
(* We only define it for a JLDP policy since the definitions for JLDP and JLFP are the same
   and can be used through the conversions *)
Section Priority.
  Context {Job: JobType} {Task: TaskType}.
  Context `{JobCost Job} `{JobArrival Job}.

  Context `{JLDP_policy Job}.

  Variable arr_seq : arrival_sequence Job.

  Context {PState : Type}.
  Context `{ProcessorState Job PState}.
  Variable sched : schedule PState.

  Definition respects_preemptive_priorities :=
    forall j j_hp t,
      arrives_in arr_seq j ->
      backlogged sched j t ->
      scheduled_at sched j_hp t ->
      hep_job_at t j_hp j.
End Priority.
