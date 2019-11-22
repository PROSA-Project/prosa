Require Export rt.restructuring.model.priority.classes.
Require Export rt.restructuring.model.schedule.preemption_time.

(** We now define what it means for a schedule to respect a priority
    in the presence of jobs with non-preemptive segments. *)
(** We only define it for a JLDP policy since the definitions for JLDP
   and JLFP are the same and can be used through the conversions. *)
Section Priority.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.
  Context `{JobReady Job (ideal.processor_state Job)}.

  (** Consider any job arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.
  
  (** ...and any uniprocessor schedule of these jobs. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** We say that a JLDP policy ...*)
  Context `{JLDP_policy Job}.
  
  (** ...is respected by the schedule iff, at every preemption point,
     a scheduled task has higher (or same) priority than (as) any
     backlogged job. *)
  Definition respects_policy_at_preemption_point :=
    forall j j_hp t,
      arrives_in arr_seq j ->
      preemption_time sched t ->
      backlogged sched j t ->
      scheduled_at sched j_hp t ->
      hep_job_at t j_hp j.

End Priority.
