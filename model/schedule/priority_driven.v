Require Export prosa.model.priority.classes.
Require Export prosa.model.schedule.preemption_time.

(** * Priority-Driven Schedules *)

(** We now define what it means for a schedule to respect a priority in the
    presence of jobs with non-preemptive segments.  We only specify a
    definition for JLDP policies since JLFP and FP policies can be used with
    this definition through the canonical conversions (see
    model.priority.classes).

    NB: For legacy reasons, the below definition is currently specific to ideal
        uniprocessor schedules. Removal of this limitation is future work. *)

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require prosa.model.processor.ideal.

Section Priority.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Suppose jobs have an arrival time, a cost, ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and consider any preemption model and notion of readiness. *)
  Context `{JobPreemptable Job}.
  Context `{JobReady Job (ideal.processor_state Job)}.

  (** Given any job arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.

  (** ...and an ideal uniprocessor schedule of these jobs, *)
  Variable sched : schedule (ideal.processor_state Job).

  (** we say that a JLDP policy ...*)
  Context `{JLDP_policy Job}.

  (** ...is respected by the schedule iff, at every preemption point, the
     priority of the scheduled job is higher than or equal to the priority of
     any backlogged job. *)
  Definition respects_policy_at_preemption_point :=
    forall j j_hp t,
      arrives_in arr_seq j ->
      preemption_time sched t ->
      backlogged sched j t ->
      scheduled_at sched j_hp t ->
      hep_job_at t j_hp j.

End Priority.

