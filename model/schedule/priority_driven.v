Require Export prosa.model.priority.classes.
Require Export prosa.model.schedule.preemption_time.

(** * Priority-Driven Uniprocessor Schedules *)

(** We now define what it means for a uniprocessor schedule to respect a
    priority in the presence of jobs with non-preemptive segments. The main
    definition is stated for JLDP policies.  For JLFP and FP policies, we
    provide thin wrappers on top of the JLDP definition because JLFP and FP
    policies can be used with this definition through the canonical conversions
    (see [model.priority.coercion]).

    NB: This definition is useful only for uniprocessor models (but not
        necessarily ideal ones). A similar, more general definition could be
        stated for multiprocessor models, but this remains future work at this
        point. *)

Section Priority.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Suppose jobs have an arrival time, a cost, ... *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and consider any processor model, preemption model, and notion of
          readiness. *)
  Context {PState : ProcessorState Job}.
  Context `{JobPreemptable Job}.
  Context {jr : JobReady Job PState}.

  (** Given any job arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.

  (** ...and any schedule of these jobs, *)
  Variable sched : schedule PState.

  (** we say that a priority policy is respected by the schedule iff,
      at every preemption point, the priority of the scheduled job is
      higher than or equal to the priority of any backlogged job.
      We define three separate notions of priority policy compliance
      based on the three types of scheduling policies : [JLDP]... *)
  Definition respects_JLDP_policy_at_preemption_point (policy: JLDP_policy Job) :=
    forall j j_hp t,
      arrives_in arr_seq j ->
      preemption_time arr_seq sched t ->
      backlogged sched j t ->
      scheduled_at sched j_hp t ->
      hep_job_at t j_hp j.

   (** ... [JLFP], and... *)
  Definition respects_JLFP_policy_at_preemption_point (policy: JLFP_policy Job) :=
    respects_JLDP_policy_at_preemption_point policy.

  (** [FP].  *)
  Definition respects_FP_policy_at_preemption_point (policy: FP_policy Task) :=
    respects_JLDP_policy_at_preemption_point (FP_to_JLFP policy).

End Priority.
