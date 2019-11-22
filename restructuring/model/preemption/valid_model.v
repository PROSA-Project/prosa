Require Export rt.restructuring.model.preemption.job.parameters.

(** * Platform with limited preemptions *)
(** In the follwoing, we define properties that any reasonable job preemption
    model must satisfy. *)
Section PreemptionModel.

  (**  Consider any type of jobs... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and the existence of a predicate mapping a job and
      its progress to a boolean value saying whether this job is
      preemptable at its current point of execution. *)
  Context `{JobPreemptable Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched : schedule PState.

  (** In this section, we define the notion of a valid preemption model. *)
  Section ValidPreemptionModel.

    (** We require that a job has to be executed at least one time
        instant in order to reach a nonpreemptive segment. In other
        words, a job must start execution to become non-preemptive. *)
    Definition job_cannot_become_nonpreemptive_before_execution (j : Job) :=
      job_preemptable j 0.

    (** And vice versa, a job cannot remain non-preemptive after its completion. *)
    Definition job_cannot_be_nonpreemptive_after_completion (j : Job) :=
      job_preemptable j (job_cost j).

    (** Next, if a job j is not preemptive at some time instant t,
        then j must be scheduled at time t. *)
    Definition not_preemptive_implies_scheduled (j : Job) :=
      forall t,
        ~~ job_preemptable j (service sched j t) ->
        scheduled_at sched j t.

    (** A job can start its execution only from a preemption point. *)
    Definition execution_starts_with_preemption_point (j : Job) :=
      forall prt,
        ~~ scheduled_at sched j prt ->
        scheduled_at sched j prt.+1 ->
        job_preemptable j (service sched j prt.+1).

    (** We say that a preemption model is a valid preemption model if
       all the assumptions given above are satisfied for any job. *)
    Definition valid_preemption_model :=
      forall j,
        arrives_in arr_seq j ->
        job_cannot_become_nonpreemptive_before_execution j
        /\ job_cannot_be_nonpreemptive_after_completion j
        /\ not_preemptive_implies_scheduled j
        /\ execution_starts_with_preemption_point j.

  End ValidPreemptionModel.

End PreemptionModel.
