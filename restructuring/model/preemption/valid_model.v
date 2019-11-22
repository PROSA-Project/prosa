Require Export rt.restructuring.model.preemption.job.parameters.
Require Export rt.restructuring.model.task.preemption.parameters.

(** * Platform with limited preemptions *)
(** Since the notion of preemption points is based on an user-provided 
    predicate (variable job_preemptable), it does not guarantee that 
    the scheduler will enforce correct behavior. For that, we must 
    define additional predicates. *)
Section PreemptionModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume the existence of a function mapping a
      task to its maximal non-preemptive segment ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

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

  (** For simplicity, let's define some local names. *)
  Let job_pending := pending sched.
  Let job_completed_by := completed_by sched.
  Let job_scheduled_at := scheduled_at sched.

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
        job_scheduled_at j t. 

    (** A job can start its execution only from a preemption point. *)
    Definition execution_starts_with_preemption_point (j : Job) := 
      forall prt,
        ~~ job_scheduled_at j prt ->
        job_scheduled_at j prt.+1 ->
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

  (** Note that for analysis purposes, it is important that the
      distance between preemption points of a job is bounded. To
      ensure that, next we define the model with bounded nonpreemptive
      segment. *)
  Section ModelWithBoundedNonpreemptiveSegments.

    (** First we require that [task_max_nonpreemptive_segment] gives an
        upper bound for values of the function
        [job_max_nonpreemptive_segment]. *)
    Definition job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (j: Job) :=
      job_max_nonpreemptive_segment j <= task_max_nonpreemptive_segment (job_task j).
    
    (** Next, we require that all the segments of a job [j] have
        bounded length. I.e., for any progress [ρ] of job [j] there
        exists a preemption point [pp] such that [ρ <= pp <= ρ +
        (job_max_nps j - ε)]. That is, in any time interval of length
        [job_max_nps j], there exists a preeemption point which lies
        in this interval. *)
    Definition nonpreemptive_regions_have_bounded_length (j : Job) :=
      forall (ρ : duration),
        0 <= ρ <= job_cost j -> 
        exists (pp : duration),
          ρ <= pp <= ρ + (job_max_nonpreemptive_segment j - ε) /\
          job_preemptable j pp.
    
    (** We say that the schedule enforces bounded nonpreemptive
        segments iff the predicate [job_preemptable] satisfies the two
        conditions above. *)
    Definition model_with_bounded_nonpreemptive_segments :=
      forall j,
        arrives_in arr_seq j ->
        job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment j
        /\ nonpreemptive_regions_have_bounded_length j.

    (** Finally, we say that the schedule enforces _valid_ bounded
        nonpreemptive segments iff the predicate [job_preemptable]
        defines a valid preemption model which has bounded
        non-preemptive segments . *)
    Definition valid_model_with_bounded_nonpreemptive_segments :=
      valid_preemption_model /\
      model_with_bounded_nonpreemptive_segments.
    
  End ModelWithBoundedNonpreemptiveSegments.
    
End PreemptionModel. 