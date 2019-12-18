Require Export prosa.util.all.
Require Export prosa.behavior.all.

(** * Job-Level Preemption Model *)
(** There are many equivalent ways to represent at which points in time a job
    is preemptable, i.e., where it can be forced to relinquish the processor on
    which it is executing. In Prosa, the various preemption models are
    represented with a single predicate [job_preemptable] that indicates, for
    given a job and a given degree of progress, whether the job is preemptable
    at its current point of execution. *)
Class JobPreemptable (Job : JobType) :=
  job_preemptable : Job -> work -> bool.

(** * Maximum and Last Non-preemptive Segment of a Job *)
(** In the following section we define the notions of the maximal and the last
    non-preemptive segments. *)
Section MaxAndLastNonpreemptiveSegment.

  (**  Consider any type of jobs with arrival times and execution costs... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and consider any given preemption model. *)
  Context `{JobPreemptable Job}.

  (** It is useful to define a representation of the preemption points of a job
      as an actual sequence of points where this job can be preempted. To this
      end, we define [job_preemption_points j] as the sequence of all progress
      values at which job [j] is preemptable, according to
      [job_preemptable]. *)
  Definition job_preemption_points (j : Job) : seq work :=
    [seq ρ : work <- range 0 (job_cost j) | job_preemptable j ρ].

  (** We observe that the conversion indeed is an equivalent way of
      representing the set of preemption points. *)
  Remark conversion_preserves_equivalence:
    forall (j : Job) (ρ : work),
      ρ <= job_cost j ->
      job_preemptable j ρ <-> ρ \in job_preemption_points j.
  Proof.
    intros ? ? LE.
    case: (posnP (job_cost j)) => [ZERO|POS].
    { unfold job_preemption_points.
      split; intros PP.
      - move: LE; rewrite ZERO leqn0; move => /eqP EQ; subst.
        by simpl; rewrite PP.
      - rewrite ZERO in PP; simpl in PP.
        destruct (job_preemptable j 0) eqn:EQ; last by done.
        by move: PP => /orP [/eqP A1| FF]; subst.
    }
    have F: job_cost j == 0 = false.
    { by apply/eqP/neqP; rewrite -lt0n. }
    split; intros PP.
    all: unfold job_preemption_points in *.
    - rewrite mem_filter; apply/andP; split; first by done.
      by rewrite mem_iota subn0 add0n //; apply/andP; split.
    - by move: PP; rewrite mem_filter; move => /andP [PP _].
  Qed.

  (** We further define a function that, for a given job, yields the sequence
      of lengths of its nonpreemptive segments. *)
  Definition lengths_of_segments (j : Job) := distances (job_preemption_points j).

  (** Next, we define a function that determines the length of a job's longest
      nonpreemptive segment (or zero if the job is fully preemptive). *)
  Definition job_max_nonpreemptive_segment (j : Job) := max0 (lengths_of_segments j).

  (** Similarly, we define a function that yields the length of a job's last
      nonpreemptive segment (or zero if the job is fully preemptive). *)
  Definition job_last_nonpreemptive_segment (j : Job) := last0 (lengths_of_segments j).

  (** * Run-to-Completion Threshold of a Job *)

  (** Finally, we define the notion of a job's run-to-completion threshold: the
      run-to-completion threshold is the amount of service after which a job
      cannot be preempted until its completion. *)
  Definition job_run_to_completion_threshold (j : Job) :=
    job_cost j - (job_last_nonpreemptive_segment j - ε).

End MaxAndLastNonpreemptiveSegment.


(** * Model Validity  *)
(** In the following, we define properties that any reasonable job preemption
    model must satisfy. *)
Section PreemptionModel.

  (**  Consider any type of jobs with arrival times and execution costs... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... and any preemption model. *)
  Context `{JobPreemptable Job}.

  (** Consider any kind of processor model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched : schedule PState.

  (** In the following, we define the notion of a valid preemption model.  To
      begin with, we require that a job has to be executed at least one time
      instant in order to reach a nonpreemptive segment. In other words, a job
      must start execution to become non-preemptive. *)
  Definition job_cannot_become_nonpreemptive_before_execution (j : Job) :=
    job_preemptable j 0.

  (** And vice versa, a job cannot remain non-preemptive after its completion. *)
  Definition job_cannot_be_nonpreemptive_after_completion (j : Job) :=
    job_preemptable j (job_cost j).

  (** Next, if a job [j] is not preemptable at some time instant [t], then [j]
      must be scheduled at time [t]. *)
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
       all assumptions given above are satisfied for any job. *)
  Definition valid_preemption_model :=
    forall j,
      arrives_in arr_seq j ->
      job_cannot_become_nonpreemptive_before_execution j
      /\ job_cannot_be_nonpreemptive_after_completion j
      /\ not_preemptive_implies_scheduled j
      /\ execution_starts_with_preemption_point j.

End PreemptionModel.
