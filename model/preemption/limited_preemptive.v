Require Export prosa.model.preemption.parameter.

(** * Job Model Parameter for Preemption Points *)

(** Under the limited-preemptive preemption model, jobs can be preempted only
    at a precise set of points during their execution. To allow such fixed,
    progress-dependent preemption points to be specified, we introduce a new
    job parameter [job_preemption_points] that, for each job, yields the set of
    progress values at which the job can be preempted by the scheduler. *)
Class JobPreemptionPoints (Job : JobType) :=
  {
    job_preemption_points : Job -> seq work
  }.

(** * Preemption Model: Limited-Preemptive Jobs *)

(** Based on the above definition of [job_preemption_points], in the following
    we instantiate [job_preemptable] for limited-preemptive jobs and introduce
    requirements that the function [job_preemption_points] should satisfy to be
    coherent with the limited-preemptive preemption model. *)
Section LimitedPreemptions.

  (**  Consider any type of jobs with arrival times and execution costs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Given each job's preemption points, as determined by
      [job_preemption_points], ...*)
  Context `{JobPreemptionPoints Job}.

  (** ...a job [j] is preemptable at a given point of progress [ρ] iff [ρ] is
      one of the preemption points of [j]. *)
  Global Instance limited_preemptions_model : JobPreemptable Job :=
    {
      job_preemptable (j : Job) (ρ : work) := ρ \in job_preemption_points j
    }.

  (** ** Model Validity *)

  (** Next, we introduce some structural properties that a valid sequence of
      preemption points must satisfy. *)
  Section ValidLimitedPreemptiveModel.

    (** Consider any arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.

    (** We require the sequence of preemption points to contain the beginning ... *)
    Definition beginning_of_execution_in_preemption_points :=
      forall j, arrives_in arr_seq j -> 0 \in job_preemption_points j.

    (** ... and the end of execution for any job [j] that arrives in the given
        arrival sequence [arr_seq]. *)
    Definition end_of_execution_in_preemption_points :=
      forall j, arrives_in arr_seq j -> last0 (job_preemption_points j) = job_cost j.

    (** We further require the sequence of preemption points to be a
        non-decreasing sequence. *)
    Definition preemption_points_is_nondecreasing_sequence :=
      forall j, arrives_in arr_seq j -> nondecreasing_sequence (job_preemption_points j).

    (** A job model is considered valid w.r.t. limited-preemptive preemption
        model if it satisfies each of the preceding definitions. *)
    Definition valid_limited_preemptions_job_model :=
      beginning_of_execution_in_preemption_points /\
      end_of_execution_in_preemption_points /\
      preemption_points_is_nondecreasing_sequence.

  End ValidLimitedPreemptiveModel.

End LimitedPreemptions.
