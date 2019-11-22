Require Export rt.restructuring.model.preemption.parameter.
Require Export rt.restructuring.model.task.preemption.parameters.

(** Definition of a parameter relating a job
    to the sequence of its preemption points. *)
Class JobPreemptionPoints (Job : JobType) :=
  {
    job_preemption_points : Job -> seq work
  }.

(** * Platform for Models with Limited Preemptions *)
(** In this section, we instantiate [job_preemptable] for the model
    with limited preemptions and introduce a set of requirements for
    function [job_preemption_points], so it is coherent with limited
    preemptions model. *)
Section LimitedPreemptions.

  (**  Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** In addition, assume the existence of a function that
      maps a job to the sequence of its preemption points. *)
  Context `{JobPreemptionPoints Job}.

  (** In the model with limited preemptions a job can be preempted 
      if its progress is equal to one of the preemption points. *)
  Global Instance limited_preemptions_model : JobPreemptable Job :=
    {
      job_preemptable (j : Job) (ρ : work) := ρ \in job_preemption_points j
    }.  
  
  (** Next, we describe some structural properties that
      a sequence of preemption points should satisfy. *)

  (** Consider any arrival sequence. *) 
  Variable arr_seq : arrival_sequence Job.

  (** We require the sequence of preemption points to contain the beginning ... *)
  Definition beginning_of_execution_in_preemption_points :=
    forall j, arrives_in arr_seq j -> 0 \in job_preemption_points j.
  
  (** ... and the end of execution for any job j. *)
  Definition end_of_execution_in_preemption_points :=
    forall j, arrives_in arr_seq j -> last0 (job_preemption_points j) = job_cost j.

  (** We require the sequence of preemption points to be a non-decreasing sequence. *)
  Definition preemption_points_is_nondecreasing_sequence :=
    forall j, arrives_in arr_seq j -> nondecreasing_sequence (job_preemption_points j).

  (** We define a valid job-level model with limited preemptions 
      as a conjunction of the hypotheses above.  *)
  Definition valid_limited_preemptions_job_model :=
    beginning_of_execution_in_preemption_points /\
    end_of_execution_in_preemption_points /\
    preemption_points_is_nondecreasing_sequence.
  
End LimitedPreemptions. 