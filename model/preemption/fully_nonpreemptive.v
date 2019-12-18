Require Export prosa.model.preemption.parameter.

(** * Preemption Model: Fully Non-Preemptive Jobs *)
(** In this section, we instantiate [job_preemptable] for the fully
    non-preemptive model, wherein no job can be forcefully preempted at any
    time. *)
Section FullyNonPreemptiveModel.

  (** Consider any type of jobs with execution costs. *)
  Context {Job : JobType}.
  Context `{JobCost Job}.

  (** We say that the model is fully non-preemptive iff no job
      can be preempted until its completion. *)
  Global Instance fully_nonpreemptive_model : JobPreemptable Job :=
    {
      job_preemptable (j : Job) (ρ : work) := (ρ == 0) || (ρ == job_cost j)
    }.

End FullyNonPreemptiveModel.
