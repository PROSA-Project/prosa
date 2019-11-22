Require Export rt.restructuring.model.preemption.parameter.

(** * Platform for Fully Premptive Model *)
(** In this section, we instantiate [job_preemptable] for the fully
   preemptive model. *)
Section FullyPreemptiveModel.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.

  (** In the fully preemptive model any job can be preempted at any time. *)
  Global Program Instance fully_preemptive_model : JobPreemptable Job :=
    {
      job_preemptable (j : Job) (ρ : work) := true
    }.

End FullyPreemptiveModel.