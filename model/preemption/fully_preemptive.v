Require Export prosa.model.preemption.parameter.

(** * Preemption Model: Fully Preemptive Jobs *)
(** In this section, we instantiate [job_preemptable] for the fully preemptive
    model, wherein any job may be preempted at any time. This matches the
    classic Liu & Layland model. *)
Section FullyPreemptiveModel.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.

  (** In the fully preemptive model, any job can be preempted at any time. *)
  Global Program Instance fully_preemptive_model : JobPreemptable Job :=
    {
      job_preemptable (_ : Job) (_ : work) := true
    }.

End FullyPreemptiveModel.
