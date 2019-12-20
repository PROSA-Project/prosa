Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.facts.preemption.job.preemptive.

(** Furthermore, we assume the fully non-preemptive task model. *)
Require Import prosa.model.task.preemption.fully_preemptive.

(** * Platform for Fully Preemptive Model *)
(** In this section, we prove that instantiation of functions
    [job_preemptable and task_max_nonpreemptive_segment] to the fully
    preemptive model indeed defines a valid preemption model with
    bounded non-preemptive regions. *)
Section FullyPreemptiveModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched : schedule PState.

  (** We prove that [fully_preemptive_model] function
      defines a model with bounded non-preemptive regions.*)
  Lemma fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions:
    model_with_bounded_nonpreemptive_segments arr_seq.
  Proof.
    intros j ARR; split.
    - case: (posnP (job_cost j)) => [ZERO|POS].
      + by rewrite /job_respects_max_nonpreemptive_segment job_max_nps_is_0. 
      + by rewrite /job_respects_max_nonpreemptive_segment job_max_nps_is_ε. 
    - intros t; exists t; split.
      + by apply/andP; split; [ done | rewrite leq_addr]. 
      + by done.
  Qed.

  (** Which together with lemma [valid_fully_preemptive_model] gives
      us the fact that [fully_preemptive_model] defined a valid
      preemption model with bounded non-preemptive regions. *) 
  Corollary fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.
  Proof.
    split.
    apply valid_fully_preemptive_model.
    apply fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions.
  Qed.
    
End FullyPreemptiveModel.

(** We add the above lemma into a "Hint Database" basic_facts, so Coq will be able to apply them automatically. *)
Hint Resolve
     valid_fully_preemptive_model
     fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions
     fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments : basic_facts.
