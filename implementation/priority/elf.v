Require Import prosa.util.int.
Require Export prosa.model.priority.elf.
Require Import prosa.implementation.priority.gel.
Require Import prosa.analysis.facts.priority.classes.

(** * ELF Priority Policy *)

(** We introduce the canonical ELF priority policy, under which jobs are
    ordered by the underlying FP policy and ties are broken by absolute priority
    points. The ELF policy belongs to the class of JLFP policies. *)
(** In order to define the policy, we introduce the required context. *)
Section ELF.

  (** Consider any type of tasks with relative priority points ... *)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ... and jobs of these tasks. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task}.

  (** We parameterize the ELF priority policy based on a fixed-priority policy.
      Job [j1] is assigned a higher priority than job [j2] if either the task
      associated with [j1] has a strictly higher priority than the task
      associated with [j2], or if their tasks have equal priorities and [j1]
      has an earlier absolute priority point. *)
  #[local] Instance ELF (fp : FP_policy Task) : JLFP_policy Job :=
  {
    hep_job (j1 j2 : Job) :=
      let gel_hep_job := @hep_job _ (GEL Job Task) in
      hp_task (job_task j1) (job_task j2)
      || (hep_task (job_task j1) (job_task j2)
          && gel_hep_job j1 j2)
  }.

End ELF.

(** In this section, we prove that the concrete ELF policy satisfies the
    corresponding model-level predicate. *)
Section PropertiesOfELF.

  (** Consider any type of tasks with relative priority points ... *)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ... and jobs of these tasks. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task}.

  (** Consider any fixed-priority policy. *)
  Variable FP : FP_policy Task.

  (** The concrete [ELF] implementation is indeed an ELF policy. *)
  Fact ELF_is_ELF_policy :
    policy_is_ELF FP (ELF FP).
  Proof. by []. Qed.

  (** By construction, ELF reduces to GEL when the two tasks have equal
      priority under the underlying FP policy. *)
  Fact hep_job_elf_gel :
    forall j j',
      ep_task (job_task j) (job_task j') ->
      (@hep_job _ (ELF FP) j j') = (@hep_job _ (GEL Job Task) j j').
  Proof.
    move=> j j' EP.
    rewrite /hep_job /ELF /GEL.
    have -> : hep_task (job_task j) (job_task j') = true by apply: ep_hep_task.
    have -> : hp_task (job_task j) (job_task j') = false by apply/negbTE/ep_not_hp_task.
    by rewrite andTb orFb.
  Qed.

End PropertiesOfELF.

(** We add the concrete-policy witness to the [basic_rt_facts] hint database so
    Coq can apply it automatically where needed. *)
Global Hint Resolve
  ELF_is_ELF_policy
  : basic_rt_facts.
