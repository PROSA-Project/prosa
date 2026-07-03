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

  (** Under the concrete [ELF] implementation, [hep_job] reduces exactly to
      fixed-priority order, and priority-point order for jobs of
      equal-priority tasks. *)
  Fact ELF_hep_job :
    forall j1 j2,
      @hep_job _ (ELF FP) j1 j2
      = (hp_task (job_task j1) (job_task j2)
         || (hep_task (job_task j1) (job_task j2)
             && (job_priority_point j1 <= job_priority_point j2)%R)).
  Proof. by rewrite /hep_job /ELF /GEL. Qed.

  (** By construction, ELF reduces to GEL when the two tasks have equal
      priority under the underlying FP policy. *)
  Fact hep_job_elf_gel :
    forall j j',
      ep_task (job_task j) (job_task j') ->
      (@hep_job _ (ELF FP) j j') = (@hep_job _ (GEL Job Task) j j').
  Proof.
    move=> j j' EP.
    rewrite ELF_hep_job GEL_hep_job.
    have -> : hep_task (job_task j) (job_task j') = true by apply: ep_hep_task.
    have -> : hp_task (job_task j) (job_task j') = false by apply/negbTE/ep_not_hp_task.
    by rewrite andTb orFb.
  Qed.

  (** Assume the underlying task priorities are reflexive, transitive, and total. *)
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** ELF is reflexive. *)
  Fact ELF_is_reflexive : reflexive_job_priorities (ELF FP).
  Proof.
    move=> j; rewrite ELF_hep_job.
    apply/orP; right; apply/andP; split; first exact: H_reflexive_priorities.
    exact: lexx.
  Qed.

  (** ELF is transitive. *)
  Fact ELF_is_transitive : transitive_job_priorities (ELF FP).
  Proof.
    move=> y x z.
    rewrite !ELF_hep_job.
    move=> /orP [HPxy| /andP[HPxy PPxy]] => /orP[HPyz| /andP [HEPyz PPyz]]
      ; apply/orP.
    - by left; exact: hp_trans.
    - by left; exact: hp_hep_trans.
    - by left; exact: hep_hp_trans HPyz.
    - right; apply /andP; split.
      * exact: H_transitive_priorities.
      * exact: le_trans PPxy PPyz.
  Qed.

  (** ELF is total. *)
  Fact ELF_is_total : total_job_priorities (ELF FP).
  Proof.
    move=> x y.
    rewrite !ELF_hep_job.
    rewrite -implyNb; apply/implyP => /norP [NHP /nandP [NHEP|NPP] ].
    { by apply /orP; left; rewrite -not_hep_hp_task. }
    { move: NHP => /nandP [NHEP'| NHEP']; apply/orP.
      - by left; rewrite -not_hep_hp_task.
      - right; move: NHEP' => /negbNE -> /=.
        by move: NPP; lia. }
  Qed.

  (** The concrete [ELF] implementation is indeed an ELF policy. *)
  Fact ELF_is_ELF_policy :
    policy_is_ELF FP (ELF FP).
  Proof.
    repeat split.
    - move=> j1 j2.
      rewrite ELF_hep_job => /orP [HP|/andP [HEP _]] //.
      exact: hp_hep_task.
    - move=> j1 j2 EP.
      rewrite ELF_hep_job.
      have -> : hep_task (job_task j1) (job_task j2) by apply: ep_hep_task.
      have -> : hp_task (job_task j1) (job_task j2) = false
        by apply/negbTE/ep_not_hp_task.
      by rewrite andTb orFb.
    - exact: ELF_is_reflexive.
    - exact: ELF_is_transitive.
    - exact: ELF_is_total.
  Qed.

End PropertiesOfELF.

(** We add the concrete-policy witness to the [basic_rt_facts] hint database so
    Coq can apply it automatically where needed. *)
Global Hint Resolve
  ELF_is_ELF_policy
  ELF_is_reflexive
  ELF_is_transitive
  ELF_is_total
  : basic_rt_facts.
