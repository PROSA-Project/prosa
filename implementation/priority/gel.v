Require Import prosa.util.int.
Require Export prosa.model.priority.gel.

(** * GEL Priority Policy *)

(** We introduce the canonical GEL priority policy, under which jobs are
    scheduled in order of their absolute priority points. The GEL policy
    belongs to the class of JLFP policies. *)
#[local] Instance GEL (Job : JobType) `{JobPriorityPoint Job} : JLFP_policy Job :=
{
  hep_job (j1 j2 : Job) := (job_priority_point j1 <= job_priority_point j2)%R
}.

(** In this section, we prove a few properties about the concrete GEL policy. *)
Section PropertiesOfGEL.

  (** Consider any type of jobs with absolute priority points. *)
  Context {Job : JobType} `{JobPriorityPoint Job}.

  (** Under the concrete [GEL] implementation, [hep_job] is exactly
      priority-point order. *)
  Fact GEL_hep_job :
    forall j1 j2,
      @hep_job Job (GEL Job) j1 j2
      = (job_priority_point j1 <= job_priority_point j2)%R.
  Proof. by []. Qed.

  (** GEL is reflexive. *)
  Fact GEL_is_reflexive : reflexive_job_priorities (GEL Job).
  Proof. move=> j; exact: lexx. Qed.

  (** GEL is transitive. *)
  Fact GEL_is_transitive : transitive_job_priorities (GEL Job).
  Proof. move=> x y z; exact: le_trans. Qed.

  (** GEL is total. *)
  Fact GEL_is_total : total_job_priorities (GEL Job).
  Proof. move=> j1 j2; exact: le_total. Qed.

  (** The concrete [GEL] implementation is indeed a GEL policy. *)
  Fact GEL_is_GEL_policy :
    policy_is_GEL (GEL Job).
  Proof.
    repeat split.
    - by move=> j1 j2; rewrite GEL_hep_job.
    - exact: GEL_is_reflexive.
    - exact: GEL_is_transitive.
    - exact: GEL_is_total.
  Qed.

End PropertiesOfGEL.

(** We add the above facts into the [basic_rt_facts] hint database so Coq can
    apply them automatically where needed. *)
Global Hint Resolve
  GEL_is_GEL_policy
  GEL_is_reflexive
  GEL_is_transitive
  GEL_is_total
  : basic_rt_facts.
