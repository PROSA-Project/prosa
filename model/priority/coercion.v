Require Export prosa.model.priority.definitions.

(** ** Automatic FP ➔ JLFP ➔ JLDP Conversion *)

(** Since there are natural interpretations of FP and JLFP policies as JLFP and
    JLDP policies, respectively, we define conversions that express these
    generalizations. In practice, this means that Coq will be able to
    automatically satisfy a JLDP assumption if a JLFP or FP policy is in
    scope. *)

(** First, any FP policy can be interpreted as an JLFP policy by comparing jobs
    according to the priorities of their respective tasks. *)
#[global]
Instance FP_to_JLFP {Job : JobType} {Task : TaskType} {tasks : JobTask Job Task}
    (FP : FP_policy Task) : JLFP_policy Job :=
  fun j1 j2 => hep_task (job_task j1) (job_task j2).

(** Second, any JLFP policy implies a JLDP policy that simply ignores the time
    parameter. *)
#[global]
Instance JLFP_to_JLDP {Job : JobType}
    (JLFP : JLFP_policy Job) : JLDP_policy Job :=
  fun _ j1 j2 => hep_job j1 j2.

(** We add coercions to enable automatic conversion from [JLFP] to [JLDP]... *)
Coercion JLFP_to_JLDP : JLFP_policy >-> JLDP_policy.
(** ...and from [FP] to [JLFP]. *)
Coercion FP_to_JLFP : FP_policy >-> JLFP_policy.

(** We now prove lemmas about conversions between the properties of these
    priority classes. *)
Section PriorityRelationsConversion.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** We observe that lifting an [FP_policy] to a [JLFP_policy] trivially maintains
      reflexivity,... *)
  Lemma reflexive_priorities_FP_implies_JLFP :
    forall (fp: FP_policy  Task),
      reflexive_task_priorities fp ->
        reflexive_job_priorities (FP_to_JLFP fp).
  Proof. by move=> ? refl_fp ?; apply: refl_fp. Qed.

  (** ...transitivity,... *)
  Lemma transitive_priorities_FP_implies_JLFP :
    forall (fp: FP_policy  Task),
      transitive_task_priorities fp ->
        transitive_job_priorities (FP_to_JLFP fp).
  Proof. by move=> ? tran_jlfp ? ? ?; apply: tran_jlfp. Qed.

  (** ...and totality of priorities. *)
  Lemma total_priorities_FP_implies_JLFP :
    forall (fp: FP_policy  Task),
      total_task_priorities fp ->
        total_job_priorities (FP_to_JLFP fp).
  Proof. by move=> ? tran_fp ? ?; apply: tran_fp. Qed.

  (** Analogously, lifting a [JLFP_policy] to a [JLDP_policy] also maintains
      reflexivity,... *)
  Lemma reflexive_priorities_JLFP_implies_JLDP :
    forall (jlfp: JLFP_policy Job),
      reflexive_job_priorities jlfp ->
        reflexive_priorities (JLFP_to_JLDP jlfp).
  Proof. by move=> ? refl_fp ?; apply: refl_fp. Qed.

  (** ...transitivity,... *)
  Lemma transitive_priorities_JLFP_implies_JLDP :
  forall (jlfp : JLFP_policy Job),
    transitive_job_priorities jlfp ->
      transitive_priorities (JLFP_to_JLDP jlfp).
  Proof. by move=> ? tran_jlfp ? ? ?; apply: tran_jlfp. Qed.

  (** ...and totality of priorities. *)
  Lemma total_priorities_JLFP_implies_JLDP :
    forall (jlfp : JLFP_policy Job),
      total_job_priorities jlfp ->
        total_priorities (JLFP_to_JLDP jlfp).
  Proof. by move=> ? tran_fp ? ?; apply: tran_fp. Qed.

End PriorityRelationsConversion.

(** We add the above lemmas into the "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve
    reflexive_priorities_FP_implies_JLFP
    reflexive_priorities_JLFP_implies_JLDP
    transitive_priorities_FP_implies_JLFP
    transitive_priorities_JLFP_implies_JLDP
    total_priorities_FP_implies_JLFP
    total_priorities_JLFP_implies_JLDP
  : basic_rt_facts.

