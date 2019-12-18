Require Export prosa.model.priority.classes.

(** * EDF Priority Policy *)

(** We introduce the classic EDF priority policy, under which jobs are
    scheduled in order of their urgency, i.e., jobs are ordered according to
    their absolute deadlines. The EDF policy belongs to the class of JLFP
    policies. *)
Instance EDF (Job : JobType) `{JobDeadline Job} : JLFP_policy Job :=
{
  hep_job (j1 j2 : Job) := job_deadline j1 <= job_deadline j2
}.

(** In this section, we prove a few properties about EDF policy. *)
Section PropertiesOfEDF.

  (**  Consider any type of jobs with deadlines. *)
  Context {Job : JobType}.
  Context `{JobDeadline Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** EDF is reflexive. *)
  Lemma EDF_is_reflexive : reflexive_priorities.
  Proof. by intros t j; unfold hep_job_at, JLFP_to_JLDP, hep_job, EDF. Qed.

  (** EDF is transitive. *)
  Lemma EDF_is_transitive : transitive_priorities.
  Proof. by intros t y x z; apply leq_trans. Qed.

  (** EDF is total. *)
  Lemma EDF_is_total : total_priorities.
  Proof. by move=> t j1 j2; apply leq_total. Qed.

End PropertiesOfEDF.

(** We add the above lemmas into a "Hint Database" basic_facts, so Coq
    will be able to apply them automatically. *)
Hint Resolve
     EDF_is_reflexive
     EDF_is_transitive
     EDF_is_total
  : basic_facts.

