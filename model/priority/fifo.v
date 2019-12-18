Require Export prosa.model.priority.classes.

(** * FIFO Priority Policy *)

(** We define the basic FIFO priority policy, under which jobs are prioritized
    in order of their arrival times. The FIFO policy belongs to the class of
    JLFP policies. *)
Instance FIFO (Job : JobType) `{JobArrival Job} : JLFP_policy Job :=
{
  hep_job (j1 j2 : Job) := job_arrival j1 <= job_arrival j2
}.

(** In this section, we prove a few basic properties of the FIFO policy. *)
Section Properties.

  (**  Consider any type of jobs with arrival times. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.

  (** FIFO is reflexive. *)
  Lemma FIFO_is_reflexive : reflexive_priorities.
  Proof.  by intros t j; unfold hep_job_at, JLFP_to_JLDP, hep_job, FIFO. Qed.

  (** FIFO is transitive. *)
  Lemma FIFO_is_transitive : transitive_priorities.
  Proof. by intros t y x z; apply leq_trans. Qed.

  (** FIFO is total. *)
  Lemma FIFO_is_total : total_priorities.
  Proof. by move=> t j1 j2; apply leq_total. Qed.

End Properties.

(** We add the above lemmas into a "Hint Database" basic_facts, so Coq
    will be able to apply them automatically. *)
Hint Resolve
     FIFO_is_reflexive
     FIFO_is_transitive
     FIFO_is_total
  : basic_facts.

