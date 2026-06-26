Require Export prosa.model.priority.fifo.

(** * FIFO Priority Policy *)

(** We define a basic FIFO priority policy, under which jobs are prioritized in
    order of their arrival times. The FIFO policy belongs to the class of JLFP
    policies. *)
#[local] Instance FIFO (Job : JobType) `{JobArrival Job} : JLFP_policy Job :=
{
  hep_job (j1 j2 : Job) := job_arrival j1 <= job_arrival j2
}.

(** In this section, we prove a few basic properties of the FIFO policy. *)
Section Properties.

  (**  Consider any type of jobs with arrival times. *)
  Context {Job : JobType} `{JobArrival Job}.

  (** The concrete [FIFO] implementation is indeed a FIFO policy. *)
  Fact FIFO_is_FIFO_policy :
    policy_is_FIFO (FIFO Job).
  Proof. by []. Qed.

  (** FIFO is reflexive. *)
  Fact FIFO_is_reflexive :
    reflexive_job_priorities (FIFO Job).
  Proof. by move=> j; apply: leqnn. Qed.

  (** FIFO is transitive. *)
  Fact FIFO_is_transitive :
    transitive_job_priorities (FIFO Job).
  Proof. by move=> y x z; apply: leq_trans. Qed.

  (** FIFO is total. *)
  Fact FIFO_is_total :
    total_job_priorities (FIFO Job).
  Proof. by move=> j1 j2; apply: leq_total. Qed.

End Properties.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Global Hint Resolve
  FIFO_is_FIFO_policy
  FIFO_is_reflexive
  FIFO_is_transitive
  FIFO_is_total
  : basic_rt_facts.
