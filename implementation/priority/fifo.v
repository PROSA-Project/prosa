Require Export prosa.model.priority.fifo.
Require Export prosa.analysis.facts.hyperperiod.

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

  (** Under the concrete [FIFO] implementation, [hep_job] is exactly arrival
      order. *)
  Fact FIFO_hep_job :
    forall j1 j2,
      @hep_job Job (FIFO Job) j1 j2 = (job_arrival j1 <= job_arrival j2).
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

  (** The concrete [FIFO] implementation is indeed a FIFO policy. *)
  Fact FIFO_is_FIFO_policy :
    policy_is_FIFO (FIFO Job).
  Proof.
    repeat split.
    - by move=> j1 j2; rewrite FIFO_hep_job.
    - exact: FIFO_is_reflexive.
    - exact: FIFO_is_transitive.
    - exact: FIFO_is_total.
  Qed.

End Properties.

(** FIFO's arrival order repeats with a periodic workload. *)
Section FIFOHyperperiodPriorities.

  (** Consider periodic tasks and their jobs. *)
  Context {Task : TaskType} `{PeriodicModel Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Consider a task set with valid periods ... *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods : valid_periods ts.

  (** ... generating a valid arrival sequence of jobs of these tasks ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... with periodic releases continuing indefinitely. *)
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.

  (** Shifting two jobs by one hyperperiod preserves their arrival order. *)
  Fact FIFO_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq (FIFO Job).
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite !FIFO_hep_job
      (next_hyperperiod_job_arrival arr_seq _ ts (job_task j1)) //
      (next_hyperperiod_job_arrival arr_seq _ ts (job_task j2)) //.
    by rewrite leq_add2r.
  Qed.

End FIFOHyperperiodPriorities.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Rocq
    will be able to apply them automatically. *)
Global Hint Resolve
  FIFO_is_FIFO_policy
  FIFO_is_reflexive
  FIFO_is_transitive
  FIFO_is_total
  FIFO_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
