Require Import prosa.util.int.
Require Export prosa.model.priority.gel.
Require Export prosa.analysis.facts.hyperperiod.

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

(** GEL's priority-point order repeats with a periodic workload. *)
Section GELHyperperiodPriorities.

  (** Consider periodic tasks with relative priority points ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{PriorityPoint Task}.

  (** ... and jobs whose absolute priority points are derived from their tasks. *)
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

  (** Shifting two jobs by one hyperperiod preserves their priority-point order. *)
  Fact GEL_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq (GEL Job).
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite !GEL_hep_job /job_priority_point /jpp_from_tpp
      !next_hyperperiod_job_task
      (next_hyperperiod_job_arrival arr_seq _ ts (job_task j1)) //
      (next_hyperperiod_job_arrival arr_seq _ ts (job_task j2)) //.
    by rewrite !natrD [((job_arrival j1)%:R + _ + _)%R]addrAC
      [((job_arrival j2)%:R + _ + _)%R]addrAC lerD2r.
  Qed.

End GELHyperperiodPriorities.

(** We add the above facts into the [basic_rt_facts] hint database so Rocq can
    apply them automatically where needed. *)
Global Hint Resolve
  GEL_is_GEL_policy
  GEL_is_reflexive
  GEL_is_transitive
  GEL_is_total
  GEL_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
