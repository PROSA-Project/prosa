Require Export prosa.model.priority.edf.
Require Export prosa.model.task.absolute_deadline.
Require Export prosa.analysis.facts.hyperperiod.

(** * EDF Priority Policy *)

(** We introduce the classic EDF priority policy, under which jobs are
    scheduled in order of their urgency, i.e., jobs are ordered according to
    their absolute deadlines. The EDF policy belongs to the class of JLFP
    policies. *)
#[local] Instance EDF (Job : JobType) `{JobDeadline Job} : JLFP_policy Job :=
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

  (** Under the concrete [EDF] implementation, [hep_job] is exactly deadline
      order. *)
  Fact EDF_hep_job :
    forall j1 j2,
      @hep_job Job (EDF Job) j1 j2
      = (job_deadline j1 <= job_deadline j2).
  Proof. by []. Qed.

  (** EDF is reflexive. *)
  Fact EDF_is_reflexive : reflexive_job_priorities (EDF Job).
  Proof. by move=> j; apply:leqnn. Qed.

  (** EDF is transitive. *)
  Fact EDF_is_transitive : transitive_job_priorities (EDF Job).
  Proof. by move=> y x z; apply: leq_trans. Qed.

  (** EDF is total. *)
  Fact EDF_is_total : total_job_priorities (EDF Job).
  Proof. by move=> j1 j2; apply: leq_total. Qed.

  (** The concrete [EDF] implementation is indeed an EDF policy. *)
  Fact EDF_is_EDF_policy :
    policy_is_EDF (EDF Job).
  Proof.
    repeat split.
    - by move=> j1 j2; rewrite EDF_hep_job.
    - exact: EDF_is_reflexive.
    - exact: EDF_is_transitive.
    - exact: EDF_is_total.
  Qed.

End PropertiesOfEDF.

(** EDF's deadline order repeats with a periodic workload. *)
Section EDFHyperperiodPriorities.

  (** Consider periodic tasks with relative deadlines ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{TaskDeadline Task}.

  (** ... and jobs whose absolute deadlines are derived from their tasks. *)
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

  (** Shifting any two given two jobs by one hyperperiod preserves their
      deadline order. *)
  Fact EDF_priorities_consistent_across_hyperperiods :
    priorities_consistent_across_hyperperiods ts arr_seq (EDF Job).
  Proof.
    move=> j1 j2 ARR1 ARR2.
    rewrite !EDF_hep_job /job_deadline /job_deadline_from_task_deadline
      !next_hyperperiod_job_task
      (next_hyperperiod_job_arrival arr_seq _ ts (job_task j1)) //
      (next_hyperperiod_job_arrival arr_seq _ ts (job_task j2)) //.
    by rewrite [job_arrival j1 + _ + _]addnAC
      [job_arrival j2 + _ + _]addnAC leq_add2r.
  Qed.

End EDFHyperperiodPriorities.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Rocq
    will be able to apply them automatically. *)
Global Hint Resolve
     EDF_is_EDF_policy
     EDF_is_reflexive
     EDF_is_transitive
     EDF_is_total
     EDF_priorities_consistent_across_hyperperiods
  : basic_rt_facts.
