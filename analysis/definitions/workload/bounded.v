Require Export prosa.model.aggregate.workload.
Require Export prosa.analysis.definitions.busy_interval.classical.

(** * Workload Bound in an Interval Starting with Quiet Time *)
(** In this section, we define the notion of a bound on the total
    workload from higher-or-equal-priority tasks in an interval that
    starts with a quiet time. *)
Section WorkloadBound.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider a JLFP policy that indicates a higher-or-equal-priority
      relation. *)
  Context {JLFP : JLFP_policy Job}.

  (** Consider an arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and a schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** We say that [B : duration -> duration -> work] is a bound on the
      higher-or-equal-priority workload of tasks different from [tsk]
      iff, for any job [j ∈ tsk] and any interval <<[t1, t1 + Δ)>>
      that starts with a quiet time (w.r.t. job [j]), the total
      workload of higher-or-equal-priority tasks distinct from [tsk]
      in the interval <<[t1, t1 + Δ)>> is bounded by
      [B (job_arrival j - t1) Δ]. *)
  Definition athep_workload_is_bounded (B : duration -> duration -> work) :=
    forall (j : Job) (t1 : instant) (Δ : duration),
      job_cost_positive j ->
      job_of_task tsk j ->
      quiet_time arr_seq sched j t1 ->
      workload_of_jobs (another_task_hep_job^~ j) (arrivals_between arr_seq t1 (t1 + Δ))
      <= B (job_arrival j - t1) Δ.

End WorkloadBound.
