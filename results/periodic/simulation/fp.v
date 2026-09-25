(** * FP Schedulability by Simulation *)

(** We specialize [jlfp_finite_deadline_check] and [jlfp_taskset_schedulable]
    from [prosa.results.periodic.simulation.interval] to any task-level FP
    policy with ties resolved by task and job IDs.

    The general result formalizes, in discrete time, the simulation bound and
    finite deadline-check argument of Guidolin–Pina et al., “Minimal simulation
    interval for periodic task schedulers”, Journal of Systems Architecture 179
    (2026), 103939.  #<br><a
    href="https://doi.org/10.1016/j.sysarc.2026.103939">DOI:
    10.1016/j.sysarc.2026.103939</a>#

    Under the assumptions below, checking the deadlines of jobs arriving before
    [simulation_horizon] establishes schedulability of the entire periodic task
    set on a fully preemptive ideal uniprocessor. *)

Require Export prosa.results.periodic.simulation.interval.
Require Export prosa.implementation.priority.tiebreaking_fp.

(** Consistent tie-breaking by task and job IDs ensures that job priorities are
    antisymmetric under FP. Additionally, monotonic job IDs ensure consistent
    prioritization across hyperperiods. Together, these two properties allow us
    to apply the general JLFP result. *)
Section FPSimulationInterval.

  (** Consider periodic tasks with offsets, execution costs, relative deadlines,
      and numeric identifiers ... *)
  Context {Task : TaskType} `{TaskOffset Task} `{PeriodicModel Task}
          `{TaskCost Task} `{TaskDeadline Task} `{TaskId Task}.

  (** ... and their jobs, with derived absolute deadlines and numeric
      identifiers. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobCost Job} `{JobId Job}.

  (** The primary task-priority policy can be any FP instance. *)
  Context {FP : FP_policy Task}.

  (** We resolve ties in job priorities by task and job IDs. *)
  #[local] Existing Instance tiebreaking_fp.

  (** Suppose the task set has valid periods ... *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods : valid_periods ts.

  (** ... and unique task IDs, making task-level tie-breaking consistent. *)
  Hypothesis H_valid_task_ids : valid_task_ids ts.

  (** The tasks generate a valid infinite arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.

  (** ... with unambiguous, monotonic job IDs ... *)
  Hypothesis H_valid_job_ids : valid_job_ids arr_seq.
  Hypothesis H_monotonic_job_ids : monotonic_job_ids arr_seq.

  (** ... and periodic arrivals starting at each task's offset. *)
  Hypothesis H_valid_offsets : valid_offsets arr_seq ts.
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.

  (** Simulation uses each task's WCET for all of its jobs. *)
  Hypothesis H_fixed_job_costs :
    forall j,
      arrives_in arr_seq j ->
      job_cost j = task_cost (job_task j).

  (** Assume the system is not permanently overloaded. *)
  Hypothesis H_no_overload : hyperperiod_workload ts <= hyperperiod ts.

  (** We restrict our attention to the basic Liu-and-Layland-style job readiness
      model, where every pending job is always ready to execute, ... *)
  #[local] Existing Instance ideal.processor_state.
  Context {job_ready_model : JobReady Job (ideal.processor_state Job)}.
  Hypothesis H_basic_readiness : basic_readiness job_ready_model.

  (** ... and also assume that jobs are fully preemptive. *)
  #[local] Existing Instance fully_preemptive_job_model.

  (** Consider a valid, work-conserving, ideal uniprocessor schedule ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... that follows the supplied FP policy with identifier-based
      tie-breaking. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched (tiebreaking_fp FP).

  (** Under these assumptions, the generic periodic simulation interval bound
      applies to the supplied FP policy. *)
  Fact tiebreaking_fp_finite_deadline_check :
    deadlines_checked_through arr_seq sched (simulation_horizon ts) ->
    all_deadlines_of_arrivals_met arr_seq sched.
  Proof.
    by apply: (jlfp_finite_deadline_check ts H_valid_periods arr_seq).
  Qed.

  (** Checking all deadlines up to the finite horizon by simulation thus
      establishes schedulability of the entire task set. *)
  Corollary tiebreaking_fp_taskset_schedulable :
    deadlines_checked_through arr_seq sched (simulation_horizon ts) ->
    taskset_schedulable arr_seq sched ts.
  Proof.
    by apply: (jlfp_taskset_schedulable ts H_valid_periods arr_seq).
  Qed.

End FPSimulationInterval.
