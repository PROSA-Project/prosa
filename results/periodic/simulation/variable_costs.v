Require Export prosa.analysis.facts.sustainability.cost.
Require Export prosa.results.periodic.simulation.interval.

(** * Simulation Certificates for Variable Job Costs *)

(** In this module, we combine the simulation theorem in
    [prosa.results.periodic.simulation.interval], which applies when each job
    executes for its task's worst-case execution time (WCET), with the job-cost
    sustainability argument in [prosa.analysis.facts.sustainability.cost] to
    extend the schedulability guarantee obtained via simulation to schedules in
    which job costs are variable (i.e., not fixed to the WCET). *)

(** ** Workload and Supplied Schedules *)

(** Let us begin with the system model. The two schedules share tasks, job
    arrivals, and deadlines, but the execution costs and readiness models
    differ. *)
Section PeriodicSimulationSustainability.

  (** Consider periodic tasks with offsets, WCETs, and relative deadlines, ... *)
  Context {Task : TaskType} `{TaskOffset Task} `{PeriodicModel Task}
          `{TaskCost Task} `{TaskDeadline Task}.

  (** ... and their jobs. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Let [ts] be the task set whose guarantees we want to establish, and let
      [arr_seq] describe its arrivals. The two schedules share this workload. *)
  Variable ts : TaskSet Task.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Jobs arrive periodically starting at their tasks' offsets. *)
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.
  Hypothesis H_valid_offsets : valid_offsets arr_seq ts.
  Hypothesis H_valid_periods : valid_periods ts.
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.

  (** Now consider a reference WCET schedule and a schedule with variable job
      costs on an ideal uniprocessor ... *)
  Variables sched_reference sched_variable : schedule (ideal.processor_state Job).

  (** ... and the corresponding job-cost parameters. *)
  Variables job_cost_reference job_cost_variable : JobCost Job.

  (** For convenience, we name the two cost functions as follows. *)
  Let reference_job_cost := @job_cost _ job_cost_reference.
  Let variable_job_cost := @job_cost _ job_cost_variable.

  (** Each reference job executes for its task's full WCET. *)
  Hypothesis H_fixed_reference_costs :
    forall j,
      arrives_in arr_seq j ->
      reference_job_cost j = task_cost (job_task j).

  (** In the second schedule, job costs may vary freely (up to the WCET). *)
  Hypothesis H_variable_costs_bounded :
    forall j,
      arrives_in arr_seq j ->
      variable_job_cost j <= task_cost (job_task j).

  (** Readiness depends on whether a job has completed, so we supply a readiness
      model using each schedule's execution costs. *)
  Variable job_ready_reference :
    @JobReady Job (ideal.processor_state Job) job_cost_reference _.
  Variable job_ready_variable :
    @JobReady Job (ideal.processor_state Job) job_cost_variable _.

  (** The simulation theorem is specific to basic job readiness. *)
  Hypothesis H_reference_basic_readiness : basic_readiness job_ready_reference.
  Hypothesis H_variable_basic_readiness : basic_readiness job_ready_variable.

  (** Both schedules must be valid under their respective cost and readiness
      models. *)
  Hypothesis H_valid_reference_schedule :
    @valid_schedule_of_arrivals _ _ _ sched_reference job_cost_reference arr_seq.
  Hypothesis H_reference_respects_job_readiness :
    @respects_job_readiness _ _ _ sched_reference job_cost_reference job_ready_reference.
  Hypothesis H_valid_variable_schedule :
    @valid_schedule_of_arrivals _ _ _ sched_variable job_cost_variable arr_seq.
  Hypothesis H_variable_respects_job_readiness :
    @respects_job_readiness _ _ _ sched_variable job_cost_variable job_ready_variable.

  (** Both schedules must be work-conserving, but for different reasons. Work
      conservation in the reference schedule supports the finite simulation
      bound. In the schedule with variable job costs, it supports the service
      comparison that carries the deadline guarantees across. *)
  Hypothesis H_reference_work_conserving :
    @work_conserving _ _ job_cost_reference _ job_ready_reference arr_seq sched_reference.
  Hypothesis H_variable_work_conserving :
    @work_conserving _ _ job_cost_variable _ job_ready_variable arr_seq sched_variable.

  (** For the simulation result to hold, the system must not be overloaded. *)
  Hypothesis H_no_overload : hyperperiod_workload ts <= hyperperiod ts.

  (** ** Deadline Transfer *)

  (** Let both schedules follow the same JLFP order, including tie-breaking. *)
  Variable JLFP : JLFP_policy Job.
  Hypothesis H_reference_respects_policy :
    @respects_JLFP_policy_at_preemption_point _ _ job_cost_reference _
      fully_preemptive_job_model job_ready_reference arr_seq sched_reference JLFP.
  Hypothesis H_variable_respects_policy :
    @respects_JLFP_policy_at_preemption_point _ _ job_cost_variable _
      fully_preemptive_job_model job_ready_variable arr_seq sched_variable JLFP.

  (** The priority order needs to satisfy two properties for the combined
      argument: antisymmetry for cost sustainability and hyperperiod consistency
      for the finite simulation theorem. *)
  Hypothesis H_priority_antisymmetric :
    antisymmetric_job_priorities JLFP arr_seq.
  Hypothesis H_priority_shift_invariant :
    priorities_consistent_across_hyperperiods ts arr_seq JLFP.

  (** The simulation theorem starts from a finite deadline check in the
      reference schedule. *)
  Let reference_deadlines_checked_through :=
    @deadlines_checked_through _ _ _ _ _ job_cost_reference arr_seq sched_reference.

  (** Our conclusion concerns all deadlines in the schedule with variable job
      costs. *)
  Let all_deadlines_met_under_variable_costs :=
    @all_deadlines_of_arrivals_met _ job_cost_variable _ _ arr_seq sched_variable.

  (** With all definitions in place, we can now connect the two
      arguments. The finite-check theorem first establishes that every deadline
      in the WCET reference schedule is met. Basic readiness supplies the
      job-readiness agreement needed by cost sustainability, which then carries
      those guarantees to the schedule with variable job costs. *)
  Theorem jlfp_finite_deadline_check_with_variable_costs :
    reference_deadlines_checked_through (simulation_horizon ts) ->
    all_deadlines_met_under_variable_costs.
  Proof.
    move=> CHECK.
    apply: (all_deadlines_preserved_under_cost_reduction
      _ job_cost_reference _ _ sched_reference) => //.
    - move=> j ARR.
      by rewrite -/reference_job_cost H_fixed_reference_costs.
    - exact: basic_readiness_compatible.
    - by apply: (jlfp_finite_deadline_check ts).
  Qed.

End PeriodicSimulationSustainability.
