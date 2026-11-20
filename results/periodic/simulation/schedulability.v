Require Export prosa.implementation.facts.ideal_uni.prio_aware.
Require Export prosa.implementation.readiness.basic.
Require Export prosa.results.periodic.simulation.variable_costs.

(** * Schedulability Test for Periodic Tasks *)

(** In this module, we turn the simulation result into a proper schedulability
    test (i.e., an executable procedure) for fully preemptive scheduling on an
    ideal uniprocessor. The caller must supply a task set, a periodic arrival
    sequence, and a scheduling policy. Prosa's reference scheduler builds a
    schedule of the jobs in the given arrival sequence with their tasks' full
    WCETs. The test procedure then checks the deadlines of all jobs arriving up
    to and including the simulation horizon. *)

(** ** Checking Procedure *)

(** We begin by defining the schedulability testing procedure. *)
Section PeriodicChecker.

  (** Consider periodic tasks with offsets, WCETs, and relative deadlines, ... *)
  Context {Task : TaskType} `{TaskOffset Task} `{PeriodicModel Task}
          `{TaskCost Task} `{TaskDeadline Task}.

  (** ... their corresponding jobs, ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** ... and a given JLFP scheduling policy. *)
  Context (policy : JLFP_policy Job).

  (** Let [ts] be the task set to check, with arrivals supplied by [arr_seq]. *)
  Variable ts : TaskSet Task.
  Variable arr_seq : arrival_sequence Job.

  (** For the reference schedule, assume each job executes for its task's full
      WCET. *)
  #[local] Instance wcet_job_cost : JobCost Job :=
    { job_cost j := task_cost (job_task j) }.

  (** We construct a fully preemptive schedule for the basic readiness model, as
      required by the periodic simulation theorem. *)
  #[local] Instance reference_job_ready :
    JobReady Job (ideal.processor_state Job) :=
    basic_ready_instance.
  #[local] Existing Instance fully_preemptive_job_model.

  (** We obtain the WCET schedule from [uni_schedule], Prosa's reference
      uniprocessor scheduler implementation. *)
  Definition periodic_reference_schedule := uni_schedule arr_seq.

  (** We must check every job released through the inclusive arrival cutoff. *)
  Definition check_periodic_deadlines (arrival_cutoff : instant) :=
    all (job_meets_deadline periodic_reference_schedule) (arrivals_up_to arr_seq arrival_cutoff).

  (** The actual checking procedure: first make sure all tasks have valid
      periods and that the processor is not permanently overloaded, and then
      check the deadlines of all jobs arriving up to and including the
      simulation horizon. *)
  Definition periodic_schedulability_check :=
    if all valid_period ts && (hyperperiod_workload ts <= hyperperiod ts)
    then check_periodic_deadlines (simulation_horizon ts)
    else false.

  (** We next note the properties that the checking procedure establishes. *)

  (** If the checker returns [true], then the periods are reasonable, ... *)
  Lemma periodic_check_valid_periods : periodic_schedulability_check -> valid_periods ts.
  Proof.
    rewrite /periodic_schedulability_check; case: ifP => // /andP [/allP PERIOD _] _.
    exact: PERIOD.
  Qed.

  (** ... the workload does not permanently overload the processor, and ... *)
  Lemma periodic_check_no_overload :
    periodic_schedulability_check -> hyperperiod_workload ts <= hyperperiod ts.
  Proof.
    by rewrite /periodic_schedulability_check; case: ifP => // /andP [].
  Qed.

  (** ... all jobs arriving up to and including the simulation horizon meet
      their deadlines. *)
  Lemma periodic_check_reference_certificate :
    periodic_schedulability_check ->
    deadlines_checked_through arr_seq periodic_reference_schedule (simulation_horizon ts).
  Proof.
    by rewrite /periodic_schedulability_check; case: ifP.
  Qed.

End PeriodicChecker.

(** ** Schedulability Guarantee *)

(** With the checker in hand, we now certify the schedulability of a periodic
    workload with variable job costs. *)
Section Schedulability.

  (** Consider periodic tasks and their jobs, as above. *)
  Context {Task : TaskType} `{TaskOffset Task} `{PeriodicModel Task}
          `{TaskCost Task} `{TaskDeadline Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** Let [ts] and [arr_seq] describe the workload to be certified, ... *)
  Variable ts : TaskSet Task.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... under a given total, transitive, and antisymmetric JLFP
      scheduling policy whose relative job priorities are consistent across
      hyperperiods. *)
  Context (policy : JLFP_policy Job).
  Hypothesis H_total_priorities : total_job_priorities policy.
  Hypothesis H_transitive_priorities : transitive_job_priorities policy.
  Hypothesis H_antisymmetric_priorities : antisymmetric_job_priorities policy arr_seq.
  Hypothesis H_priority_shift_invariant :
    priorities_consistent_across_hyperperiods ts arr_seq policy.

  (** Consider the task set's infinite periodic arrival sequence. *)
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.
  Hypothesis H_valid_offsets : valid_offsets arr_seq ts.
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.

  (** Allow jobs to exhibit variable execution costs, up to their WCETs. *)
  Context `{JobCost Job}.
  Hypothesis H_costs_bounded : arrivals_have_valid_job_costs arr_seq.

  (** Consider any given valid, work-conserving, fully preemptive schedule of
      these jobs under a basic readiness model (i.e., without self-suspensions
      or release jitter). *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_valid_schedule_of_arrivals : valid_schedule_of_arrivals sched arr_seq.
  Context {RM : JobReady Job (ideal.processor_state Job)}.
  Hypothesis H_basic_readiness : basic_readiness RM.
  Hypothesis H_respects_job_readiness : respects_job_readiness sched.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  #[local] Existing Instance fully_preemptive_job_model.
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched policy.

  (** Under these assumptions, the extended simulation result for variable job
      costs [jlfp_finite_deadline_check_with_variable_costs] applies if the
      checking procedure returns [true]. *)
  Theorem periodic_schedulability_check_sound :
    periodic_schedulability_check policy ts arr_seq ->
    all_deadlines_of_arrivals_met arr_seq sched.
  Proof.
    move=> CHECK.
    apply: (jlfp_finite_deadline_check_with_variable_costs ts arr_seq _ _ _ _ _ _
      (periodic_reference_schedule policy arr_seq) sched wcet_job_cost _ _ _
      reference_job_ready RM) => //.
    - exact: periodic_check_valid_periods.
    - apply: uni_schedule_valid; exact: basic_readiness_nonclairvoyance.
    - apply: uni_schedule_respects_job_readiness; exact: basic_readiness_nonclairvoyance.
    - apply: uni_schedule_work_conserving => //.
      exact: basic_readiness_nonclairvoyance.
    - exact: periodic_check_no_overload.
    - apply: schedule_respects_policy => //.
      exact: basic_readiness_nonclairvoyance.
    - exact: periodic_check_reference_certificate.
  Qed.

  (** Finally, we obtain the desired schedulability guarantee by restating the
      previous theorem at the level of tasks.  *)
  Corollary periodic_check_taskset_schedulable :
    periodic_schedulability_check policy ts arr_seq ->
    taskset_schedulable arr_seq sched ts.
  Proof.
    move=> CHECK tsk IN j ARR TSK.
    exact: periodic_schedulability_check_sound.
  Qed.

End Schedulability.
