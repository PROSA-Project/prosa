Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.abstract.IBF.task.
Require Export prosa.analysis.abstract.abstract_rta.

(** * Abstract Response-Time Analysis with Sequential Tasks *)
(** In this file, we propose a general framework for response-time analysis
    (RTA) of uni-processor scheduling of real-time tasks with arbitrary arrival
    models and sequential tasks, valid for any processor state satisfying the
    uniprocessor and unit-service assumptions. *)

(** We prove that the maximum among the solutions of the response-time bound
    inequalities is a response-time bound for [tsk]. Note that in this section we
    _do_ rely on the hypothesis about task sequentiality. This allows us to
    provide a more precise response-time bound, since jobs of the same task will
    be executed strictly in the order they arrive.

    Unlike [uniprocessor_response_time_bound_seq] in
    [analysis.abstract.ideal.abstract_seq_rta], this theorem does _not_ assume
    an ideal processor. The non-preemptive interference bound [IBF_NP] is
    therefore kept as an explicit parameter. *)
Section AbstractRTASequential.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any kind of uniprocessor state model with unit service. Note that
      unlike the ideal version of this theorem, we do _not_ require
      [ideal_progress_proc_model]. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any schedule of this arrival sequence... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Consider an arbitrary task set. *)
  Variable ts : seq Task.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model ... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ... and a valid task run-to-completion threshold function.
      That is, [task_rtct tsk] is (1) no bigger than [tsk]'s cost and
      (2) for any job [j] of task [tsk] [job_rtct j] is bounded by
      [task_rtct tsk]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e.,
      for any task [tsk] in [ts], [max_arrivals tsk] is (1) an arrival
      bound of [tsk] and (2) a monotonic function that equals [0] for
      the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** We assume that the schedule is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Unlike [uniprocessor_response_time_bound], we assume that (1) tasks are
      sequential and (2) the interference and interfering workload functions are
      consistent with the sequential-tasks hypothesis. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.
  Hypothesis H_interference_and_workload_consistent_with_sequential_tasks :
    interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk.

  (** Assume we have a constant [L] that bounds the busy interval of any of
      [tsk]'s jobs. *)
  Variable L : duration.
  Hypothesis H_busy_interval_exists :
    busy_intervals_are_bounded_by arr_seq sched tsk L.

  (** Let us abbreviate task [tsk]'s RBF for clarity. *)
  Let task_rbf := task_request_bound_function tsk.

  (** Next, we assume that [task_IBF] is a bound on the
      _non-self_ interference incurred by jobs of task [tsk] (i.e.,
      interference due to sources other than other jobs of [tsk]). *)
  Variable task_IBF : duration -> duration -> duration.
  Hypothesis H_task_interference_is_bounded :
    task_interference_is_bounded_by arr_seq sched tsk task_IBF.

  (** We define the first-phase IBF [IBF_P] as the sum of the self-interference
      bound [task_rbf (A + ε) - task_cost tsk] and the non-self interference
      bound [task_IBF A Δ]. Note that the self-interference term is computed via
      the task's request-bound function, following the standard sequential-tasks
      argument. *)
  Let IBF_P A Δ := (task_rbf (A + ε) - task_cost tsk) + task_IBF A Δ.

  (** Next, we assume that [IBF_NP] is a bound on interference incurred by a job
      of task [tsk] during the non-preemptive execution stage. The parameter
      semantics for [IBF_NP] is [relative_time_to_reach_rtct]: [IBF_NP F Δ]
      bounds interference in an interval of length [Δ] _given_ that the job
      reaches its run-to-completion threshold by time [t1 + F].

      Unlike in [analysis.abstract.ideal.abstract_seq_rta], [IBF_NP] is _not_
      derived from the processor model here; it is kept as an explicit parameter
      to support non-ideal processor models. *)
  Variable IBF_NP : duration -> duration -> duration.
  Hypothesis H_job_interference_is_bounded_IBFNP :
    job_interference_is_bounded_by arr_seq sched tsk IBF_NP
      (relative_time_to_reach_rtct sched tsk IBF_P).

  (** We also assume that [IBF_NP] respects its own parameter, i.e., [task_cost
      tsk + IBF_NP F Δ >= F] for all [F] and [Δ]. Intuitively, this ensures the
      second-phase bound is at least as large as the first-phase solution. *)
  Hypothesis H_IBF_NP_ge_param : forall F Δ, F <= task_cost tsk + IBF_NP F Δ.

  (** For clarity, define the search space in terms of [IBF_P]. *)
  Let is_in_search_space_seq A := is_in_search_space L IBF_P A.

  (** Consider any value [R] that upper-bounds the solutions of the
      two-inequality response-time recurrence.  That is, for any
      relative arrival time [A] from the search space there exists a
      solution [F] such that
      (1) [task_rtct tsk + (task_rbf (A + ε) - task_cost tsk) + task_IBF A Δ A F <= F], and
      (2) [task_cost tsk + IBF_NP F (A + R) <= A + R]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum_seq :
    forall A,
      is_in_search_space_seq A ->
      exists F,
        task_rtct tsk + IBF_P A F <= F
        /\ task_cost tsk + IBF_NP F (A + R) <= A + R.

  (** Using [task_IBF_implies_job_IBF], we lift the task-level bound [task_IBF]
      to the job level, obtaining a valid [IBF_P]. We then apply
      [uniprocessor_response_time_bound] to conclude that [R] is a response-time
      bound for [tsk]. *)
  Theorem uniprocessor_response_time_bound_seq :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => j ARR TSK.
    eapply uniprocessor_response_time_bound => //.
    exact: task_IBF_implies_job_IBF.
  Qed.

End AbstractRTASequential.
