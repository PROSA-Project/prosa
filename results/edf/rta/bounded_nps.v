Require Export prosa.util.tactics.
Require Import prosa.model.readiness.basic.
Require Export prosa.analysis.facts.busy_interval.pi_bound.
Require Export prosa.analysis.facts.busy_interval.arrival.
Require Export prosa.results.edf.rta.bounded_pi.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.analysis.definitions.busy_interval.classical.
Require Export prosa.analysis.facts.blocking_bound.edf.
Require Export prosa.analysis.facts.workload.edf_athep_bound.

(** * RTA for EDF  with Bounded Non-Preemptive Segments *)

(** In this section we instantiate the Abstract RTA for EDF-schedulers
    with Bounded Priority Inversion to EDF-schedulers for ideal
    uni-processor model of real-time tasks with arbitrary
    arrival models _and_ bounded non-preemptive segments. *)

(** Recall that Abstract RTA for EDF-schedulers with Bounded Priority
    Inversion does not specify the cause of priority inversion. In
    this section, we prove that the priority inversion caused by
    execution of non-preemptive segments is bounded. Thus the Abstract
    RTA for EDF-schedulers is applicable to this instantiation. *)
Section RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskRunToCompletionThreshold Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For clarity, let's denote the relative deadline of a task as [D]. *)
  Let D tsk := task_deadline tsk.

  (** Consider the EDF policy that indicates a higher-or-equal priority relation.
     Note that we do not relate the EDF policy with the scheduler. However, we
     define functions for Interference and Interfering Workload that actively use
     the concept of priorities. *)
  Let EDF := EDF Job.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any valid ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and the schedule respects the scheduling policy at every preemption point. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched EDF.

  (** Consider an arbitrary task set ts, ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and the cost of a job cannot be larger than the task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
     any task [tsk] in ts [max_arrival tsk] is (1) an arrival bound of
     [tsk], and (2) it is a monotonic function that equals 0 for the
     empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
     is, [task_rtct tsk] is (1) no bigger than [tsk]'s cost, (2) for
     any job of task [tsk] [job_rtct] is bounded by [task_rtct]. *)
  Hypothesis H_valid_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** We introduce as an abbreviation [rbf] for the task request bound function,
     which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a task T. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce [task_rbf] as an abbreviation for the task
     request bound function of task [tsk]. *)
  Let task_rbf := rbf tsk.

  (** Using the sum of individual request bound functions, we define the request bound
     function of all tasks (total request bound function). *)
  Let total_rbf := total_request_bound_function ts.

  (** Let's define some local names for clarity. *)
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.

  (** ** Search Space *)

  (** If priority inversion is caused exclusively by non-preemptive sections,
      then we do not need to consider the priority-inversion bound in the search
      space. Hence we define the following search space, which refines the more
      general [bounded_pi.is_in_search_space] for our specific setting. *)
  Definition is_in_search_space (L A : duration) :=
    (A < L) && (task_rbf_changes_at tsk A
                || bound_on_total_hep_workload_changes_at ts tsk A).

  (** For the following proof, we exploit the fact that the blocking bound is
      monotonically decreasing in [A], which we note here. *)
  Fact blocking_bound_decreasing :
    forall A1 A2,
      A1 <= A2 ->
      blocking_bound ts tsk A1 >= blocking_bound ts tsk A2.
  Proof.
    move=> A1 A2 LEQ.
    rewrite /blocking_bound.
    apply: bigmax_subset => tsk_o IN /andP[/andP[OTHER LT] ARR].
    by repeat (apply /andP; split) => //; lia.
  Qed.

  (** To use the refined search space with the abstract theorem, we must show
      that it still includes all relevant points. To this end, we first observe
      that a step in the blocking bound implies the existence of a task that
      could release a job with an absolute deadline equal to the absolute
      deadline of the job under analysis. *)
  Lemma task_with_equal_deadline_exists :
    forall {A},
      priority_inversion_changes_at (blocking_bound ts tsk) A ->
      exists tsk_o, (tsk_o \in ts)
                 && (blocking_relevant tsk_o)
                 && (tsk_o != tsk)
                 && (D tsk_o == D tsk + A).
  Proof.
    move=> A. rewrite /priority_inversion_changes_at => NEQ.
    have LEQ: blocking_bound ts tsk A <= blocking_bound ts tsk (A - ε) by apply: blocking_bound_decreasing; lia.
    have LT: blocking_bound ts tsk A < blocking_bound ts tsk (A - ε) by lia.
    move: LT; rewrite /blocking_bound => LT {LEQ} {NEQ}.
    move: (bigmax_witness_diff LT) => [tsk_o [IN [NOT HOLDS]]].
    move: HOLDS => /andP[REL LTeps].
    exists tsk_o; repeat (apply /andP; split) => //;
      first by apply /eqP => EQ; move: LTeps; rewrite EQ; lia.
    move: NOT; rewrite negb_and => /orP[/negP // |]; unfold D.
    by lia.
  Qed.

  (** With the above setup in place, we can show that the search space defined
      above by [is_in_search_space] covers the more abstract search space
      defined by [bounded_pi.is_in_search_space]. *)
  Lemma search_space_inclusion :
     forall {A L},
       bounded_pi.is_in_search_space ts tsk (blocking_bound ts tsk) L A ->
       is_in_search_space L A.
   Proof.
     move=> A L /andP[BOUND STEP].
     apply /andP; split => //; apply /orP.
     move: STEP => /orP[/orP[STEP|RBF] | IBF]; [right| by left| by right].
     move: (task_with_equal_deadline_exists STEP) => [tsk_o /andP[/andP[/andP[IN REL] OTHER] EQ]].
     rewrite /bound_on_total_hep_workload_changes_at.
     apply /hasP; exists tsk_o => //.
     apply /andP; split; first by rewrite eq_sym.
     move: EQ. rewrite /D => /eqP EQ.
     rewrite /task_request_bound_function EQ.
     move: REL; rewrite /blocking_relevant => /andP [ARRIVES COST].
     rewrite eqn_pmul2l //.
     have -> : A + task_deadline tsk - (task_deadline tsk + A)
              = 0 by lia.
     have -> : A + ε + task_deadline tsk - (task_deadline tsk + A)
              = ε by lia.
     by move: (H_valid_arrival_curve tsk_o IN) => [-> _]; lia.
   Qed.


  (** ** Response-Time Bound *)
  (** In this section, we prove that the maximum among the solutions of the response-time
      bound recurrence is a response-time bound for [tsk]. *)
  Section ResponseTimeBound.

    (** Let L be any positive fixed point of the busy interval recurrence. *)
    Variable L : duration.
    Hypothesis H_L_positive : L > 0.
    Hypothesis H_fixed_point : L = total_rbf L.

    (** Consider any value [R], and assume that for any given arrival
        offset [A] in the search space, there is a solution of the
        response-time bound recurrence which is bounded by [R]. *)
    Variable R : duration.
    Hypothesis H_R_is_maximum:
      forall (A : duration),
        is_in_search_space L A ->
        exists (F : duration),
          A + F >= blocking_bound ts tsk A
                  + (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk))
                  + bound_on_athep_workload ts tsk A (A + F) /\
          R >= F + (task_cost tsk - task_rtct tsk).

    (** Then, using the results for the general RTA for EDF-schedulers, we establish a
         response-time bound for the more concrete model of bounded non-preemptive segments.
         Note that in case of the general RTA for EDF-schedulers, we just _assume_ that
         the priority inversion is bounded. In this module we provide the preemption model
         with bounded non-preemptive segments and _prove_ that the priority inversion is
         bounded. *)
    Theorem uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments:
      response_time_bounded_by tsk R.
    Proof.
      apply: uniprocessor_response_time_bound_edf; eauto 4 with basic_rt_facts.
      { apply: priority_inversion_is_bounded => //.
        by move=> *; apply: nonpreemptive_segments_bounded_by_blocking. }
      - move=> A BPI_SP.
        by apply H_R_is_maximum, search_space_inclusion.
    Qed.

  End ResponseTimeBound.

End RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.
