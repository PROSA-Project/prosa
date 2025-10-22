Require Import prosa.analysis.facts.readiness.basic.
Require Export prosa.model.composite.valid_task_arrival_sequence.
Require Export prosa.analysis.facts.preemption.rtc_threshold.floating.
Require Export prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Export prosa.analysis.abstract.restricted_supply.bounded_bi.fp.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fp.
Require Export prosa.analysis.facts.model.sbf.periodic.

(** * RTA for FP Scheduling with Floating Non-Preemptive Regions on Uniprocessors under the Periodic Resource Model *)

(** In the following, we derive a response-time analysis for FP schedulers,
    assuming a workload of sporadic real-time tasks with floating non-preemptive
    regions, characterized by arbitrary arrival curves, executing upon a
    uniprocessor under the periodic resource model (see "Periodic Resource Model
    for Compositional Real-Time Guarantees" by Shin & Lee, RTSS 2003). To this
    end, we instantiate the sequential variant of _abstract Restricted-Supply
    Analysis_ (aRSA) as provided in the
    [prosa.analysis.abstract.restricted_supply] module. *)

Section RTAforFloatingFPModelwithArrivalCurves.

  (** ** Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is needed to
      define the system model under consideration. To this end, we next
      introduce and define the following notions using Prosa's standard
      definitions and behavioral semantics:

      - tasks, jobs, and their parameters,
      - the task set and the task under analysis,
      - the processor model,
      - the sequence of job arrivals,
      - the absence of self-suspensions,
      - an arbitrary schedule of the task set, and finally,
      - the resource-supply model. *)

  (** *** Tasks and Jobs  *)

  (** Consider tasks characterized by a WCET [task_cost], an arrival curve
      [max_arrivals], and a bound on the task's longest non-preemptive segment
      [task_max_nonpreemptive_segment], ... *)
  Context {Task : TaskType} `{TaskCost Task} `{MaxArrivals Task}
          `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and their associated jobs, where each job has a corresponding task
      [job_task], an execution time [job_cost], an arrival time [job_arrival],
      and a list of preemption points
      [job_preemptive_points]. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job} `{JobArrival Job}
          `{JobPreemptionPoints Job}.

  (** We assume that jobs are limited-preemptive. *)
  #[local] Existing Instance limited_preemptive_job_model.

  (** *** The Task Set and the Task Under Analysis*)

  (** Consider an arbitrary task set [ts], and ... *)
  Variable ts : seq Task.

  (** ... let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** *** Processor Model *)

  (** Consider any kind of fully-supply-consuming, unit-supply
      processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** *** The Job Arrival Sequence *)

  (** Allow for any possible arrival sequence [arr_seq] consistent with the
      parameters of the task set [ts]. That is, [arr_seq] is a valid arrival
      sequence in which each job's cost is upper-bounded by its task's WCET,
      every job stems from a task in [ts], and the number of arrivals respects
      each task's [max_arrivals] bound. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_task_arrival_sequence : valid_task_arrival_sequence ts arr_seq.

  (** Assume a model with floating non-preemptive regions. I.e., for each task
      only the length of the maximal non-preemptive segment is known and each
      job is divided into a number of non-preemptive segments by inserting
      preemption points. *)
  Hypothesis H_valid_task_model_with_floating_nonpreemptive_regions :
    valid_model_with_floating_nonpreemptive_regions arr_seq.

  (** *** Absence of Self-Suspensions *)

  (** We assume the classic (i.e., Liu & Layland) model of readiness without
      jitter or self-suspensions, wherein pending jobs are always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** *** The Schedule *)

  (** Consider an arbitrary fixed-priority policy [FP] that indicates a
      higher-or-equal priority relation among the tasks in [ts], and assume that
      the relation is reflexive and transitive. *)
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

  (** Consider a work-conserving, valid uniprocessor schedule with limited
      preemptions that corresponds to the given arrival sequence [arr_seq] (and
      hence the given task set [ts]). *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_schedule_with_limited_preemptions :
    schedule_respects_preemption_model arr_seq sched.

  (** We assume that the schedule respects the given [FP] scheduling policy. *)
  Hypothesis H_respects_policy :
    respects_FP_policy_at_preemption_point arr_seq sched FP.

  (** Furthermore, we require that the schedule ensures that jobs of the same
      task are executed in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.

  (** *** Periodic Resource Model *)

  (** Assume that the processor supply follows the *periodic resource model* as
      defined in "Periodic Resource Model for Compositional Real-Time
      Guarantees" by Shin & Lee (RTSS 2003). Under this model, the supply is
      distributed periodically with a resource period [Π] and a resource
      allocation time [γ]: in every interval <<[Π⋅k, Π⋅(k+1))>>, the processor
      provides at least [γ] units of supply. Furthermore, let [prm_sbf Π γ]
      denote the corresponding SBF defined in the paper, which, as proven in the
      same paper and verified in [prosa.analysis.facts.model.sbf.periodic], is a
      valid SBF. *)
  Variable Π γ : duration.
  Hypothesis H_periodic_resource_model : periodic_resource_model Π γ sched.

  (** ** Maximum Length of a Busy Interval *)

  (** In order to apply aRSA, we require a bound on the maximum busy-window
      length.  To this end, let [L] be any positive solution of the
      busy-interval "recurrence" (i.e., inequality) [prm_sbf Π γ L >=
      blocking_bound ts tsk +
      total_hep_request_bound_function_FP ts tsk L], as defined below.

      As the lemma [busy_intervals_are_bounded_rs_fp] shows, under [FP]
      scheduling, this condition is sufficient to guarantee that the maximum
      busy-window length is at most [L], i.e., the length of any busy interval
      is bounded by [L]. *)
  Definition busy_window_recurrence_solution (L : duration) :=
    L > 0
    /\ prm_sbf Π γ L >= blocking_bound ts tsk + total_hep_request_bound_function_FP ts tsk L.

  (** ** Response-Time Bound *)

  (** Having established all necessary preliminaries, it is finally time to
      state the claimed response-time bound [R]. *)

  (** A value [R] is a response-time bound for task [tsk] if, for any given
      offset [A] in the search space (w.r.t. the busy-window bound [L]), the
      response-time bound "recurrence" (i.e., inequality) has a solution [F] not
      exceeding [A + R]. *)
  Definition rta_recurrence_solution L R :=
    forall (A : duration),
      is_in_search_space tsk L A ->
      exists (F : duration),
        prm_sbf Π γ F >= blocking_bound ts tsk
                        + task_request_bound_function tsk (A + ε)
                        + total_ohep_request_bound_function_FP ts tsk F
        /\ A + R >= F.

  (** Finally, using the sequential variant of abstract restricted-supply
      analysis, we establish that, given a bound on the maximum busy-window
      length [L], any such [R] is indeed a sound response-time bound for task
      [tsk] under FP scheduling with floating non-preemptive regions on a
      unit-speed uniprocessor under the periodic resource model. *)
  Theorem uniprocessor_response_time_bound_floating_fp :
    forall (L : duration),
      busy_window_recurrence_solution L ->
      forall (R : duration),
        rta_recurrence_solution L R ->
        task_response_time_bound arr_seq sched tsk R.
  Proof.
    move=> L [BW_POS BW_SOL] R SOL js ARRs TSKs.
    have VAL1 : valid_preemption_model arr_seq sched
      by apply valid_fixed_preemption_points_model_lemma, H_valid_task_model_with_floating_nonpreemptive_regions.
    have [ZERO|POS] := posnP (job_cost js); first by rewrite /job_response_time_bound /completed_by ZERO.
    have VBSBF : valid_busy_sbf arr_seq sched tsk (prm_sbf Π γ).
    { by apply: valid_pred_sbf_switch_predicate; last apply prm_sbf_valid. }
    have US : unit_supply_bound_function (prm_sbf Π γ) by exact: prm_sbf_unit.
    have POStsk: 0 < task_cost tsk
      by move: TSKs => /eqP <-; apply: leq_trans; [apply POS | apply H_valid_task_arrival_sequence].
    eapply uniprocessor_response_time_bound_restricted_supply_seq with (L := L) (SBF := prm_sbf Π γ) => //=.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - by exact: instantiated_interference_and_workload_consistent_with_sequential_tasks => //.
    - eapply busy_intervals_are_bounded_rs_fp with (SBF := prm_sbf Π γ); try done.
      by eapply instantiated_i_and_w_are_coherent_with_schedule.
    - apply: valid_pred_sbf_switch_predicate; last first.
      + by apply prm_sbf_valid.
      + by move => ? ? ? ? [? ?]; split => //.
    - apply: instantiated_task_intra_interference_is_bounded; eauto 1 => //; first last.
      + by apply athep_workload_le_total_ohep_rbf.
      + apply: service_inversion_is_bounded => // => jo t1 t2 ARRo TSKo BUSYo.
        unshelve rewrite (leqRW (nonpreemptive_segments_bounded_by_blocking _ _ _ _ _ _ _ _ _)) => //.
        by instantiate (1 := fun _ => blocking_bound ts tsk).
    - move => A SP; move: (SOL A) => [].
      + apply: search_space_sub => //=.
        by apply: non_pathological_max_arrivals =>//; apply H_valid_task_arrival_sequence.
      + move => F [EQ1 EQ2].
        exists F; split; last split.
        * lia.
        * by rewrite /task_intra_IBF subnn subn0; lia.
        * by rewrite subnn addn0; exact: prm_sbf_monotone.
  Qed.

End RTAforFloatingFPModelwithArrivalCurves.
