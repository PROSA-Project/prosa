(** * Simulation Interval for Periodic Schedulers *)

(** This module develops the results of Guidolin–Pina et al., “Minimal
    simulation interval for periodic task schedulers”, Journal of Systems
    Architecture 179 (2026), 103939.
    #<br><a href="https://doi.org/10.1016/j.sysarc.2026.103939">DOI: 10.1016/j.sysarc.2026.103939</a>#

    Theorem 1 concerns a bounded first idle point ending a repeating
    hyperperiod. Corollary 4.1 specializes this bound to constrained offsets.
    Lemma 4.7 transfers a finite deadline check to the entire schedule.  Here we
    prove discrete-time versions of these statements.  As a notable deviation
    from the paper, whereas Guidolin-Pina et al. reason about a class of
    "resettable deterministic schedulers" that asserts properties of state-based
    schedulers, we introduce here a different scheduler contract that better
    suits Prosa's schedule representation (which does not explicitly model the
    scheduler itself). A general JLFP result establishes the reset contract from
    deterministic, antisymmetric priorities preserved across hyperperiods,
    yielding a finite deadline-check corollary for JLFP schedules.

    The development concerns fully preemptive ideal uniprocessors. *)

(** We reuse Prosa's periodic task, service, readiness, and deadline models. *)
Require Export prosa.analysis.facts.busy_interval.carry_in.
Require Export prosa.analysis.facts.hyperperiod.
Require Export prosa.analysis.facts.model.ideal.schedule.
Require Export prosa.analysis.facts.priority.jlfp.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.definitions.infinite_jobs.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.model.processor.ideal.
Require Export prosa.model.preemption.fully_preemptive.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.model.task.absolute_deadline.

Section SimulationInterval.

  (** ** System Model *)

  (** Tasks have arbitrary offsets and relative deadlines, periodic arrivals,
      and fixed execution requirements. *)
  Context {Task : TaskType} `{TaskOffset Task} `{PeriodicModel Task}
          `{TaskCost Task} `{TaskDeadline Task}.

  (** Jobs of these tasks have arrival times and execution requirements.  Each
      job's absolute is derived from its task's relative deadline via
      [job_deadline_from_task_deadline]. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobCost Job}.

  (** The considered workload is a finite set of periodic tasks ... *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods : valid_periods ts.

  (** ... generating a valid infinite arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.

  (** ... in which each task's first job arrives at its offset ... *)
  Hypothesis H_valid_offsets : valid_offsets arr_seq ts.

  (** ... and consecutive jobs of each task are separated by exactly one period. *)
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.

  (** Simulation uses the task WCET for every job, ensuring that execution
      requirements repeat. *)
  Hypothesis H_fixed_job_costs :
    forall j,
      arrives_in arr_seq j ->
      job_cost j = task_cost (job_task j).

  (** We assume that the system is not overloaded: the work arriving per
      hyperperiod fits in one hyperperiod of service.  This is the integer
      formulation of the paper's utilization bound [U <= 1], and permits both
      zero work and full utilization. *)
  Hypothesis H_no_overload : hyperperiod_workload ts <= hyperperiod ts.

  (** We use the basic Liu-and-Layland-style job readiness model, where every
      pending job is always ready to execute, including jobs whose deadlines
      have passed. *)
  Context {job_ready_model : JobReady Job (ideal.processor_state Job)}.
  Hypothesis H_basic_readiness : basic_readiness job_ready_model.

  (** In the following, we analyze a given well-formed, _work-conserving_
      schedule of the workload on an ideal uniprocessor. *)
  #[local] Existing Instance ideal.processor_state.
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Importantly, we make no assumption on which scheduling policy was used to
      obtain [sched] and do not assume any particular preemption model. *)

  (** ** Simulation Time Boundaries *)

  (** We now identify the part of the schedule that a finite simulation must
      cover. The following definitions translate the paper's time conventions to
      Prosa's discrete time model and specify where to look for a no-carry-in
      instant that bounds a complete repeating hyperperiod. *)

  (** Following Definition 4.1 in the paper, the "onset of global periodicity"
      is the maximum of [task_offset tsk + 1 - task_period tsk], with saturating
      subtraction and an empty maximum of zero. This translates the paper's
      strict inequality [t > O - T]; in particular, [O = T] requires [t >= 1]. *)
  Definition arrival_periodicity_start :=
    max0 [seq task_offset tsk + 1 - task_period tsk | tsk <- ts].

  (** When every task's offset is strictly less than its period, i.e., when all
      tasks have constrained offsets, then this bound reduces to zero, yielding
      the horizon specialization of Corollary 4.1. *)
  Remark constrained_offsets_periodicity :
    constrained_offsets ts ->
    arrival_periodicity_start = 0.
  Proof.
    move=> H_constrained_offsets; rewrite /arrival_periodicity_start.
    case E: [seq task_offset tsk + 1 - task_period tsk | tsk <- ts] => [|x xs] //.
    apply: max0_of_uniform_set => // y H_y.
    have /mapP [tsk H_tsk ->] :
      y \in [seq task_offset tsk + 1 - task_period tsk | tsk <- ts] by rewrite E.
    apply/eqP; rewrite subn_eq0 addn1.
    exact: H_constrained_offsets tsk H_tsk.
  Qed.

  (** The search for a no-carry-in instant starts one hyperperiod after the arrival
      boundary. This is the first integer strictly after the paper's
      [t0 + H], interpreting [0^-] as the predecessor of zero. *)
  Definition no_carry_in_search_start := arrival_periodicity_start + hyperperiod ts.

  (** The _simulation horizon_ is the main bound of interest: the main claim
      established below is that a simulation must cover only the jobs that
      arrive prior to this horizon to establish schedulability for _all_ jobs
      (up to infinity).  It accounts for the initial transient through the
      no-carry-in search boundary as well as for the total amount of work
      carried out by the tasks in one hyperperiod.  *)
  Definition simulation_horizon :=
    no_carry_in_search_start + (hyperperiod_workload ts - 1).

  (** The paper's "idle points" are exactly Prosa's [no_carry_in] times: every
      job arriving strictly before the instant has completed. This gives the
      scheduler an empty backlog before processing new arrivals.  New jobs may
      arrive and execute at the idle point itself. *)

  (** The first no-carry-in instant at or after the search start identifies
      the earliest eligible boundary for the simulation. *)
  Definition first_no_carry_in_instant (t : instant) :=
    no_carry_in_search_start <= t
    /\ no_carry_in arr_seq sched t
    /\ forall t',
        no_carry_in_search_start <= t' ->
        t' < t ->
        exists_carry_in arr_seq sched t'.


  (** ** Existence of a No-Carry-In Instant *)

  (** With the system model and key definitions in place, we begin by observing
      that the first no-carry-in instant always exists before the simulation
      horizon because the system is (a) not overloaded and (b) work-conserving. *)
  Local Lemma first_no_carry_in_instant_within_horizon :
    exists2 t,
      first_no_carry_in_instant t
      & t <= simulation_horizon.
  Proof.
    have suff:
      exists t,
        (no_carry_in_search_start <= t <= simulation_horizon)
        && ~~ exists_carry_in arr_seq sched t.
    { move=> EX.
      have [no_carry_in_instant /andP [/andP [START BOUND] /negP NCI] MIN] := ex_minnP EX.
      exists no_carry_in_instant => //; split=> //; split.
      - move=> j ARR BEFORE; apply/negPn/negP => NCOMP.
        apply: NCI; apply/exists_carry_inP => // NCI'.
        by move: NCOMP; rewrite (NCI' j ARR BEFORE).
      - move=> t LOW HIGH; apply/negPn/negP => NCI'.
        suff : no_carry_in_instant <= t by rewrite leqNgt HIGH.
        apply: MIN; rewrite NCI' andbT LOW /=.
        exact: leq_trans (ltnW HIGH) BOUND. }
    apply.
    have [δ [LT NCI]] :
      exists δ,
        δ < maxn 1 (hyperperiod_workload ts)
        /\ no_carry_in arr_seq sched (no_carry_in_search_start + δ).
    { apply: (processor_is_not_too_busy arr_seq _ _ _ sched _ _ _
                (JLFP := {| hep_job := fun _ _ => true |})) => //.
      - by apply: basic_readiness_is_work_bearing_readiness.
      - by rewrite leq_max leqnn.
      - move=> t _.
        rewrite /blackout_during big1;
          first by move=> t' _; rewrite /is_blackout ideal_proc_has_supply.
        rewrite add0n.
        apply: (leq_trans _ (leq_maxr _ _)).
        apply: leq_trans; last apply: workload_in_hyperperiod_bounded => //.
        + apply: workload_of_jobs_reduce_range; first exact: leq_addr.
          rewrite leq_add2l geq_max H_no_overload andbT.
          exact: valid_periods_imply_pos_hp.
        + by move=> j ARR; rewrite /valid_job_cost H_fixed_job_costs. }
    exists (no_carry_in_search_start + δ); apply/andP; split.
    - rewrite leq_addr /= /simulation_horizon leq_add2l.
      by move: LT; case: (hyperperiod_workload ts) => [|workload];
        rewrite ?maxn0 ?maxnSS ?max0n subn1 /=.
    - by apply/negP => /exists_carry_inP; apply.
  Qed.


  (** We next establish some auxiliary lemmas that we require for the subsequent
      proofs. *)

  (** ** Matching Jobs Across Hyperperiods *)

  (** To relate "matching" jobs across hyperperiods, we use Prosa's [next_hyperperiod_job]
      and [prev_hyperperiod_job] definitions. We establish some useful facts
      about these definitions in our specific context. *)

  (** As a stepping stone, we observe that jobs that arrive after the starting
      threshold for the no-carry-in instant search have indeed a predecessor
      that arrives exactly one hyperperiod earlier. *)
  Local Lemma late_arrival_job_index :
    forall j,
      arrives_in arr_seq j ->
      no_carry_in_search_start <= job_arrival j ->
      jobs_per_hyperperiod ts (job_task j) <= job_index arr_seq j.
  Proof.
    move=> j ARR LATE.
    case: (leqP (jobs_per_hyperperiod ts (job_task j)) (job_index arr_seq j)) => // INDEX.
    exfalso; move: LATE; apply/negP.
    rewrite -ltnNge /no_carry_in_search_start
      (periodic_arrival_times arr_seq _ (job_task j) _ _ _ (job_index arr_seq j) j) //.
    apply: (ltn_leq_trans (n := arrival_periodicity_start
                               + (job_index arr_seq j).+1 * task_period (job_task j))).
    - rewrite mulSn addnA ltn_add2r addnC -leq_subLR -addn1.
      apply: in_max0_le.
      by apply: map_f; apply: H_all_jobs_from_taskset.
    - by rewrite (hyperperiod_as_job_count ts (job_task j)) //
                 leq_add2l leq_mul2r INDEX orbT.
  Qed.

  (** A job's "matching successor" indeed arrives during the next hyperperiod. *)
  Local Lemma next_hyperperiod_job_in_next_interval :
    forall start j,
      j \in arrivals_between arr_seq start (start + hyperperiod ts) ->
      next_hyperperiod_job ts arr_seq j \in
        arrivals_between arr_seq
          (start + hyperperiod ts)
          (start + 2 * hyperperiod ts).
  Proof.
    move=> start j /[dup]
      /(in_arrivals_implies_arrived arr_seq j _ _) ARR
      /(job_arrival_between arr_seq H_valid_arrival_sequence.1) /andP [LOW HIGH].
    apply: arrived_between_implies_in_arrivals => //.
    - by apply: (next_hyperperiod_job_arrives arr_seq _ ts (job_task j)).
    - by rewrite /arrived_between
        (next_hyperperiod_job_arrival arr_seq _ ts (job_task j)) //
        mul2n -addnn addnA leq_add2r ltn_add2r LOW HIGH.
  Qed.

  (** From the arrival boundary onward, there is a "matching predecessor" in the
      preceding hyperperiod for every later release. *)
  Local Lemma prev_hyperperiod_job_in_prev_interval :
    forall start j,
      arrival_periodicity_start <= start ->
      j \in arrivals_between arr_seq
        (start + hyperperiod ts)
        (start + 2 * hyperperiod ts) ->
      prev_hyperperiod_job ts arr_seq j \in
        arrivals_between arr_seq start (start + hyperperiod ts).
  Proof.
    move=> start j START /[dup]
      /(in_arrivals_implies_arrived arr_seq j _ _) ARR
      /(job_arrival_between arr_seq H_valid_arrival_sequence.1) /andP [LOW HIGH].
    have INDEX : jobs_per_hyperperiod ts (job_task j) <= job_index arr_seq j.
    { apply: late_arrival_job_index => //.
      apply: (leq_trans _ LOW).
      by rewrite /no_carry_in_search_start leq_add2r. }
    apply: arrived_between_implies_in_arrivals => //.
    - by apply: (prev_hyperperiod_job_arrives arr_seq _ ts (job_task j)).
    - rewrite /arrived_between
        (prev_hyperperiod_job_arrival arr_seq _ ts (job_task j)) //.
      apply/andP; split.
      + rewrite -[start](addnK (hyperperiod ts)).
        exact: leq_sub2r _ LOW.
      + rewrite ltn_subLR; first exact: leq_trans (leq_addl _ _) LOW.
        by rewrite addnCA addnn -mul2n.
  Qed.

  (** For jobs that arrive after the start of periodicity, the "matching
      successor" and "matching predecessor" relationships cancel out. *)
  Local Lemma next_prev_hyperperiod_job_in_interval :
    forall start j,
      arrival_periodicity_start <= start ->
      j \in arrivals_between arr_seq
        (start + hyperperiod ts)
        (start + 2 * hyperperiod ts) ->
      next_hyperperiod_job ts arr_seq (prev_hyperperiod_job ts arr_seq j)
      = j.
  Proof.
    move=> start j START /[dup]
      /(in_arrivals_implies_arrived arr_seq j _ _) ARR
      /(job_arrival_between arr_seq H_valid_arrival_sequence.1) /andP [LOW HIGH].
    apply: next_prev_hyperperiod_job => //.
    apply: late_arrival_job_index => //.
    apply: (leq_trans _ LOW).
    by rewrite /no_carry_in_search_start leq_add2r.
  Qed.

  (** Next, we establish two helper lemmas on the workload in intervals exactly
      one hyperperiod apart. *)

  (** ** Relating Workload Across Hyperperiods *)

  (** The total workload in a given interval is never less than the total
      workload in an interval of the same length exactly one hyperperiod
      later. This holds even during the initial transient. *)
  Lemma workload_nondecreasing_after_hyperperiod_shift :
    forall start stop,
      total_workload_between arr_seq start stop
      <= total_workload_between arr_seq
          (start + hyperperiod ts)
          (stop + hyperperiod ts).
  Proof.
    move=> start stop; rewrite /total_workload_between /total_workload /workload_of_jobs.
    apply: (@leq_trans (\sum_(j <- [seq next_hyperperiod_job ts arr_seq j
      | j <- arrivals_between arr_seq start stop]) job_cost j)).
    - rewrite big_map; apply: leq_sum_seq => j
        /(in_arrivals_implies_arrived arr_seq j _ _) ARR _.
      rewrite !H_fixed_job_costs ?next_hyperperiod_job_task //.
      by apply: (next_hyperperiod_job_arrives arr_seq _ ts (job_task j)).
    - apply: leq_sum_sub_uniq.
      + rewrite map_inj_in_uniq; last by apply: arrivals_uniq.
        apply: (can_in_inj (g := prev_hyperperiod_job ts arr_seq)) => j
          /(in_arrivals_implies_arrived arr_seq j _ _) ARR.
        by apply: prev_next_hyperperiod_job.
      + move=> j /mapP [j' /[dup]
          /(in_arrivals_implies_arrived arr_seq j' _ _) ARR
          /(job_arrival_between arr_seq H_valid_arrival_sequence.1) RANGE ->].
        apply: arrived_between_implies_in_arrivals => //.
        * by apply: (next_hyperperiod_job_arrives arr_seq _ ts (job_task j')).
        * by rewrite /arrived_between
            (next_hyperperiod_job_arrival arr_seq _ ts (job_task j')) //
            leq_add2r ltn_add2r.
  Qed.

  (** Once arrivals repeat, the workload comparison becomes an equality. *)
  Lemma workload_equal_across_hyperperiods :
    forall start,
      arrival_periodicity_start <= start ->
      total_workload_between arr_seq
        start
        (start + hyperperiod ts)
      = total_workload_between arr_seq
          (start + hyperperiod ts)
          (start + 2 * hyperperiod ts).
  Proof.
    move=> start START; apply/eqP.
    rewrite eqn_leq; apply/andP; split.
    { rewrite mul2n -addnn addnA.
      exact: workload_nondecreasing_after_hyperperiod_shift. }
    rewrite /total_workload_between /total_workload /workload_of_jobs.
    apply: (@leq_trans (\sum_(j <- [seq prev_hyperperiod_job ts arr_seq j
      | j <- arrivals_between arr_seq (start + hyperperiod ts)
        (start + 2 * hyperperiod ts)]) job_cost j)).
    - rewrite big_map; apply: leq_sum_seq => j IN _.
      rewrite !H_fixed_job_costs ?prev_hyperperiod_job_task //.
      + exact: in_arrivals_implies_arrived.
      + apply: in_arrivals_implies_arrived.
        exact: (prev_hyperperiod_job_in_prev_interval start).
    - apply: leq_sum_sub_uniq.
      + rewrite map_inj_in_uniq; last by apply: arrivals_uniq.
        apply: (can_in_inj (g := next_hyperperiod_job ts arr_seq)) => j IN.
        exact: (next_prev_hyperperiod_job_in_interval start).
      + move=> j /mapP [j' IN ->].
        exact: prev_hyperperiod_job_in_prev_interval.
  Qed.


  (** ** Resettable Deterministic Schedulers *)

  (** Guidolin–Pina et al. introduce a notion of "resettable deterministic
      schedulers" (RDS) to state their result in broad terms, independently of a
      specific scheduling policy such as FP or EDF. The essence of their
      definition is that such a scheduler must reset to a known internal state
      whenever it encounters a no-carry-in instant. They then argue that an RDS
      scheduler must necessarily produce a recurring schedule under the stated
      system model.

      In Prosa, we represent schedules directly, typically without reasoning
      about the scheduler that produces the schedule. Their definition does not
      translate directly to our setting. Instead, we explicitly require the
      schedule to exhibit a recurring pattern. *)

  (** First, a hyperperiod-sized interval is _self-contained_ if it has a
      no-carry-instant on both ends, which implies that no workload "bleeds in
      or out" of the interval. *)
  Definition self_contained_hyperperiod (start : instant) :=
    no_carry_in arr_seq sched start
    /\ no_carry_in arr_seq sched (start + hyperperiod ts).

  (** We say that _execution repeats_ at time [t] in schedule [sched]
      (w.r.t. the workload's hyperperiod) if the "matching successor" job given
      by [next_hyperperiod_job] (if any) is scheduled at time [t + hyperperiod
      ts]. Similarly, if no job is scheduled at time [t], then [t + hyperperiod
      ts] must also be idle. *)
  Definition execution_repeats_at (t : instant) :=
    if sched t is Some j
    then sched (t + hyperperiod ts) = Some (next_hyperperiod_job ts arr_seq j)
    else sched (t + hyperperiod ts) = None.

  (** No-carry-in instants give the scheduler matching reset states. This
      contract captures the consequence of resettable determinism needed here:
      corresponding arrivals produce matching execution over the following
      hyperperiod. This lets us propagate no-carry-in boundaries and establish
      indefinite repetition by induction over successive hyperperiods.

      We show further below in lemma [jlfp_respects_hyperperiod_reset] that JLFP
      policies satisfy this requirement under mild assumptions (antisymmetric
      job prioritization that agrees across hyperperiods). *)
  Definition respects_hyperperiod_reset :=
    forall reset_time,
      arrival_periodicity_start <= reset_time ->
      self_contained_hyperperiod reset_time ->
      forall elapsed,
        elapsed < hyperperiod ts ->
        execution_repeats_at (reset_time + elapsed).

  (** The consequence of the RDS contract is that execution repeats forever
      after the initial transient, which we define here and establish below. *)
  Definition repeats_forever_from (start : instant) :=
    forall delta,
      execution_repeats_at (start + delta).

  (** ** Self-Contained Hyperperiod Propagation *)

  (** We next establish that, if the schedule repeats, then a self-contained
      hyperperiod begets a successive self-contained hyperperiod, thereby
      propagating the notion to infinity. *)

  (** As the first step, we note that the [service] received by matching jobs is
      equal at all points across successive hyperperiods, ... *)
  Lemma service_repeats_in_hyperperiod :
    forall start elapsed j,
      j \in arrivals_between arr_seq start (start + hyperperiod ts) ->
      (forall delta,
         delta < elapsed ->
         execution_repeats_at (start + delta)) ->
      service sched
        (next_hyperperiod_job ts arr_seq j)
        (start + hyperperiod ts + elapsed)
      = service sched j (start + elapsed).
  Proof.
    move=> start elapsed j /[dup]
      /(in_arrivals_implies_arrived arr_seq j _ _) ARR
      /(job_arrival_between arr_seq H_valid_arrival_sequence.1) /andP [LOW _] REPEAT.
    rewrite -(service_cat _ _ (start + hyperperiod ts)) ?leq_addr //
            -(service_cat _ j start) ?leq_addr //
            !no_service_before_arrival // ?add0n.
    - by rewrite (next_hyperperiod_job_arrival arr_seq _ ts (job_task j)) // leq_add2r.
    - rewrite /service_during big_addn addnAC addnK.
      apply: eq_big_nat => t /andP [LO HI].
      have : execution_repeats_at t.
      { rewrite -(subnKC LO); apply: REPEAT.
        by rewrite ltn_subLR // addnC. }
      rewrite /execution_repeats_at !service_at_def.
      case SCHED: (sched t) => [j'|] -> //=.
      move /eqP: SCHED; rewrite -scheduled_at_def =>
           /(valid_schedule_jobs_come_from_arrival_sequence sched arr_seq H_valid_schedule) ARR'.
      apply: congr1; rewrite !eqE /=.
      apply/idP/idP; last by move/eqP=> ->; rewrite eqxx.
      move/eqP/(congr1 (prev_hyperperiod_job ts arr_seq)).
      rewrite (prev_next_hyperperiod_job arr_seq _ ts (job_task j')) //
        (prev_next_hyperperiod_job arr_seq _ ts (job_task j)) //.
      by move=> ->; rewrite eqxx.
  Qed.

  (** ... which trivially extends to the [pending] predicate. *)
  Corollary pending_repeats_in_hyperperiod :
    forall start elapsed j,
      j \in arrivals_between arr_seq start (start + hyperperiod ts) ->
      (forall delta, delta < elapsed -> execution_repeats_at (start + delta)) ->
      pending sched
        (next_hyperperiod_job ts arr_seq j)
        (start + hyperperiod ts + elapsed)
      = pending sched j (start + elapsed).
  Proof.
    move=> start elapsed j IN REPEAT.
    have ARR : arrives_in arr_seq j by exact: in_arrivals_implies_arrived.
    rewrite /pending /has_arrived /completed_by service_repeats_in_hyperperiod //
      (next_hyperperiod_job_arrival arr_seq _ ts (job_task j)) //
      addnAC leq_add2r !H_fixed_job_costs ?next_hyperperiod_job_task //.
    by apply: next_hyperperiod_job_arrives.
  Qed.

  (** We obtain the induction step for repeating self-contained hyperperiods. *)
  Lemma self_contained_hyperperiod_propagates :
    forall start,
      arrival_periodicity_start <= start ->
      self_contained_hyperperiod start ->
      (forall elapsed,
         elapsed < hyperperiod ts ->
         execution_repeats_at (start + elapsed)) ->
      self_contained_hyperperiod (start + hyperperiod ts).
  Proof.
    move=> start START [_ NCI] REPEAT; split=> // j ARR BEFORE.
    case: (ltnP (job_arrival j) (start + hyperperiod ts)) => [OLD|NEW].
    - apply: completion_monotonic; last exact: NCI.
      exact: leq_addr.
    - have suff : j \in arrivals_between arr_seq (start + hyperperiod ts)
          (start + 2 * hyperperiod ts).
      { move=> IN.
        have PRE := prev_hyperperiod_job_in_prev_interval start j START IN.
        rewrite -(next_prev_hyperperiod_job_in_interval start j START IN) /completed_by
          service_repeats_in_hyperperiod //.
        rewrite (next_prev_hyperperiod_job_in_interval start j START IN)
          H_fixed_job_costs // -(prev_hyperperiod_job_task arr_seq ts j) -H_fixed_job_costs;
          first exact: in_arrivals_implies_arrived.
        apply: NCI;
          first exact: in_arrivals_implies_arrived.
        by move: PRE =>
          /(job_arrival_between arr_seq H_valid_arrival_sequence.1) /andP []. }
      apply; apply: arrived_between_implies_in_arrivals => //.
      by rewrite /arrived_between NEW /= mul2n -addnn addnA.
  Qed.

  (** ** Repeating Schedule *)

  (** We now have the ingredients for a repeating schedule. To bring them
      together, we first need two no-carry-in instants one hyperperiod apart.
      Fortunately, finding the later instant also tells us that there are no
      carry-in jobs at the earlier one, either. The intuition, captured by the
      workload argument of Lemma 4.5 in the paper, is that any unfinished
      backlog at the earlier boundary would leave unfinished work one
      hyperperiod later as well. *)
  Lemma no_carry_in_previous_hyperperiod :
    forall t,
      no_carry_in arr_seq sched (t + hyperperiod ts) ->
      no_carry_in arr_seq sched t.
  Proof.
    move=> t NCI j ARR BEFORE; apply/negPn/negP => NCOMP.
    (* We consider all jobs together so that the busy-interval facts describe
       the processor's total workload. *)
    pose all_equal : JLFP_policy Job := {| hep_job := fun _ _ => true |}.
    have /(exists_busy_interval_prefix arr_seq H_valid_arrival_sequence sched
      (JLFP := all_equal) j ARR (fun _ => erefl true) t)
      [start [PREFIX /andP [LOW _]]] : pending sched j t.
    { apply/andP; split=> //; exact: ltnW BEFORE. }
    have BUSY : forall u, start < u <= start + (t - start) ->
      ~ @quiet_time _ _ _ _ arr_seq sched all_equal j u.
    { move=> u; rewrite subnKC ?(leq_trans LOW (ltnW BEFORE)) // -[u <= t]ltnS.
      exact: busy_interval_prefix_no_quiet_time. }
    suff : t - start < t - start by rewrite ltnn.
    apply: (ltn_leq_trans (n := total_workload_between arr_seq start t)).
    - rewrite -{2}[t](subnKC (leq_trans LOW (ltnW BEFORE))).
      apply: leq_ltn_trans;
        last apply: (busy_interval_too_much_workload arr_seq _ sched _ _
          (JLFP := all_equal) j _ t) => //.
      + rewrite (hep_jobs_receive_no_service_before_quiet_time arr_seq _ sched _
          (JLFP := all_equal) j) //; first by case: PREFIX => _ [].
        apply/eq_leq/esym.
        apply: (no_idle_time_within_non_quiet_time_interval arr_seq _ sched _ _
          (JLFP := all_equal) _ j) => //.
        by apply: basic_readiness_is_work_bearing_readiness.
      + rewrite subn_gt0; exact: leq_ltn_trans LOW BEFORE.
    - apply: leq_trans; first exact: workload_nondecreasing_after_hyperperiod_shift.
      rewrite /total_workload_between /total_workload
        (all_jobs_have_completed_impl_workload_eq_service _ arr_seq _ sched _ _
          predT _ _ (t + hyperperiod ts)) //.
      + move=> j' /[dup] /(in_arrivals_implies_arrived arr_seq j' _ _) ARR'
          /(job_arrival_between arr_seq H_valid_arrival_sequence.1) /andP [_ BEFORE'] _.
        exact: NCI.
      + rewrite -[t - start](subnDr (hyperperiod ts)).
        by apply: service_of_jobs_le_length_of_interval'.
  Qed.

  (** With a self-contained hyperperiod in hand, we can now follow the
      schedule forward. The RDS contract gives us matching execution in
      the next hyperperiod, and the propagation lemma above tells us that
      this next hyperperiod is self-contained too. We can therefore apply
      the same reasoning again, carrying the repeating pattern forward. *)
  Lemma self_contained_hyperperiod_repeats_forever :
    respects_hyperperiod_reset ->
    forall start,
      arrival_periodicity_start <= start ->
      self_contained_hyperperiod start ->
      repeats_forever_from start.
  Proof.
    move=> RESET start START NCI elapsed.
    have suff : forall n, self_contained_hyperperiod (start + n * hyperperiod ts).
    { move=> CYCLES; rewrite [elapsed](divn_eq elapsed (hyperperiod ts)) addnA.
      apply: RESET.
      - exact: leq_trans START (leq_addr _ _).
      - exact: CYCLES.
      - apply: ltn_pmod; exact: valid_periods_imply_pos_hp. }
    apply; elim=> [|n IH]; first by rewrite mul0n addn0.
    rewrite mulSn [hyperperiod ts + _]addnC addnA.
    apply: self_contained_hyperperiod_propagates => //.
    - exact: leq_trans START (leq_addr _ _).
    - apply: RESET => //.
      exact: leq_trans START (leq_addr _ _).
  Qed.

  (** ** Minimal Simulation Interval *)

  (** We are now ready to put the pieces together and establish our version of
      Guidolin–Pina et al.'s Theorem 1. The first no-carry-in instant in our
      search lies within the simulation horizon. Looking back one hyperperiod
      gives us the other no-carry-in instant, so the interval between them is
      self-contained.  From the start of this interval onward, the schedule
      follows the same pattern forever.

      For tasks with constrained offsets, [constrained_offsets_periodicity] lets
      us place the arrival boundary at zero. The horizon then simplifies to
      [hyperperiod ts + (hyperperiod_workload ts - 1)], giving the
      specialization in Corollary 4.1. Rocq's subtraction saturates at zero, so
      this bound also covers the corner case of task sets with zero workload. *)
  Theorem minimal_simulation_interval :
    respects_hyperperiod_reset ->
    exists no_carry_in_instant,
      first_no_carry_in_instant no_carry_in_instant
      /\ no_carry_in_instant <= simulation_horizon
      /\ repeats_forever_from (no_carry_in_instant - hyperperiod ts).
  Proof.
    move=> RESET.
    have [no_carry_in_instant /[dup] FIRST [START [NCI _]] BOUND] :=
      first_no_carry_in_instant_within_horizon.
    exists no_carry_in_instant; split=> //; split=> //.
    have SHIFT : no_carry_in_instant - hyperperiod ts + hyperperiod ts = no_carry_in_instant.
    { apply: subnK; exact: leq_trans (leq_addl _ _) START. }
    apply: self_contained_hyperperiod_repeats_forever => //.
    - by rewrite -(leq_add2r (hyperperiod ts)) SHIFT.
    - split; last by rewrite SHIFT.
      apply: no_carry_in_previous_hyperperiod.
      by rewrite SHIFT.
  Qed.

  (** ** Finite Deadline Check *)

  (** Having found a repeating pattern, we can turn our attention to
      deadlines. We collect the jobs arriving up to and including a chosen
      horizon and check that each of them meets its deadline. These jobs
      will serve as our representatives for the rest of the schedule. *)
  Definition deadlines_checked_through (horizon : instant) :=
    all (job_meets_deadline sched) (arrivals_up_to arr_seq horizon).

  (** The repeating pattern explains why these representatives suffice.
      Theorem 1 places a complete repeating hyperperiod within our simulation
      horizon. Every later job has a matching predecessor one hyperperiod
      earlier, with the same execution requirement and relative deadline.
      Since matching jobs receive the same service at corresponding times,
      they also share the same deadline outcome. Stepping backward through
      these predecessors eventually brings us to a job covered by the finite
      check. This gives us the guarantee for the entire schedule, as stated
      in Lemma 4.7.  *)
  Theorem finite_deadline_check :
    respects_hyperperiod_reset ->
    deadlines_checked_through simulation_horizon ->
    all_deadlines_of_arrivals_met arr_seq sched.
  Proof.
    move=> RESET /allP CHECK.
    have [no_carry_in_instant [[START _] [BOUND REPEAT]]] := minimal_simulation_interval RESET.
    rewrite /no_carry_in_search_start in START.
    have HP : 0 < hyperperiod ts by exact: valid_periods_imply_pos_hp.
    (** We follow the chain of matching predecessors by induction on arrival
        time, until we reach a job whose deadline has already been checked. *)
    have suff : forall t (j : Job), job_arrival j <= t -> arrives_in arr_seq j ->
        job_meets_deadline sched j.
    { move=> ALL j; exact: ALL (leqnn _). }
    apply; apply: ltn_ind => t IH j BEFORE ARR.
    case: (leqP (job_arrival j) simulation_horizon) => [CHECKED|LATE].
    - by apply: CHECK; apply: arrived_between_implies_in_arrivals.
    - have INDEX : jobs_per_hyperperiod ts (job_task j) <= job_index arr_seq j.
      { apply: late_arrival_job_index => //.
        exact: leq_trans START (leq_trans BOUND (ltnW LATE)). }
      have PRE : arrives_in arr_seq (prev_hyperperiod_job ts arr_seq j)
        by apply: prev_hyperperiod_job_arrives.
      (** We can now compare the job with its predecessor: the repeating
          execution pattern gives them matching service through their
          respective deadlines. *)
      rewrite /job_meets_deadline /completed_by /job_deadline
        /= -[j in service _ j _](next_prev_hyperperiod_job arr_seq _ ts (job_task j)) //.
      rewrite -[job_arrival j](subnK (_ : hyperperiod ts <= job_arrival j)); first by lia.
      rewrite service_repeats_in_hyperperiod.
      + apply: arrived_between_implies_in_arrivals => //.
        rewrite /arrived_between (prev_hyperperiod_job_arrival arr_seq _ ts (job_task j)) //.
        by lia.
      + move=> delta LT.
        rewrite -(subnKC (_ : no_carry_in_instant - hyperperiod ts <=
                             job_arrival j - hyperperiod ts + delta));
          first by lia.
        exact: REPEAT.
      + rewrite H_fixed_job_costs // -(prev_hyperperiod_job_task arr_seq ts j)
          -H_fixed_job_costs //
          -(prev_hyperperiod_job_arrival arr_seq _ ts (job_task j)) //.
        apply: (IH (job_arrival (prev_hyperperiod_job ts arr_seq j))) => //.
        rewrite (prev_hyperperiod_job_arrival arr_seq _ ts (job_task j)) //.
        by lia.
  Qed.

  (** ** RDS Contract for JLFP Priority Policies *)

  (** So far, we have used the reset contract as an assumption. We now show
      how a job-level fixed-priority (JLFP) policy can provide this contract.
      The intuition is that, when corresponding jobs are pending and their
      priority order agrees, the scheduler makes corresponding choices.
      Starting from empty backlogs, we can follow these choices through a
      whole hyperperiod. *)
  Section JLFP_RDS.

    (** We begin with a JLFP policy, whose priority relation between jobs
        stays fixed as time passes. We include the scheduler's way of
        breaking priority ties in this relation too. *)
    Context {JLFP : JLFP_policy Job}.

    (** We consider fully preemptive jobs, so the scheduler can enforce the
        priority order at every instant, ... *)
    #[local] Existing Instance fully_preemptive_job_model.

    (** ... and assume that the schedule indeed complies with job priorities at
        all times. *)
    Hypothesis H_respects_policy :
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

    (** To make the choice of job deterministic, we also ask that the order
        resolve priority ties uniquely among arriving jobs. This is the role of
        _antisymmetry_: together with policy compliance, it ensures that the
        same pending jobs force the same choice. *)
    Hypothesis H_priority_antisymmetric :
      antisymmetric_job_priorities JLFP arr_seq.

    (** Finally, the priority order must agree across hyperperiods. When we
        replace jobs by their matching successors, their relative order,
        including the way ties are broken, stays the same. This lets us carry a
        scheduling decision from one hyperperiod to the next. *)
    Hypothesis H_priority_shift_invariant :
      priorities_consistent_across_hyperperiods ts arr_seq JLFP.

    (** Let us first look at a single scheduling decision. Suppose execution
        has already matched up to this point in the two hyperperiods. The
        service and pending-job results above tell us that the chosen job's
        matching successor is pending too. The preserved priority order
        then puts this successor ahead of every competing choice.

        Prosa's [jlfp_pending_highest_priority_job_is_scheduled] lemma lets
        us conclude that the successor is indeed the job that runs. This
        gives us the next matching decision. *)
    Local Lemma jlfp_scheduled_job_repeats :
      forall start elapsed j,
        arrival_periodicity_start <= start ->
        self_contained_hyperperiod start ->
        elapsed < hyperperiod ts ->
        (forall delta, delta < elapsed -> execution_repeats_at (start + delta)) ->
        scheduled_at sched j (start + elapsed) ->
        scheduled_at sched
          (next_hyperperiod_job ts arr_seq j)
          (start + hyperperiod ts + elapsed).
    Proof.
      move=> start elapsed j START [NCI NCI_NEXT] LT REPEAT /[dup] SCHED
        /(valid_schedule_jobs_come_from_arrival_sequence sched arr_seq H_valid_schedule) ARR.
      apply: jlfp_pending_highest_priority_job_is_scheduled => //.
      - by rewrite /preemption_time;
          case: (scheduled_job_at arr_seq sched (start + hyperperiod ts + elapsed)).
      - by apply: next_hyperperiod_job_arrives.
      - rewrite pending_repeats_in_hyperperiod //.
        apply: (pending_job_not_carried_in arr_seq _ sched _ _ (start + elapsed)) => //.
        by rewrite leq_addr ltn_add2l.
      - move=> j' SCHED' NEQ.
        have IN : j' \in arrivals_between arr_seq (start + hyperperiod ts)
            (start + 2 * hyperperiod ts).
        { rewrite mul2n -addnn addnA.
          apply: (pending_job_not_carried_in arr_seq _ sched _ _
            (start + hyperperiod ts + elapsed)) => //.
          by rewrite leq_addr ltn_add2l. }
        rewrite -(next_prev_hyperperiod_job_in_interval start j' START IN)
          H_priority_shift_invariant //.
        + apply: in_arrivals_implies_arrived.
          by apply: (prev_hyperperiod_job_in_prev_interval start).
        + apply: (H_respects_policy _ _ (start + elapsed)) => //.
          * apply: in_arrivals_implies_arrived.
            by apply: (prev_hyperperiod_job_in_prev_interval start).
          * by rewrite /preemption_time; case: (scheduled_job_at arr_seq sched (start + elapsed)).
          * rewrite /backlogged H_basic_readiness -pending_repeats_in_hyperperiod //.
            -- by apply: (prev_hyperperiod_job_in_prev_interval start).
            -- rewrite (next_prev_hyperperiod_job_in_interval start j' START IN).
               apply/andP; split; first exact: scheduled_implies_pending.
               move: SCHED; rewrite !scheduled_at_def => /eqP ->.
               rewrite !eqE /=.
               apply/eqP => EQ; move: NEQ.
               by rewrite EQ (next_prev_hyperperiod_job_in_interval start j' START IN) eqxx.
    Qed.

    (** We can now build the matching execution of an entire hyperperiod,
        one decision at a time. Whenever a job runs, the lemma above gives
        us its matching successor in the next hyperperiod. Idle instants
        match as well: corresponding jobs have the same pending status,
        and work conservation makes the processor run whenever work is
        ready. Induction carries these two observations through the
        hyperperiod, establishing the reset contract. *)
    Lemma jlfp_respects_hyperperiod_reset :
      respects_hyperperiod_reset.
    Proof.
      move=> start START NCI elapsed; elim/ltn_ind: elapsed => elapsed IH LT.
      have REPEAT : forall delta, delta < elapsed -> execution_repeats_at (start + delta).
      { move=> delta BEFORE; apply: IH => //; exact: ltn_trans BEFORE LT. }
      rewrite /execution_repeats_at addnAC.
      case SCHED: (sched (start + elapsed)) => [j|].
      - apply/eqP; rewrite -scheduled_at_def.
        apply: jlfp_scheduled_job_repeats => //.
        by rewrite scheduled_at_def SCHED.
      - case NEXT: (sched (start + hyperperiod ts + elapsed)) => [j|] //.
        move/eqP: NEXT; rewrite -scheduled_at_def => NEXT.
        have IN : j \in arrivals_between arr_seq (start + hyperperiod ts)
            (start + 2 * hyperperiod ts).
        { rewrite mul2n -addnn addnA.
          apply: (pending_job_not_carried_in arr_seq _ sched _ _
            (start + hyperperiod ts + elapsed)) => //.
          - exact: NCI.2.
          - by rewrite leq_addr ltn_add2l. }
        suff : exists j', scheduled_at sched j' (start + elapsed).
        { by move=> [j']; rewrite scheduled_at_def SCHED. }
        apply: (H_work_conserving (prev_hyperperiod_job ts arr_seq j)).
        + apply: in_arrivals_implies_arrived.
          by apply: (prev_hyperperiod_job_in_prev_interval start).
        + rewrite /backlogged H_basic_readiness scheduled_at_def SCHED andbT
            -pending_repeats_in_hyperperiod //.
          * by apply: (prev_hyperperiod_job_in_prev_interval start).
          * rewrite (next_prev_hyperperiod_job_in_interval start j START IN).
            exact: scheduled_implies_pending.
    Qed.

    (** With the reset contract established, we can apply the finite
        deadline check from the preceding section to our JLFP schedule.
        The jobs arriving up to and including the simulation horizon
        serve as representatives whose deadline guarantees extend to
        every later arrival. *)
    Corollary jlfp_finite_deadline_check :
      deadlines_checked_through simulation_horizon ->
      all_deadlines_of_arrivals_met arr_seq sched.
    Proof.
      exact: finite_deadline_check jlfp_respects_hyperperiod_reset.
    Qed.

    (** Finally, we can express the same guarantee from the tasks' point of
        view. Since every arriving job meets its deadline, every task's releases
        meet their deadlines too. This connects our finite check to the usual
        notion of task-set schedulability. *)
    Corollary jlfp_taskset_schedulable :
      deadlines_checked_through simulation_horizon ->
      taskset_schedulable arr_seq sched ts.
    Proof.
      move=> CHECK tsk IN j ARR TSK.
      exact: jlfp_finite_deadline_check.
    Qed.

  End JLFP_RDS.

End SimulationInterval.

(** ** Applicability to EDF, FP, FIFO, GEL, and ELF *)

(** The corollary [jlfp_finite_deadline_check] applies to fully preemptive EDF,
    FP, FIFO, GEL, and ELF schedules with consistent tie-breaking. In
    particular:

    - The specialization [tiebreaking_edf_finite_deadline_check] in
      [prosa.results.periodic.simulation.edf] applies directly to EDF with
      task-ID and job-ID tie-breaking under [valid_task_ids] and
      [valid_job_ids].

    - Similarly, [tiebreaking_fp_finite_deadline_check] in
      [prosa.results.periodic.simulation.fp] applies to any task-level FP policy
      with task-ID and job-ID tie-breaking under [valid_task_ids],
      [valid_job_ids], and [monotonic_job_ids]. The latter constraint makes ties
      between jobs of the same task follow arrival order, preserving priorities
      across hyperperiods.

    - The specialization [tiebreaking_fifo_finite_deadline_check] in
      [prosa.results.periodic.simulation.fifo] likewise applies directly to FIFO
      with task-ID and job-ID tie-breaking under the same ID validity
      constraints as required by EDF.

    - Under the same assumptions, the specialization
      [tiebreaking_gel_finite_deadline_check] in
      [prosa.results.periodic.simulation.gel] also applies to GEL with
      task-derived priority points.

    - Finally, [tiebreaking_elf_finite_deadline_check] in
      [prosa.results.periodic.simulation.elf] applies to ELF over any task-level
      FP policy with task-derived priority points, again with tie-breaking based
      on task and job IDs.

     *)
