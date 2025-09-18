Require Export prosa.model.task.arrival.curves.
Require Export prosa.analysis.facts.completes_at.
Require Export prosa.analysis.facts.model.overheads.priority_bump.
Require Export prosa.analysis.facts.model.overheads.schedule_change.
Require Export prosa.analysis.facts.model.arrival_curves.

(** In this file, we prove upper bounds on the total number of
    schedule changes that can occur within a busy-interval prefix
    under FIFO, FP, and general JLFP scheduling policies. *)

(** * Number of Schedule Changes is Bounded by the Number of Arrivals *)

(** We begin by proving a set of helper lemmas that relate the number
    of schedule changes to the number of job arrivals within a given
    busy-interval prefix. *)
Section ScheduleChangesBoundedHelper.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any valid arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any explicit-overhead uni-processor schedule without
      superfluous preemptions. *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** Consider any valid preemption model. *)
  Context `{JobPreemptable Job}.
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Assume that the schedule respects the JLFP policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Consider any job [j] that has a positive job cost and is in the
      arrival sequence. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
  Variables t1 t2 : instant.
  Hypothesis H_busy_interval_prefix : busy_interval_prefix arr_seq sched j t1 t2.

  (** We define a helper predicate that holds if some job completes at time [t]. *)
  Let some_job_completes_at (t : instant) :=
    has (fun j_any => completes_at sched j_any t) (arrivals_up_to arr_seq t).

  (** To reason about the number of schedule changes, we first show
      that any change in the schedule at time [t] must be caused by
      either a priority bump or a job completion. *)
  Local Lemma schedule_change_caused_by_bump_or_completion :
    forall (t : instant),
      t > 0 ->
      t1 <= t < t2 ->
      schedule_change sched t ->
      priority_bump sched t || some_job_completes_at t.
  Proof.
    move=> t POS NEQ; rewrite /schedule_change => SC.
    have [j2 SCHED2]: exists j2, scheduled_job sched t = Some j2.
    { edestruct job_scheduled_in_busy_interval_prefix as [ja SCHED] => //.
      by exists ja; apply scheduled_at_iff_scheduled_job.
    }
    destruct (scheduled_job sched t.-1) as [j1 | ] eqn:SCHED1; last first.
    { by apply/orP; left; rewrite /priority_bump SCHED1 SCHED2. }
    have [COMPL | NCOMP] := boolP (completed_by sched j1 t).
    { apply/orP; right; apply/hasP; exists j1.
      { by apply scheduled_at_iff_scheduled_job in SCHED1; apply: arrivals_up_to_scheduled_at => //; lia. }
      { apply/andP; split => //.
        have ->: t == 0 = false by lia.
        by rewrite orbF; apply scheduled_implies_not_completed => //; apply scheduled_at_iff_scheduled_job.
      }
    }
    { apply/orP; left.
      rewrite /priority_bump SCHED1 SCHED2.
      apply: H_no_superfluous_preemptions; last by apply scheduled_at_iff_scheduled_job, SCHED2.
      apply/andP; split; [apply/andP; split | ]; [ by apply scheduled_at_iff_scheduled_job | by done | ].
      apply/negP => NSCHED1; apply scheduled_at_iff_scheduled_job in NSCHED1; rewrite NSCHED1 in SCHED2.
      inversion SCHED2; subst; rewrite NSCHED1 in SC.
      by inversion SC; rewrite eq_refl in SC.
    }
  Qed.

  (** As a simple corollary, the number of schedule changes in
      <<[t1.+1, t)>> is bounded by the number of time instants in that
      interval where either a priority bump occurs or some job
      completes.

      Note: The interval starts at [t1.+1] because we do not account
      for a schedule change at the very first instant of a busy
      interval. Even if such a change occurs, it is not relevant for
      our later analysis. *)
  Local Corollary schedule_changes_bounded_by_bumps_or_completions :
    forall (t : instant),
      t1 <= t <= t2 ->
      number_schedule_changes sched t1.+1 t
      <= size [seq to <- index_iota t1.+1 t | priority_bump sched to || some_job_completes_at to].
  Proof.
    intros; rewrite /number_schedule_changes !size_filter; apply sub_count_seq => x IN.
    by apply: schedule_change_caused_by_bump_or_completion => //; rewrite mem_index_iota in IN; lia.
  Qed.

  (** ** LP and HEP completions are bounded   *)

  (** We now turn to bounding the number of "causes" that could lead
      to schedule changes within a busy interval prefix. In
      particular, we consider two types of events: (i) priority bumps,
      and (ii) job completions. We show that the number of such events
      is also bounded. *)

  (** Let us first define the total number of low-priority job
      completions that occur during the interval [(t1, t2)]. Note that
      completions exactly at [t1] are ignored. *)
  Let lp_completions_during (t1 t2 : instant) :=
    \sum_(t1.+1 <= to < t2)
      \sum_(jlp <- arrivals_between arr_seq 0 t2 | ~~ hep_job jlp j)
        completes_at sched jlp to.

  (** Similarly, we define the number of higher-or-equal-priority job
      completions in the same interval. *)
  Let hep_completions_during (t1 t2 : instant) :=
    \sum_(t1.+1 <= t < t2)
      \sum_(jhp <- arrivals_between arr_seq t1 t2 | hep_job jhp j)
        completes_at sched jhp t.

  (** Let us fix a time instant [t] within the busy-interval prefix. *)
  Variable t : instant.
  Hypothesis H_t_in_busy_prefix : t1 < t <= t2.

  (** When a low-priority job completes, it necessarily triggers a
      priority bump. Hence, the number of low-priority completions is
      bounded by the number of instants in which both a priority bump
      and a job completion occur. *)
  Local Lemma lp_completions_bounded_by_prio_bumps_completions :
    lp_completions_during t1 t
    <= size [seq t <- index_iota t1.+1 t
           | priority_bump sched t & some_job_completes_at t].
  Proof.
    have IF : forall (b : bool), (if b then 1 else 0) = b by done.
    rewrite -!sum1_size !big_filter [leqLHS]big_mkcond [leqRHS]big_mkcond [leqLHS]big_seq [leqRHS]big_seq //=.
    apply leq_sum => to; rewrite mem_index_iota IF => NEQ.
    have [PI|NPI] := boolP (priority_inversion arr_seq sched j t1); last first.
    { apply leq_trans with 0; last by done.
      rewrite leqn0; apply/eqP; rewrite big_seq_cond; apply big1 => jlp2 /andP [ARR2 LP2].
      apply/eqP; rewrite eqb0; apply/negP => COMP.
      apply scheduled_at_precedes_completes_at in COMP; last by lia.
      rewrite [scheduled_at _ _ _ ]Bool.negb_involutive_reverse in COMP.
      move: COMP => /negP SCHED; apply: SCHED.
      by apply: lower_priority_jobs_never_scheduled_if_no_inversion => //; lia.
    }
    { move: (PI) => /andP [NINS /hasP [jlp INlp LP]]; rewrite scheduled_jobs_at_iff in INlp => //=.
      have [COMPL | NCOMP] := boolP (completes_at sched jlp to); last first.
      { apply leq_trans with 0; last by done.
        rewrite leqn0; apply/eqP.
        rewrite big_seq_cond; apply big1 => jl /andP [ARRl LPl].
        apply/eqP; rewrite eqb0; apply/negP => COMP.
        move: (COMP) => SCHED; apply scheduled_at_precedes_completes_at in SCHED; last by move: NEQ; clear; lia.
        have EQ : jl = jlp.
        { by apply: only_one_pi_job; (try exact BUSY) => //; (try move : NEQ H_t_in_busy_prefix; clear; lia). }
        by subst; rewrite COMP in NCOMP.
      }
      { apply leq_trans with 1; first by apply only_one_job_completes_at_a_time => //; lia.
        rewrite lt0b; apply/andP; split.
        { move: (COMPL) => SCHED.
          apply scheduled_at_precedes_completes_at, scheduled_at_iff_scheduled_job in SCHED; last by move: NEQ; clear; lia.
          rewrite /priority_bump SCHED.
          have [jh [SCHEDh HEPh]] : exists ja, scheduled_at sched ja to /\ hep_job ja j.
          { eapply completetion_time_is_preemption_time in COMPL => //.
            by edestruct not_quiet_implies_exists_scheduled_hp_job_after_preemption_point
              with (t1 := t1) (t2 := t2) (t := to) (tp := to) as [jhp [FF TT]] => //; [lia | lia | exists jhp; split; eapply TT].
          }
          apply scheduled_at_iff_scheduled_job in SCHEDh; rewrite SCHEDh; apply/negP => HEPlh.
          by move: LP  => /negP LP; apply: LP; apply: H_priority_is_transitive => //. }
        { by apply/hasP; exists jlp; [ apply: arrivals_up_to_scheduled_at => //; lia | ]. }
      }
    }
  Qed.

  (** Under FIFO scheduling, priorities are determined solely by
      arrival times. Since a job cannot complete before
      earlier-arriving jobs, no low-priority job can complete while
      any higher-priority job is incomplete. Hence, low-priority
      completions cannot occur. *)
  Local Lemma lp_completions_bounded_by_arrivals :
    policy_is_FIFO JLFP ->
    lp_completions_during t1 t = 0.
  Proof.
    move=> FIFO; unfold lp_completions_during.
    rewrite big_seq; apply big1 => to; rewrite mem_index_iota => NEQ.
    apply big1 => jlp LP.
    apply/eqP; rewrite eqb0; apply/negP => COMPL.
    rewrite FIFO -ltnNge in LP.
    move: (H_busy_interval_prefix) => [_ [_ [NQT _]]].
    move: (NQT t2.-1 ltac:(lia)); apply => jhp ARR HEP _.
    rewrite FIFO in HEP.
    have HEP2 : job_arrival jhp < job_arrival jlp; [ by lia | clear HEP LP].
    apply scheduled_at_precedes_completes_at in COMPL; last by lia.
    eapply completion_monotonic; last first.
    { apply: early_hep_job_is_scheduled => //.
      by intros ?; rewrite /JLFP_to_JLDP /hep_job_at !FIFO; lia. }
    { by lia. }
  Qed.

  (** A higher-or-equal-priority job can complete at most once. Thus,
      the number of higher-or-equal-priority completions is bounded by
      the number of such jobs that arrive during the busy-interval
      prefix. *)
  Local Lemma hep_completions_bounded_by_arrivals :
    hep_completions_during t1 t
    <= size [seq jhp <- arrivals_between arr_seq t1 t | hep_job jhp j].
  Proof.
    rewrite -!sum1_size !big_filter.
    rewrite /hep_completions_during exchange_big //=.
    rewrite [leqLHS]big_mkcond [leqRHS]big_mkcond //=.
    rewrite [leqLHS]big_seq [leqRHS]big_seq //=.
    apply leq_sum => jhp ARR.
    have [LP|HP] := boolP (hep_job jhp j) => //.
    by apply job_completes_at_most_once.
  Qed.

  (** * Bounding the number of schedule-change causes *)

  (** Every job completion must be either a higher-or-equal priority
      or lower-priority job. Thus, the total number of instants in
      which some job completes is bounded by the number of completions
      of LP and HEP jobs. *)
  Local Lemma some_job_completes_bound :
    size [seq to <- index_iota t1.+1 t | some_job_completes_at to]
    <= hep_completions_during t1 t + lp_completions_during t1 t.
  Proof.
    rewrite -!sum1_size !big_filter.
    apply leq_trans with (
        \sum_(to <- index_iota t1.+1 t)
         \sum_(jhp <- arrivals_between arr_seq 0 t | hep_job jhp j) completes_at sched jhp to
        + \sum_(to <- index_iota t1.+1 t)
           \sum_(jhp <- arrivals_between arr_seq 0 t | ~~ hep_job jhp j) completes_at sched jhp to
      ).
    { rewrite big_mkcond [leqLHS]big_seq -big_split //= [leqRHS]big_seq; apply leq_sum => //=.
      move=> to; rewrite mem_index_iota => NEQo.
      rewrite big_mkcond //= [in X in _ + X]big_mkcond //= -big_split //=.
      destruct (some_job_completes_at to) eqn:COM; last by done.
      move: COM => /hasP [jc IN COMP]; rewrite sum_nat_gt0; apply/hasP; exists jc.
      { by rewrite mem_filter //=; apply: arrivals_between_sub; [ | | apply IN]; lia. }
      { by destruct (hep_job _ _); rewrite COMP. }
    }
    rewrite leq_add2r big_nat_cond [leqRHS]big_nat_cond.
    apply leq_sum => to /andP [NEQo _].
    rewrite (arrivals_between_cat _ _ t1); try lia.
    rewrite big_cat //= -[leqRHS]add0n leq_add // leqn0; apply/eqP.
    rewrite big_seq_cond; apply big1 => jhp /andP [T1 T2].
    apply/eqP; rewrite eqb0.
    by erewrite no_early_hep_job_completes_during_busy_prefix => //; lia.
  Qed.

  (** Priority bumps can only be caused by newly arrived
      higher-or-equal priority jobs. Therefore, the number of time
      instants with a priority bump is bounded by the number of such
      jobs. *)
  Local Lemma priority_bumps_bounded_by_hep_arrivals :
    size [seq to <- index_iota t1.+1 t | priority_bump sched to]
    <= size [seq jhp <- arrivals_between arr_seq t1 t | hep_job jhp j].
  Proof.
    have IF : forall (b : bool), (if b then 1 else 0) = b by done.
    rewrite -!sum1_size !big_filter.
    apply leq_trans with (
        \sum_(to <- index_iota t1.+1 t | priority_bump sched to)
         \sum_(jhp <- arrivals_between arr_seq t1 t) scheduled_at sched jhp to).
    { rewrite big_mkcond [leqRHS]big_mkcond //= big_seq [leqRHS]big_seq //=; apply leq_sum.
      move=> to; rewrite mem_index_iota => NEQto.
      destruct (priority_bump sched to) eqn:PB => //; rewrite sum_nat_gt0.
      edestruct priority_bump_implies_hp_arrival_in_prefix as [jhp [SCHED ARR]]; last first.
      { by apply/hasP; exists jhp; [rewrite mem_filter | rewrite SCHED]. }
      all: try apply H_busy_interval_prefix; try apply PB; try done; lia.
    }
    { rewrite exchange_big [leqRHS]big_mkcond //= big_seq [leqRHS]big_seq //=.
      apply leq_sum => jhp ARR; rewrite IF.
      have [LP|HP] := boolP (hep_job jhp j); last first.
      { rewrite leqn0 big_nat_cond big1 // => to /andP [NEQto PB].
        by apply/eqP; rewrite eqb0; apply: lp_job_should_arrive_early_for_pi => //; lia.
      }
      { rewrite big_mkcond //=; move_neq_up GT; apply sum_ge_2_nat in GT; last first.
        { by intros; destruct priority_bump, (scheduled_at sched) => //. }
        destruct GT as [to1 [to2 [LE1 [LE2 [LE3 [EQ1 EQ2]]]]]].
        destruct (priority_bump sched to1), (scheduled_at sched jhp to1) eqn:SCHED1,
            (priority_bump sched to2) eqn:PB, (scheduled_at sched jhp to2) eqn:SCHED2 => //.
        clear EQ1 EQ2; move: PB; apply scheduled_at_iff_scheduled_job in SCHED2; rewrite /priority_bump SCHED2.
        have [jo SCHEDo] : exists jo, scheduled_at sched jo to2.-1
            by apply: job_scheduled_in_busy_interval_prefix => //=; lia.
        apply scheduled_at_iff_scheduled_job in SCHEDo; rewrite SCHEDo => /negP HEP; apply: HEP.
        apply scheduled_at_iff_scheduled_job in SCHEDo.
        eapply priority_higher_than_pending_job_priority with (t1 := to1) (t2 := to2) (t := to2.-1) => //.
        { by apply scheduled_at_iff_scheduled_job in SCHED2. }
        { intros; rewrite /job_ready //=; apply/andP; split.
          - rewrite /has_arrived; eapply has_arrived_scheduled in SCHED1 => //.
            by rewrite /has_arrived in SCHED1; lia.
          - clear SCHEDo SCHED1; apply scheduled_at_iff_scheduled_job in SCHED2.
            by eapply incompletion_monotonic; [ | apply scheduled_implies_not_completed => //]; lia.
        }
        { lia. }
      }
    }
  Qed.

  (** In the special case of FIFO priority policy, no priority bump
      can occur within the interval. *)
  Local Lemma no_priority_bumps_under_fifo :
    policy_is_FIFO JLFP ->
    size [seq to <- index_iota t1.+1 t | priority_bump sched to] = 0.
  Proof.
    move=> FIFO; apply/eqP; rewrite -leqn0; move_neq_up POS.
    move: POS; rewrite -has_predT => /hasP [pb]; rewrite mem_filter => /andP [PB IN] _.
    move: IN; rewrite mem_index_iota => IN.
    eapply no_priority_bumps_in_fifo with (t := pb) in FIFO => //; last by lia.
    by erewrite PB in FIFO.
  Qed.

  (** ** Putting bounds together *)

  (** The number of instants with either a priority bump or a job
      completion is at most twice the number of jobs that have
      higher-or-equal priority than [j] and arrive in <<[t1, t)>>.

      Intuitively, each such job may trigger at most one priority bump
      and complete once, and these are the only events that can appear
      in the considered set. *)
  Local Lemma bumps_and_completions_bounded_by_hep_arrivals :
    size [seq to <- index_iota t1.+1 t | priority_bump sched to || some_job_completes_at to]
    <= 2 * size [seq jhp <- arrivals_between arr_seq t1 t | hep_job jhp j].
  Proof.
    rewrite !size_filter; apply: leq_trans.
    { by rewrite count_predUI'; apply leqnn. }
    { rewrite -[2]addn1 mulnDl mul1n -addnBA; last first.
      { by apply sub_count_seq => to _ /andP [_ B]; apply: B. }
      rewrite -!size_filter.
      apply leq_add; first by apply: priority_bumps_bounded_by_hep_arrivals.
      rewrite leq_subLR; apply: leq_trans.
      { apply: some_job_completes_bound; try done. }
      { rewrite addnC; apply leq_add.
        { by apply: lp_completions_bounded_by_prio_bumps_completions. }
        { by apply: hep_completions_bounded_by_arrivals. }
      }
    }
  Qed.

  (** Under FIFO scheduling, the number of instants with either a
      priority bump or a job completion is at most the number of
      higher-or-equal priority jobs (i.e., earlier or equal arrival
      time) in <<[t1, t)>>.

      This is because, under FIFO, priority bumps cannot occur, and
      each such job may complete at most once. *)
  Local Lemma bumps_and_completions_bounded_by_hep_arrivals_fifo :
    policy_is_FIFO JLFP ->
    size [seq to <- index_iota t1.+1 t | priority_bump sched to || some_job_completes_at to]
    <= size [seq jhp <- arrivals_between arr_seq t1 t | hep_job jhp j].
  Proof.
    move=> FIFO; apply: leq_trans.
    { by rewrite !size_filter count_predUI'; apply leqnn. }
    apply: leq_trans; first by apply leq_subr.
    rewrite -[leqRHS]add0n leq_add //.
    { by rewrite -size_filter no_priority_bumps_under_fifo. }
    rewrite -!size_filter.
    eapply leq_trans; first apply some_job_completes_bound.
    eapply leq_trans.
    { apply leq_add; first by apply hep_completions_bounded_by_arrivals.
      by rewrite lp_completions_bounded_by_arrivals; [ apply leqnn | ].
    }
    lia.
  Qed.

End ScheduleChangesBoundedHelper.

(** * Number of schedule changes is bounded *)

(** In this section, we prove that the number of schedule changes in a
    busy-interval prefix is bounded under JLFP scheduling. *)
Section JLFP.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any valid arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any explicit-overhead uni-processor schedule without
      superfluous preemptions of this arrival sequence. *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** Assume that the schedule respects the JLFP policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Assume that the preemption model is valid. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Consider any job [j] that has a positive job cost and is in the
      arrival sequence. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
  Variables t1 t2 : instant.
  Hypothesis H_busy_interval_prefix : busy_interval_prefix arr_seq sched j t1 t2.

  (** Next, consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{MaxArrivals Task}.
  Context `{JobTask Job Task}.

  (** ... and an arbitrary task set [ts]. *)
  Variable ts : seq Task.

  (** Assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of arrival curves that
      constrains the arrival sequence [arr_seq]. *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Consider an interval <<[t1, t1 + Δ) ⊆ [t1, t2)>>. *)
  Variable Δ : duration.
  Hypothesis H_subinterval : t1 + Δ <= t2.

  (** The number of schedule changes in the interval <<[t1 + 1, t1 + Δ)>>
      is bounded by twice the total number of job arrivals across
      all tasks during [Δ].

      The factor of 2 arises because each arriving job can cause at
      most one job completion and one priority bump. *)
  Lemma schedule_changes_bounded_by_total_arrivals_JLFP :
    number_schedule_changes sched t1.+1 (t1 + Δ)
    <= 2 * \sum_(tsk <- ts) max_arrivals tsk Δ.
  Proof.
    have [LT|LE] := leqP Δ 1.
    { rewrite /number_schedule_changes.
      destruct Δ as [ | [ | δ]]; last by done.
      - by rewrite /index_iota addn0 subnS subnn //=.
      - by rewrite /index_iota addn1 subnn //=.
    }
    apply: leq_trans.
    { by apply: schedule_changes_bounded_by_bumps_or_completions => //; lia. }
    { apply: leq_trans.
      - by apply: bumps_and_completions_bounded_by_hep_arrivals => //; lia.
      - by rewrite leq_mul2l; apply jlfp_hep_arrivals_bounded_by_sum_max_arrivals => //.
    }
  Qed.

End JLFP.

(** In this section, we prove that the number of schedule changes in a
    busy-interval prefix is bounded under FP scheduling. *)
Section FP.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{MaxArrivals Task}.
  Context `{FP : FP_policy Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider an FP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.
  Hypothesis H_priority_is_transitive : transitive_task_priorities FP.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any valid arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any explicit-overhead uni-processor schedule without
      superfluous preemptions of this arrival sequence. *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** Assume that the schedule respects the FP policy. *)
  Hypothesis H_respects_policy :
    respects_FP_policy_at_preemption_point arr_seq sched FP.

  (** Assume that the preemption model is valid. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Consider any job [j] that has a positive job cost and is in the
      arrival sequence. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
  Variables t1 t2 : instant.
  Hypothesis H_busy_interval_prefix : busy_interval_prefix arr_seq sched j t1 t2.

  (** Next, we consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of arrival curves that
      constrains the arrival sequence [arr_seq]. *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Consider an interval <<[t1, t1 + Δ) ⊆ [t1, t2)>>. *)
  Variable Δ : duration.
  Hypothesis H_subinterval : t1 + Δ <= t2.

  (** Under FP scheduling, we bound the number of schedule changes in
      <<[t1 + 1, t1 + Δ)>> by twice the number of arrivals of tasks
      with priority higher than or equal to the task of job [j].

      As before, each arrival may lead to at most one priority bump
      and one completion. Furthermore, tasks with lower priority
      cannot initiate a schedule change. *)
  Lemma schedule_changes_bounded_by_total_arrivals_FP :
    number_schedule_changes sched t1.+1 (t1 + Δ)
    <= 2 * \sum_(tsk <- ts | hep_task tsk (job_task j)) max_arrivals tsk Δ.
  Proof.
    have [LT|LE] := leqP Δ 1.
    { rewrite /number_schedule_changes.
      destruct Δ as [ | [ | δ]]; last by done.
      - by rewrite /index_iota addn0 subnS subnn //=.
      - by rewrite /index_iota addn1 subnn //=.
    }
    apply: leq_trans.
    { by apply: schedule_changes_bounded_by_bumps_or_completions => //; lia. }
    { apply: leq_trans.
      - by apply: bumps_and_completions_bounded_by_hep_arrivals => //; lia.
      - by rewrite leq_mul2l; apply fp_hep_arrivals_bounded_by_sum_max_arrivals => //.
    }
  Qed.

End FP.

(** In this section, we prove that the number of schedule changes in a
    busy-interval prefix is bounded under FIFO scheduling. *)
Section FIFO.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider a FIFO priority policy that indicates a higher-or-equal
      priority relation. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_FIFO : policy_is_FIFO JLFP.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any valid arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any explicit-overhead uni-processor schedule without
      superfluous preemptions of this arrival sequence. *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** Assume that the schedule respects the JLFP (i.e., FIFO) policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Assume that the preemption model is valid. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Consider any job [j] that has a positive job cost and is in the
      arrival sequence. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job [j]. *)
  Variables t1 t2 : instant.
  Hypothesis H_busy_interval_prefix : busy_interval_prefix arr_seq sched j t1 t2.

  (** Next, consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{MaxArrivals Task}.
  Context `{JobTask Job Task}.

  (** ... and an arbitrary task set [ts]. *)
  Variable ts : seq Task.

  (** Assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that [max_arrivals] is a family of arrival curves that
      constrains the arrival sequence [arr_seq]. *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Consider an interval <<[t1, t1 + Δ) ⊆ [t1, t2)>>. *)
  Variable Δ : duration.
  Hypothesis H_subinterval : t1 + Δ <= t2.

  (** Under FIFO scheduling, no priority bumps can occur. Thus, the
      number of schedule changes in <<[t1 + 1, t1 + Δ)>> is at most
      the number of job arrivals during an interval of length [Δ]. *)
  Lemma schedule_changes_bounded_by_total_arrivals_FIFO :
    number_schedule_changes sched t1.+1 (t1 + Δ)
    <= \sum_(tsk <- ts) max_arrivals tsk Δ.
  Proof.
    have [LT|LE] := leqP Δ 1.
    { rewrite /number_schedule_changes.
      destruct Δ as [ | [ | δ]]; last by done.
      - by rewrite /index_iota addn0 subnS subnn //=.
      - by rewrite /index_iota addn1 subnn //=.
    }
    have REFL : reflexive_job_priorities JLFP.
    { by move=> ?; rewrite H_FIFO; lia. }
    have TRNS : transitive_job_priorities JLFP.
    { by move => ? ? ?; rewrite !H_FIFO; lia. }
    apply: leq_trans.
    { by apply: schedule_changes_bounded_by_bumps_or_completions => //; lia. }
    { apply: leq_trans.
      - by apply: bumps_and_completions_bounded_by_hep_arrivals_fifo => //; lia.
      - by apply jlfp_hep_arrivals_bounded_by_sum_max_arrivals => //.
    }
  Qed.

End FIFO.
