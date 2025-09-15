(** * Transfer Schedulability for Ideal Uniprocessors *)

(** This module provides the mechanized result from the following paper:

    - Willemsen et al., “Transfer Schedulability in Periodic Real-Time Systems”,
      EMSOFT 2025 / ACM TECS, 2025.
      #<br><a href="https://doi.org/10.1145/3763236">DOI: 10.1145/3763236</a># *)

(** ** Overview and Dependencies *)

(** Transfer schedulability is a concept that allows mimicking the behavior of
    some reference schedule in an online schedule such that no job finishes
    later in the online schedule than in the reference schedule. In this
    development, we define the exact transfer schedulability criterion and prove
    two sufficient conditions and one necessary condition. In particular, we are
    concerned solely with _the conditions under which such a schedulability
    transfer is guaranteed_. We do not concern ourselves with any particular
    mechanism for accomplishing such a transfer at runtime. *)


(** The following line imports Prosa's utility library, which in turn pulls in
    the SSReflect tactics language that we use to construct proofs. *)

Require Export prosa.util.all.

(** We build on Prosa's central modeling definitions and many auxiliary lemmas. *)

Require Export prosa.analysis.facts.model.service_of_jobs.
Require Export prosa.analysis.definitions.schedulability.

(** In particular, we restrict our focus exclusively to ideal uniprocessor
    schedules in the following. *)

Require Export prosa.analysis.facts.model.ideal.schedule.
Require Export prosa.analysis.facts.model.uniprocessor.


(** ** System Model *)

(** We are now ready to introduce the general system model upon which our
    analysis rests. *)

Section TransferSchedulability.

  (** We consider jobs that are characterized by arrival times and deadlines. No
      assumptions are made on how jobs relate (or whether they do so at all) and
      on how deadlines relate to arrival times. (We do not consider any "task"
      concept in this file.) *)

  Context {Job : JobType} `{JobArrival Job} `{JobDeadline Job}.

  (** As already mentioned, we consider ideal uniprocessor schedules. To this
      end, let us recall Prosa's existing definition of this common assumption.
      (For convenience and to match Prosa convention, we will refer to the ideal
      uniprocessor state simply as [PState].) *)

  #[local] Existing Instance ideal.processor_state.
  Let PState := ideal.processor_state Job.

  (** Next, we introduce the two key elements of the model. First, assume we are
      given a _reference schedule_, called [ref_sched] in the following. This is
      the schedule that we assume is being emulated. *)

  Variable ref_sched : schedule PState.

  (** Second, we consider a second _online schedule_ called [online_sched],
      which is the schedule to which schedulability is supposed to be
      transferred. *)

  Variable online_sched : schedule PState.

  (** We need to consider two different job costs: the one _planned for_ in the
      reference schedule, called [ref_job_cost], and the one _actually
      exhibited_ in the online schedule, called [online_job_cost]. *)

  Variable ref_job_cost online_job_cost : JobCost Job.

  (** When we say that a job is complete in the reference schedule, it is a
      statement w.r.t. the reference cost [job_cost_ref]. Conversely, when we
      say that a job is complete in the online schedule, it is a statement
      w.r.t. the online cost [job_cost_online]. For ease of reference, we define
      respective local abbreviations.

      Syntax hint: The "@" notation allows us to explicitly specify parameters
      that are usually implicitly inferred, such as the job-cost parameter in
      our case here. *)

  Let ref_completed_by := (@completed_by _ _ ref_sched ref_job_cost).
  Let online_completed_by := (@completed_by _ _ online_sched online_job_cost).

  (** ** Well-Formedness of the Schedules *)

  (** In order to prove the desired results, we need to place some mild
      assumptions on the reference and online schedules. The following
      hypotheses express these well-formedness requirements. *)

  (** First of all, we assume that the (possibly infinite) set of jobs to be
      scheduled is characterized by the arrival sequence, called [arr_seq],
      which is a standard modeling element in Prosa.

      Note that [arr_seq] is a section variable and hence implicitly
      ∀-quantified. The results established in this file thus hold w.r.t. _any_
      arrival sequence (in which each job arrives at most once). *)

  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Next, we require that the reference schedule indeed contains only jobs
      that arrive in the system. *)

  Hypothesis H_jobs_arr_ref : jobs_come_from_arrival_sequence ref_sched arr_seq.

  (** Additionally, we require the reference schedule to be well-formed: any job
      that executes must have arrived and not yet completed. *)

  Hypothesis H_jobs_must_arrive_ref : jobs_must_arrive_to_execute ref_sched.
  Hypothesis H_jobs_exec_ref : (@completed_jobs_dont_execute _ _ ref_sched ref_job_cost).

  (** Finally, we also require that completed jobs don't execute past their
      completion in the online schedule. *)

  Hypothesis H_jobs_exec_on : (@completed_jobs_dont_execute _ _ online_sched online_job_cost).


  (** * Definition of Schedulability Transfer *)

  (** By "transfer schedulability", we refer to the property that no job
      finishes later in the online schedule than in the reference schedule. That
      is, _if_ a job [j] is finished at a given time [t] in the reference
      schedule, _then_ the same job is also finished at time [t] in the online
      schedule. *)

  Definition schedulability_transferred :=
    forall j t,
      ref_completed_by j t -> online_completed_by j t.

  (** As a corollary, we next observe that this notion trivially extends to
      deadlines. As before, we need to be careful to refer to the appropriate
      job-cost parameter. *)

  Let ref_job_meets_deadline :=  (@job_meets_deadline _ _ ref_sched ref_job_cost _).
  Let online_job_meets_deadline := (@job_meets_deadline _ _ online_sched online_job_cost _).

  (** We can now re-state the schedulability-transfer property in terms of job
      deadlines: Assuming that the [schedulability_transferred] property holds,
      a job meets its deadline in the online schedule if it meets its deadline
      in the reference schedule. *)

  Corollary deadlines_met :
    schedulability_transferred ->
    (forall j, ref_job_meets_deadline j -> online_job_meets_deadline j).
  Proof. move=> TRANS j MET; by apply: TRANS. Qed.


  (** * Setup for the Generic Argument *)

  (** We are now ready to start establishing the desired results. Since we want
      to prove two variants of the sufficiency condition, one for
      [online_job_cost] and one for [ref_job_cost], we are abstracting in the
      following from the specific job-cost parameter. *)

  Section ParametericCostBound.

    (** Let [job_cost_bound] denote an upper bound on the cost of each job in
        [online_sched]. Below, we are going to instantiate [job_cost_bound] once
        as [online_job_cost] and once as [ref_job_cost], but technically it
        could be any bound in between the two extremes. *)

    Variable job_cost_bound : JobCost Job.

    (** We require that [job_cost_bound] indeed upper-bounds the online cost of
        any job. *)

    Hypothesis H_job_cost_bounded :
      forall j,
        online_job_cost j <= job_cost_bound j.

    (** Conversely, we require that the reference cost [ref_job_cost]
        upper-bounds the [job_cost_bound] used in this section. *)

    Hypothesis H_ref_cost_dominates :
      forall j,
        job_cost_bound j <= ref_job_cost j.

    (** As a trivial corollary, by transitivity the reference cost also bounds
        the online cost. *)

    Corollary ref_cost_bounds_online_cost :
      forall j,
        online_job_cost j <= ref_job_cost j.
    Proof.
      move=> j.
      apply: (leq_trans (H_job_cost_bounded j)).
      exact: H_ref_cost_dominates.
    Qed.

    (** ** The Remaining Job-Cost Bound *)

    (** We next introduce one of the central elements of the proof: the
        _remaining job-cost bound_, which for a given job [j] and given time [t]
        relates the amount of service received by [j] up to time [t] in the
        online schedule to the generic upper bound given by [job_cost_bound]. *)

    Definition remaining_cost_bound j t :=
      (job_cost_bound j) - (service online_sched j t).

    (** As the proofs must reason about [remaining_cost_bound] quite a bit, we
        require a few auxiliary lemmas related to this definition, which we
        introduce below. Most of these are common-sense facts that will be
        obvious to a human reader. *)

    (** *** Basic Facts About the Remaining Job-Cost Bound *)

    (** The remaining job-cost bound at a given time [t] can be split into the
        remaining cost at the next point in time [t.+1] and the service received
        at time [t] itself. *)

    Lemma remcost_service :
      forall j t,
        remaining_cost_bound j t = remaining_cost_bound j t.+1 + service_at online_sched j t.
    Proof.
      move=> j t.
      have := H_job_cost_bounded j.
      have : service online_sched j t.+1 <= online_job_cost j by apply: service_at_most_cost.
      by rewrite /remaining_cost_bound -!service_last_plus_before; lia.
    Qed.

    (** We can trivially lift the preceding fact to entire intervals. *)

    Lemma remcost_service_during :
      forall j t1 t2,
        t1 <= t2 ->
        remaining_cost_bound j t1 = remaining_cost_bound j t2 + service_during online_sched j t1 t2.
    Proof.
      move=> j t1 t2 LEQ.
      have := H_job_cost_bounded j.
      have : service online_sched j t2 <= online_job_cost j by apply: service_at_most_cost.
      rewrite /remaining_cost_bound.
      by rewrite -(service_cat _ _ t1) //; lia.
    Qed.

    (** Furthermore, we can lift the preceding whole-interval observation to
        arbitrary sets of jobs.

        Notation hint: [xpredT] is the trivial dummy predicate that is always
        true, i.e., no jobs are being filtered here. *)

    Lemma remcost_total_service_during :
      forall (js : seq Job) t1 t2,
        t1 <= t2 ->
        \sum_(j <- js) remaining_cost_bound j t1
        = (\sum_(j <- js) remaining_cost_bound j t2)
          + service_of_jobs online_sched xpredT js t1 t2.
    Proof.
      move=> js t1 t2 LEQ.
      rewrite /service_of_jobs.
      rewrite -[RHS]big_split_idem //=.
      apply: eq_bigr => j _.
      exact: remcost_service_during.
    Qed.

    (** If we further know that, at each point in the interval, some job in the
        set of jobs under consideration is scheduled, then we can relate the
        remaining job-cost bound to the interval length.

        This is a crucial reasoning step, as it allows us to conclude that the
        remaining cost must be zero at time [t2] if the interval length equals
        the total remaining cost (as it will in our proof below).

        Notation hint: [uniq js] means that [js] is indeed a set, i.e.,
        technically a list without repetitions. *)

    Lemma remaining_cost_invariant :
      forall (js : seq Job) t1 t2,
        t1 <= t2 ->
        uniq js ->
        (forall t, t1 <= t < t2 -> exists j, (j \in js) && scheduled_at online_sched j t) ->
        \sum_(j <- js) remaining_cost_bound j t1
        = (\sum_(j <- js) remaining_cost_bound j t2) + (t2 - t1).
    Proof.
      move=> js t1 t2 LEQ UNIQ SCHED.
      suff <-: service_of_jobs online_sched xpredT js t1 t2 = t2 - t1 by apply: remcost_total_service_during.
      apply: service_of_jobs_always_scheduled => // t RANGE.
      have [j /andP[IN SCHED']] := SCHED t RANGE.
      by exists j; repeat split.
    Qed.

    (** *** Relation to the Remaining Online Cost *)

    (** As the purpose of the remaining job-cost bound is to upper-bound the
        leftover runtime of jobs in the online schedule, we introduce a few
        auxiliary lemmas relating the (true) remaining online cost to the
        (over-approximating) job-cost bound. *)

    (** As before, we introduce an intuitive alias to succinctly refer to the
        remaining online cost. The definition used here, [remaining_cost], is a
        standard Prosa construct. *)

    Let online_remaining_cost := (@remaining_cost _ _ online_sched online_job_cost).

    (** As intended, the remaining job-cost bound indeed upper-bounds the
        remaining online cost. *)

    Lemma online_remaining_cost_bounded :
      forall j t,
        online_remaining_cost j t <= remaining_cost_bound j t.
    Proof.
      move=> j t.
      rewrite leq_sub2rE //.
      apply: (@leq_trans (online_job_cost j)) => //.
      by apply: service_at_most_cost.
    Qed.

    (** Furthermore, the remaining job-cost bound of any incomplete job is
        necessarily positive. *)

    Lemma remaining_cost_positive :
      forall j t,
        ~~ online_completed_by j t ->
        remaining_cost_bound j t > 0.
    Proof.
      move=> j t.
      rewrite incomplete_is_positive_remaining_cost.
      rewrite /remaining_cost/remaining_cost_bound/job_cost.
      rewrite !subn_gt0 => LT.
      by apply: (leq_trans LT).
    Qed.

    (** Conversely, if the total remaining job-cost bound of a set of jobs hits
        zero, then every job in the set is necessarily complete. *)

    Lemma remaining_cost_zero :
      forall (js : seq Job) t,
        \sum_(j <- js) remaining_cost_bound j t == 0 ->
        forall j,
          j \in js ->
          online_completed_by j t.
    Proof.
      move=> js t ZERO j IN.
      apply: contraT.
      rewrite incomplete_is_positive_remaining_cost.
      suff: online_remaining_cost j t == 0 by rewrite /online_remaining_cost; lia.
      have REM0: remaining_cost_bound j t == 0.
      { move: ZERO.
        rewrite sum_nat_eq0_nat => /allP; apply.
        by rewrite mem_filter; apply/andP; split. }
      have := online_remaining_cost_bounded j t.
      by lia.
    Qed.

    (** ** The Set of Critical Jobs *)

    (** The second major element in the proof is the notion of the set of
        _critical jobs_ at a given time [t1] w.r.t. to a _reference time_ [t2].
        Intuitively, the critical jobs are those that must be scheduled
        immediately in order to avoid a deadline miss. *)


    (** Technically, based on the arrival sequence [arr_seq], given an interval
        <<[t1, t2)>>, we define the set of critical jobs to be those that

        - are _not_ finished at time [t1] in the _online_ schedule and

        - _are_ finished in the _reference_ schedule at time [t2].

        Notation hint: [ [seq j <- some_sequence | filter_predicate_on j ] ] is
        MathComp's notation for a list comprehension, similarly to those
        encountered in for instance Haskell or Python. *)

    Definition critical_jobs t1 t2 :=
      [seq j <- arrivals_up_to arr_seq t2 |
        ref_completed_by j t2
        && ~~ online_completed_by j t1].


    (** *** Basic Facts About the Set of Critical Jobs *)

    (** To reason about critical jobs, we establish a number of facts about them
        that will be fairly obvious to a human reader. *)

    (** To begin with, if a job is critical at a time [t2] w.r.t. a reference
        time [t3], then it is also critical at any earlier time [t1] w.r.t. the
        same reference time. *)

    Lemma critical_jobs_monotonicity :
      forall t1 t2 t3,
        t1 <= t2 <= t3 ->
        forall j,
          j \in critical_jobs t2 t3 ->
          j \in critical_jobs t1 t3.
    Proof.
      move=> t1 t2 t3 /andP[LEQ12 LEQ23] j.
      rewrite !mem_filter => /andP[ /andP[COMP NCOMP] IN].
      repeat (apply/andP; split => //).
      by apply: incompletion_monotonic; first exact: LEQ12.
    Qed.

    (** If a job is critical at a time [t1] w.r.t. a reference time [t3] and no
        longer critical at a later time [t2] (w.r.t. the same reference time),
        then it must have completed in the meantime. *)

    Lemma critical_jobs_dropout :
      forall t1 t2 t3,
        t1 <= t2 <= t3 ->
        forall j,
          j \in critical_jobs t1 t3 ->
          j \notin critical_jobs t2 t3 ->
          online_completed_by j t2.
    Proof.
      move=> t1 t2 t3 /andP[LEQ12 LEQ23] j.
      rewrite !mem_filter  => /andP[ /andP[COMP NCOMP1] IN].
      by rewrite COMP IN andbT andTb => /negPn.
    Qed.

    (** We can thus express the set of critical jobs at a time [t2] w.r.t. a
        reference time [t3] as the set of critical jobs at an earlier time [t1]
        (w.r.t. the same reference time) by filtering out all jobs that
        completed in the meantime. *)

    Lemma critical_jobs_filter_complete :
      forall t1 t2 t3,
        t1 <= t2 ->
        critical_jobs t2 t3 =
          [seq j <- critical_jobs t1 t3 | ~~ online_completed_by j t2].
    Proof.
      move=> t1 t2 t3 LEQ.
      rewrite -filter_predI.
      apply: eq_filter => j /=.
      case: (ref_completed_by j t3);
        case ON2: (online_completed_by j t2) => //=.
      case ON1: (online_completed_by j t1) => //.
      exfalso.
      suff: online_completed_by j t2 => //.
      by apply: completion_monotonic; [exact LEQ|exact ON1].
    Qed.

    (** Since the set of jobs is defined in terms of the arrival sequence (in
        which each job arrives at most once), the set of critical jobs is indeed
        a proper set (that is represented as a sequence without repeated
        elements). *)

    Lemma critical_jobs_uniq :
      forall t1 t2,
        uniq (critical_jobs t1 t2).
    Proof.
      move=> t1 t2.
      by apply/filter_uniq/arrivals_uniq.
    Qed.

    (** We observe that the generic job-cost bound implies a lower bound on the
        earliest-possible completion time of any critical jobs at time zero.

        This lemma may appear somewhat contrived at first sight, but represents
        an important reasoning step to rule out a corner case at time zero. *)

    Lemma critical_jobs_min_completion_time :
      forall t,
        t >= \sum_(j <- critical_jobs 0 t) job_cost_bound j.
    Proof.
      move=> t.
      apply: leq_trans;
        first by apply: leq_sum => j _; exact: H_ref_cost_dominates.
      have ->: \sum_(j <- critical_jobs 0 t) ref_job_cost j
               = \sum_(j <- critical_jobs 0 t) service_during ref_sched j 0 t.
      { rewrite big_seq [RHS]big_seq.
        apply: eq_bigr => j.
        rewrite mem_filter =>  /andP[ /andP[COMP NCOMP] IN].
        apply/eqP; rewrite eqn_leq.
        apply/andP; split => //.
        by apply: service_at_most_cost. }
      rewrite -/(service_of_jobs ref_sched xpredT _ 0 t).
      rewrite -[leqRHS]subn0.
      apply: service_of_jobs_le_length_of_interval' => //.
      exact: critical_jobs_uniq.
    Qed.

    (** Finally, we observe that the total remaining job-cost bound of a set of
        critical jobs is monotonically decreasing. *)

    Lemma critical_jobs_remaining_cost_monotonic :
      forall t1 t2 t3,
        t1 <= t2 <= t3 ->
        \sum_(j <- critical_jobs t1 t3) remaining_cost_bound j t1
        >= \sum_(j <- critical_jobs t2 t3) remaining_cost_bound j t2.
    Proof.
      move=> t1 t2 t3 /andP[LEQ12 LEQ23].
      apply: leq_trans; last first.
      { apply: (leq_sum_subseq _ (critical_jobs t2 t3)).
        rewrite subseq_filter //; apply/andP; split; last exact: filter_subseq.
        apply/allP => j.
        rewrite mem_filter => /andP[ /andP[COMP NCOMP] IN].
        repeat (apply/andP; split => //).
        by apply: incompletion_monotonic; first exact: LEQ12. }
      { apply: leq_sum => j _.
        rewrite leq_sub2lE.
        - exact: service_monotonic.
        - apply: (@leq_trans (online_job_cost j)) => //.
          exact: service_at_most_cost. }
    Qed.


    (** ** Definition of Slackless Intervals *)

    (** The third and final major element of the proof is the concept of
        "slackless intervals," which we define next. Slackless intervals tie
        together the remaining job-cost bound and the notion of critical jobs. *)

    (** In the definition of a "slackless interval," the "slack" is computed
        based on the generic job-cost bound, since the online job cost is
        assumed to be unknown until after the job's completion (i.e., we seek to
        support also the non-clairvoyant setting). More precisely, we call a
        _non-empty_ interval <<[t1, t2)>> _slackless_ if the total remaining
        job-cost bound of the critical jobs at time [t1] (w.r.t. reference time
        [t2]) is exactly equal to the interval length [t2 - t1]. *)

    Definition slackless_interval t1 t2 :=
      (t1 < t2)
      && \sum_(j <- critical_jobs t1 t2) remaining_cost_bound j t1 == t2 - t1.

    (** In fact, in our proof we require a stronger notion of slackless
        intervals: slackless intervals without "holes." To this end, we call an
        interval <<[t1, t2)>> _contiguously slackless_ if <<[t1, t2)>> is
        slackless (and hence non-empty) and every suffix interval ending at [t2]
        is also slackless.

        Notation hints:

        - The notation ['I_(t2 - t1)] is MathComp's notation for a bounded
          natural number, i.e., for the set {0, 1, 2, ..., [t2 - t1 - 1]}.

        - The notation [ [forall delta, some_predicate_on delta ] ] is
          conceptually the same as the standard
          [(forall delta, some_property_on delta)], but defined on a finite type
          and hence in [bool] and not [Prop], and therefore computable (which
          we'll need).

        Technical comment: the definition is slightly redundant, because the
        ∀-quantified part covers also <<[t1, t2)>>, but by requiring
        [slackless_interval t1 t2] explicitly we avoid having to deal with empty
        intervals. *)

    Definition contiguously_slackless_interval t1 t2 :=
      slackless_interval t1 t2
      && [forall delta : 'I_(t2 - t1), slackless_interval (t1 + delta) t2].

    (** We are now ready to state the main property: To guarantee the transfer
        of schedulability, we define the following property, which forces
        critical jobs to be scheduled at the beginning of slackless intervals. *)

    (** * The Schedulability Transfer Criterion *)

    (** The condition [schedulability_transferred] --- no job finishes later in
        the online schedule than in the reference schedule --- is simple and
        intuitive, but has one major downside: it can only be checked _after the
        fact_, that is, whether a schedule satisfies it becomes apparent only
        when it's already too late to do anything about a possible deadline
        violation. *)

    (** We therefore next introduce a definition _equivalent_ to
        [schedulability_transferred] that can be checked _before_ reaching a
        job's deadline, namely at the beginning of a slackless interval in which
        it is part of the critical jobs.

        In short, the criterion requires that a critical job is scheduled at the
        beginning of any slackless interval in the online schedule. Establishing
        that this definition is indeed equivalent to
        [schedulability_transferred] is the overall proof objective of this
        file. *)

    Definition transfer_schedulability_criterion :=
      forall t1 t2,
        slackless_interval t1 t2 ->
        exists j,
          scheduled_at online_sched j t1
          && (j \in critical_jobs t1 t2).

    (** In the remainder of this section, we assume the criterion to be
        satisfied. *)

    Hypothesis H_ts_criterion : transfer_schedulability_criterion.

    (** The main proof establishing that [transfer_schedulability_criterion] is
        a sufficient condition for [schedulability_transferred] consists of
        three steps that lead to contradiction:

        - First, assume that some job [j] finishes later in the online schedule
          than in the reference schedule, and let [t2] denote a time such that
          [j] is complete in the reference schedule and incomplete in the online
          schedule.

        - Second, we establish there exists a preceding contiguously slackless
          interval <<[t1, t2)>> and that [j] is a critical job at time [t1]
          w.r.t. reference time [t2].

        - Third, we establish that any job that is critical at the start of the
          contiguously slackless interval is necessarily complete in the online
          schedule at the end of it, which contradicts the assumption that [j]
          is incomplete at time [t2]. *)

    (** Of the three steps, the second step is by far the most challenging one.
        We consider it next. *)

    (** * Existence of a Contiguously Slackless Interval *)

    (** In the second step of the overall proof strategy, the goal is to
        establish the existence of a contiguously slackless interval under two
        major assumptions: (1) the [transfer_schedulability_criterion] holds and
        (2) there exists a job that completes later in the online schedule than
        in the reference schedule.

        While this existence claim may not be so difficult for a human to "see,"
        it is not so easy to formally establish this existence proof such that
        Rocq verifies it. We therefore first establish a number of supporting
        auxiliary lemmas. *)

    (** ** Supporting Lemmas *)

    (** If a job is complete in the reference schedule and not complete in the
        online schedule, it is by definition a critical job at the time. *)

    Lemma late_in_critical_jobs :
      forall j t,
        ref_completed_by j t ->
        ~~ online_completed_by j t ->
        j \in critical_jobs t t.
    Proof.
      move=> j t COMP NCOMP.
      have [ZERO|POS] := (posnP (ref_job_cost j)).
      { exfalso.
        have := ref_cost_bounds_online_cost j.
        by move: NCOMP; rewrite /online_completed_by/completed_by/job_cost; lia. }
      { rewrite mem_filter.
        repeat (apply/andP; split => //).
        have [t' [/andP[ARR LT] SCHED]]: exists t' : nat, job_arrival j <= t' < t /\ scheduled_at ref_sched j t'.
        { apply: positive_service_implies_scheduled_since_arrival => //.
          by move: COMP; rewrite /ref_completed_by/completed_by/job_cost; lia. }
        rewrite /arrivals_up_to.
        by apply: job_in_arrivals_between => //; lia. }
    Qed.

    (** No job is late at the start of the schedule, which rules out some corner
        cases. *)

    Lemma late_not_at_start :
      forall j t,
        ref_completed_by j t ->
        ~~ online_completed_by j t ->
        t > 0.
    Proof.
      move=> j t COMP NCOMP.
      apply: (contraNltn _ NCOMP).
      rewrite leqn0 => /eqP ZERO.
      move: COMP; rewrite /ref_completed_by/online_completed_by/completed_by/job_cost.
      rewrite ZERO !service0.
      by move: (ref_cost_bounds_online_cost j); lia.
    Qed.

    (** ** Intervals of Non-Positive Slack *)

    (** As a stepping stone towards finding slackless intervals, we introduce
        the related notion of an interval with _non-positive slack_. This notion
        relaxes the slackless interval's strict equality to an inequality. It
        thus over-approximates slackless intervals (i.e., every slackless
        interval has non-positive slack, but an interval with non-positive slack
        may not satisfy the slackless definition if there is in fact negative
        "slack"). *)

    Definition nonpositive_slack t1 t2 :=
      \sum_(j <- critical_jobs t1 t2) remaining_cost_bound j t1  >= t2 - t1.

    (** Mirroring the step from slackless intervals to contiguously slackless
        intervals, we establish the notion of contiguously non-positive slack
        intervals, with the obvious interpretation: every suffix-interval must
        also have non-positive slack. *)

    Definition contiguously_nps t1 t2 :=
      [forall delta : 'I_(t2 - t1), nonpositive_slack (t1 + delta) t2].

    (** *** Facts about Intervals with Non-Positive Slack *)

    (** Before moving on, we establish some further auxiliary lemmas covering
        various cases coming up in the main proofs below. *)

    (** First, before the start of a maximally contiguously non-positive slack
        interval, there is an interval with positive slack. *)

    Lemma contiguously_nps_start :
      forall t0 t2,
        ~~ contiguously_nps t0 t2 ->
        contiguously_nps t0.+1 t2 ->
        ~~ nonpositive_slack t0 t2.
    Proof.
      move=> t0 t2 /forallPn /= [d NPS] /forallP /= CNPS.
      case: d NPS; case => [d //= /[1! addn0] LT|] //.
      move=> d LT NPS; exfalso.
      move: NPS => /negP; apply => //=.
      have LT': d < t2 - t0.+1 by lia.
      move: (CNPS (Ordinal LT')) => //=.
      by rewrite addSnnS.
    Qed.

    (** If a job is finished at a given time [t2] in the reference schedule, but
        not in the online schedule, then there exists a non-empty contiguously
        non-positive slack interval <<[t1, t2)>> that either starts at time zero
        or is preceded by an interval with positive slack.

        NB: Note the comments in the proof --- this is a key step. *)

    Lemma contiguously_nps_existence :
      forall j t2,
        ref_completed_by j t2 ->
        ~~ online_completed_by j t2 ->
        exists t1,
          contiguously_nps t1 t2
          /\ t1 < t2
          /\ (t1 = 0 \/ ~~ nonpositive_slack t1.-1 t2).
    Proof.
      move=> j t2 COMP NCOMP.
      (** As a starting point, we establish that <<[t2 -1, t2)>> has
          non-positive slack. *)
      have NPS2 : nonpositive_slack t2.-1 t2.
      { apply: (@leq_trans (\sum_(j' <- [:: j]) _)); last first.
        - apply: leq_sum_subseq.
          rewrite sub1seq.
          apply: critical_jobs_monotonicity; last exact: late_in_critical_jobs.
          by lia.
        - rewrite big_seq1.
          suff: remaining_cost_bound j t2.-1 > 0 by lia.
          apply: remaining_cost_positive.
          apply: (incompletion_monotonic _ _ _ _ _ NCOMP).
          by lia. }
      (** We "upgrade" [NPS2] to a contiguously non-positive slack interval.
          Since the interval contains only one point, this is conceptually
          trivial, but we need it as a witness for the below search via
          MathComp's [ex_minn] facility. *)
      have CNPS2 : contiguously_nps t2.-1 t2.
      { rewrite /contiguously_nps.
        apply: contraT => /forallPn /= [d +].
        move=> /negP; suff: nonpositive_slack (t2.-1 + d) t2 => //.
        have ->: nat_of_ord d = 0 by move: (ltn_ord d); lia.
        rewrite addn0.
        exact NPS2. }
      (** The following is a key step of the overall proof strategy: We search
          "backwards" in time from [t2.-1] until we find the starting point of
          the maximally, contiguously non-positive slack interval ending at
          [t2]. *)
      have WITNESS : exists t, contiguously_nps t t2 by  exists t2.-1.
      have [t1 CNPS MIN] := (find_ex_minn WITNESS).
      exists t1; repeat split => //;
        first by move: (MIN t2.-1 CNPS2) (late_not_at_start j t2 COMP NCOMP); lia.
      (** Finally, we do a case analysis on [t1 =?= 0] to figure out the last
          disjunction of the existence claim: either [t1 = 0], in which case the
          first case holds trivially, or [t1 = t0.+1 > 0], in which case we show
          that <<[t0, t2)>> has positive slack. *)
      case: t1 CNPS MIN => [| t0 CNPS MIN]; [by left|right].
      have [CNPS0|NCNPS] := boolP (contiguously_nps t0 t2);
        first by move: (MIN t0 CNPS0); lia.
      rewrite -pred_Sn.
      exact: contiguously_nps_start.
    Qed.


    (** *** Slackless Interval Existence Induction Step *)

    (** In the following, we establish a key technical lemma,
        [slackless_interval_step], which will later serve as the induction step
        in the main argument below. The lemma establishes that, if we have a
        slackless interval <<[t1, t2)>> and <<[t1 + 1, t2)>> has non-positive
        slack, then <<[t1 + 1, t2)>> is also a slackless interval. Intuitively,
        this will allow us to "grow" the contiguously slackless interval (the
        existence of which we seek to establish) via induction on the length of
        the interval.

        Since establishing [slackless_interval_step] is itself somewhat
        laborious, we reason by case analysis and break it up into smaller
        steps. *)


    (** **** Case 1: The Critical Job Completes *)

    (** The first case is characterized by the following added assumptions:

        - there is a critical job [j] scheduled at time [t1], and

        - [j] is _complete_ at time [t1 + 1].

        To help establish [slackless_interval_step] in this case, we first
        observe that such a job's remaining cost bound is necessarily zero. *)

    Lemma slackless_interval_step_case_completed_job_rem :
      forall t1 t2,
        slackless_interval t1 t2 ->
        nonpositive_slack t1.+1 t2 ->
        forall j,
          scheduled_at online_sched j t1 ->
          j \in critical_jobs t1 t2 ->
          online_completed_by j t1.+1 ->
          remaining_cost_bound j t1.+1 = 0.
    Proof.
      move=> t1 t2 /andP[_ ZS] NPS j SCHED IN COMP.
      apply /eqP; rewrite -leqn0 leqNgt; apply /negP => POS.
      move: NPS; rewrite /nonpositive_slack.
      rewrite (critical_jobs_filter_complete t1) //
        big_filter_cond big_seq_cond.
      rewrite (eq_bigr (fun j' => remaining_cost_bound j' t1)); last first.
      { move=> j' /andP[IN' /andP[NCOMP' _]].
        rewrite /remaining_cost_bound.
        apply/eqP; rewrite eqn_sub2lE;
          try (apply: leq_trans;
               last exact: H_job_cost_bounded;
               exact: service_at_most_cost).
        rewrite /service -service_during_last_plus_before //.
        apply/eqP; rewrite service_at_is_scheduled_at -[RHS]addn0.
        apply/eqP; rewrite eqn_add2l eqb0.
        apply: scheduled_job_at_neq => //.
        apply: contraT => /negPn/eqP EQ.
        move: NCOMP' => /negP.
        by rewrite -EQ. }
      { rewrite (eq_bigl (fun j' => (j' \in critical_jobs t1 t2) && (j != j'))).
        { rewrite -big_seq_cond => NPS.
          have GT1: remaining_cost_bound j t1 > 1.
          { move: POS; rewrite /remaining_cost_bound.
            rewrite /service -service_during_last_plus_before //.
            rewrite service_at_is_scheduled_at SCHED.
            by lia. }
          move: ZS.
          rewrite (bigID (fun j' => j == j')) /=.
          rewrite (big_pred1_seq _ _ IN) //; last exact: critical_jobs_uniq.
          by lia. }
        { move=> j'.
          case IN': (j' \in critical_jobs t1 t2) => //=.
          case: (eqVneq j j') => [<-|NEQ //=];
            first by rewrite COMP.
          rewrite andbT.
          have INCOMP: ~~ online_completed_by j' t1
            by move: IN'; rewrite mem_filter => /andP[/andP[]].
          apply: not_scheduled_remains_incomplete => //.
          by apply: scheduled_job_at_neq. } }
    Qed.

    (** With the above helper lemma in place, we can establish
        [slackless_interval_step]'s claim under the assumptions of the first
        case. *)

    Lemma slackless_interval_step_case_completed_job :
      forall t1 t2,
        slackless_interval t1 t2 ->
        t1.+1 < t2 ->
        nonpositive_slack t1.+1 t2 ->
        forall j,
          scheduled_at online_sched j t1 ->
          j \in critical_jobs t1 t2 ->
          online_completed_by j t1.+1 ->
          slackless_interval t1.+1 t2.
    Proof.
      move=> t1 t2 SL LT NPS j SCHED IN COMP.
      have [ZERO|+] := posnP (remaining_cost_bound j t1.+1);
        last by rewrite (slackless_interval_step_case_completed_job_rem _ t2).
      apply/andP; split => //.
      rewrite (critical_jobs_filter_complete t1) // big_filter_cond.
      rewrite big_rmcond_in /=.
      { move: SL => /andP[_ +]; rewrite (remaining_cost_invariant _ t1 t1.+1) //.
        - by lia.
        - exact: critical_jobs_uniq.
        - move=> t /andP[LO HI].
          exists j; apply/andP; split => //.
          by have -> : t = t1 by lia. }
      { move=> j' IN'.
        rewrite andbT => /negPn COMP'.
        suff -> : j' = j => //.
        apply/eqP/contraT => NEQ.
        suff /negP: ~~ online_completed_by j' t1.+1 => //.
        rewrite /online_completed_by.
        apply not_scheduled_remains_incomplete;
          first by move: IN'; rewrite mem_filter /online_completed_by => /andP[/andP[_ NCOMP'] _].
        move: NEQ; rewrite eq_sym => NEQ.
        by apply: scheduled_job_at_neq. }
    Qed.

    (** **** Case 2: The Critical Job Remains Incomplete *)

    (** The second case covers the complementary situation:

        - there is a critical job [j] scheduled at time [t1] but

        - [j] remains _incomplete_ at time [t1 + 1]. *)

    Lemma slackless_interval_step_case_incomplete_job :
      forall t1 t2,
        slackless_interval t1 t2 ->
        t1.+1 < t2 ->
        nonpositive_slack t1.+1 t2 ->
        forall j,
          scheduled_at online_sched j t1 ->
          j \in critical_jobs t1 t2 ->
          ~~ online_completed_by j t1.+1 ->
          slackless_interval t1.+1 t2.
    Proof.
      move=> t1 t2 /andP[_ ZS] LT NPS j SCHED IN NCOMP.
      apply/andP; split => //.
      rewrite (critical_jobs_filter_complete t1) //.
      rewrite -(@eq_in_filter _ predT); last first.
      { move=> j' IN'.
        case: (eqVneq j' j) => [-> //| /[1! eq_sym] NEQ //=]; symmetry.
        have INCOMP: ~~ online_completed_by j' t1
          by move: IN'; rewrite mem_filter => /andP[/andP[]].
        apply: not_scheduled_remains_incomplete => //.
        by apply: scheduled_job_at_neq. }
      { rewrite filter_predT.
        move: ZS; rewrite (remaining_cost_invariant _ t1 t1.+1) //.
        - by lia.
        - exact: critical_jobs_uniq.
        - move=> t /andP[LO HI].
          exists j; apply/andP; split => //.
          by have -> : t = t1 by lia. }
    Qed.


    (** **** Induction Step by Case Analysis *)

    (** From the transfer schedulability criterion [H_ts_criterion], we have
        that there is indeed a critical job [j] scheduled at the beginning [t1]
        of any given slackless interval. We proceed by case analysis on whether
        or not [j] completes at the next step [t1 + 1], which results in exactly
        the two cases analyzed above. *)

    Lemma slackless_interval_step :
      forall t1 t2,
        slackless_interval t1 t2 ->
        t1.+1 < t2 ->
        nonpositive_slack t1.+1 t2 ->
        slackless_interval t1.+1 t2.
    Proof.
      move=> t1 t2 SL LT NPS.
      move: (H_ts_criterion t1 t2 SL) => [j /andP[SCHED IN]].
      have [COMP|NCOMP] := boolP( online_completed_by j t1.+1 ).
      - by apply: slackless_interval_step_case_completed_job.
      - by apply: slackless_interval_step_case_incomplete_job.
    Qed.

    (** ** Main Argument: Slackless Interval Existence *)

    (** With all required helper lemmas in place, we can proceed to the main
        argument, which establishes that a late completion is necessarily
        preceded by a contiguously slackless interval. *)

    (** We first establish the main "upgrade lemma": if we have a slackless
        interval <<[t1, t2)>>, and know that <<[t1, t2)>> is also a contiguously
        non-positive slack interval, then we can conclude that <<[t1, t2)>> is
        in fact also contiguously slackless. *)

    Lemma slackless_interval_continuation :
      forall t1 t2,
        slackless_interval t1 t2 ->
        contiguously_nps t1 t2 ->
        [forall delta : 'I_(t2 - t1), slackless_interval (t1 + delta) t2].
    Proof.
      move=> t1 t2 SL CNPS.
      apply /forallP => /= d.
      case: d => d //=.
      (* NB: The following line is a "magic incantation" from MathComp that
         makes [elim] do a _strong induction_ on [d] (rather than a regular
         induction). *)
      case: (ubnPgeq d).
      elim: d => [d /[!leqn0]/eqP ->|b IH d DB LT]; first by rewrite addn0.
      have [LEQ|LTbd] := leqP d b; first by apply IH.
      move: SL => /andP [LT' _].
      have -> : d = b.+1 by lia.
      rewrite addnS.
      apply: slackless_interval_step; [by apply IH; lia| by lia|].
      move: CNPS => /forallP /= CNPS.
      rewrite -addnS.
      have LT'' : b.+1 < t2 - t1 by lia.
      by move: (CNPS (Ordinal LT'')).
    Qed.

    (** With the "upgrade lemma" [slackless_interval_continuation] in place, we
        are finally ready to derive the existence of contiguously slackless
        intervals from a late completion.

        Note: This proof is commented more than usual to highlight the key
        reasoning steps. *)

    Lemma slackless_interval_existence :
      forall j t2,
        ref_completed_by j t2 ->
        ~~ online_completed_by j t2 ->
        exists (t1 : instant),
          contiguously_slackless_interval t1 t2
          && (j \in critical_jobs t1 t2).
    Proof.
      (** Setup: job [j] is incomplete at time [t2] in the online schedule, but
          complete in the reference schedule. *)
      move=> j t2 COMP NCOMP.
      (** A: Recall that a contiguously non-positive slack interval exists
          before [t2]. *)
      have [t1 [CNPS [LT START]]] :=
        contiguously_nps_existence j t2 COMP NCOMP.
      move: (CNPS) => /forallP /= CNPS'.
      (** B: We will show that <<[t1, t2)>> is a contiguously slackless
          interval. *)
      exists t1; apply/andP; split;
        (** Showing that [j] is in [critical_jobs t1 t2] is trivial and done
            here. *)
        last by (apply: critical_jobs_monotonicity; last exact: late_in_critical_jobs); lia.
      (** C: We recall that <<[t1, t2)>> has non-positive slack. *)
      have NPS1 : nonpositive_slack t1 t2.
      { have LT' : 0 < t2 - t1 by lia.
        move: (CNPS' (Ordinal LT')) => //=.
        by rewrite addn0. }
      (** D: From the observation that <<[t1, t2)>> has non-positive slack, we
          infer that <<[t1, t2)>> is in fact slackless. This step needs to deal
          with a bunch of corner cases (e.g., at time zero). *)
      have SL1 : slackless_interval t1 t2.
      { move: (NPS1); rewrite /nonpositive_slack leq_eqVlt => /orP [EQ|NEQ];
          first by repeat (apply/andP; split => //).
        exfalso.
        move: START => [EQ1|POS].
        - move: NEQ; rewrite EQ1 /nonpositive_slack/remaining_cost_bound.
          rewrite subn0.
          under eq_bigr do rewrite service0 subn0.
            move: (critical_jobs_min_completion_time t2).
          by lia.
        - move: POS.
          rewrite /nonpositive_slack -ltnNge.
          by feed (critical_jobs_remaining_cost_monotonic t1.-1 t1 t2); lia. }
      apply/andP; split; first exact: SL1.
      (** E: Finally, the above "upgrade" lemma allows us to go from
          <<[t1, t2)>> being slackless to <<[t1, t2)>> being _contiguously_
          slackless. *)
      exact: slackless_interval_continuation.
    Qed.

    (** * All Critical Jobs Complete in a Contiguously Slackless Interval *)

    (** The third step of the overall proof strategy is to show that all
        critical jobs are complete at the end of a contiguously slackless
        interval. We establish this key "stepping stone" in the following lemma.

        From the length of the proof and the absence of many additional
        supporting lemmas, it should be obvious that this step is much easier
        than the preceding one. Which makes intuitive sense since the
        "contiguously slackless" property is a very strong property, which is
        hard to establish but easy to exploit. *)

    Lemma slackless_interval_completion :
      forall j t1 t2,
        contiguously_slackless_interval t1 t2 ->
        (j \in critical_jobs t1 t2) ->
        online_completed_by j t2.
    Proof.
      move=> j t1 t2 /andP[SL /forallP /= CSL] CRIT.
      (** We are going to argue that the total remaining job-cost bound for the
          critical jobs across <<[t1, t2)>> is zero, and they all must have
          completed. What remains to be shown afterwards is that the remaining
          job-cost bound is indeed zero. *)
      apply: (remaining_cost_zero (critical_jobs t1 t2)) => //.
      (** The main setup step: convert the fact that <<[t1, t2)>> is
          contiguously slackless into the property that at each point in the
          interval there is a critical job scheduled. *)
      have SCHED:
        forall t', t1 <= t' < t2
              -> exists j', (j' \in critical_jobs t1 t2)
                      && scheduled_at online_sched j' t'.
      { move=> t' /andP[LO HI].
        have LT' : t' - t1 < (t2 - t1) by lia.
        move: (CSL (Ordinal LT')) => //=.
        have -> : t1 + (t' - t1) = t' by lia.
        move=> SL'.
        have [j' /andP[SCHED' IN']] := (H_ts_criterion _ _ SL').
        exists j'; apply/andP; split => //.
        apply: critical_jobs_monotonicity; last exact IN'.
        by lia. }
      move: SL => /andP[LT /eqP SL'].
      (** From the property that there is always a critical job scheduled, we
          can apply a helper lemma that lets us relate the interval length to
          the accumulated service. *)
      have REM := remaining_cost_invariant (critical_jobs t1 t2) t1 t2 _ _ SCHED.
      feed_n 2 REM; [by lia|exact: critical_jobs_uniq|].
      (** The rest is simple arithmetic. *)
      by move: REM; rewrite SL'; lia.
    Qed.

    (** This marks the end of the generic argument for an abstract
        [job_cost_bound]. We will now close this section and establish the
        concrete results. *)

  End ParametericCostBound.

  (** * Main Results *)

  (** Naturally, to derive any guarantees, the reference schedule needs to
      over-approximate the job costs encountered in the online schedule. We add
      this assumption now. *)

  Hypothesis H_bounded_job_costs : forall j, online_job_cost j <= ref_job_cost j.

  (** ** Sufficiency Theorem w.r.t. Online Job Costs *)

  (** Using the generic argument for [job_cost_bound := online_job_cost], we
      establish that [transfer_schedulability_criterion] is a sufficient
      condition for [schedulability_transferred] to hold. *)

  Theorem online_transfer_schedulability_criterion_sufficiency :
    transfer_schedulability_criterion online_job_cost -> schedulability_transferred.
  Proof.
    move=> CRIT j t2 COMP.
    (** By contradiction: suppose [j] is not complete in the online schedule at
        time [t], but it is complete in the reference schedule. *)
    apply: contraT => NCOMP.
    (** Observe that [online_job_cost] trivially "bounds" [online_job_cost]. *)
    have BOUNDED : forall j, online_job_cost j <= online_job_cost j by done.
    (**  There is necessarily a contiguously slackless interval <<[t1, t2)>>. *)
    have [t1 /andP[CSL IN]] :=
      slackless_interval_existence _ BOUNDED H_bounded_job_costs CRIT j t2 COMP NCOMP.
    (** That means that [j] is complete at time [t2], which contradicts the
        initial assumption that [j] is incomplete at time [t2]. *)
    suff: online_completed_by j t2 by move: NCOMP => /negP.
    by apply: (slackless_interval_completion _ BOUNDED CRIT j t1).
  Qed.

  (** As a straightforward corollary, and for the sake of completeness, we lift
      [online_transfer_schedulability_criterion_sufficiency] to the level of job
      deadlines. *)

  Corollary online_transfer_schedulability_criterion_ensures_schedulability :
    transfer_schedulability_criterion online_job_cost ->
    (forall j, ref_job_meets_deadline j -> online_job_meets_deadline j).
  Proof.
    move=> CRIT j MET.
    apply: deadlines_met => //.
    exact: online_transfer_schedulability_criterion_sufficiency.
  Qed.

  (** ** Necessity Theorem w.r.t. Online Job Costs *)

  (** For [job_cost_bound := online_job_cost], we can also establish the reverse
      direction: [transfer_schedulability_criterion online_job_cost] is a
      _necessary_ condition for [schedulability_transferred], which establishes
      the equivalency of the two definitions for online job costs. *)

  (** As a stepping stone, we first establish a lemma that shows that, if there
      ever is a slackless interval in which none of the critical jobs is
      scheduled at the start of the interval, then some job _must_ finish later
      in the online schedule than in the reference schedule. *)

  Lemma delay_if_no_critical_job_is_scheduled :
    forall t1 t2,
      slackless_interval online_job_cost t1 t2 ->
      {in critical_jobs t1 t2, forall j, ~~ scheduled_at online_sched j t1} ->
      (exists j, (j \in critical_jobs t1 t2) /\ ~~ online_completed_by j t2).
  Proof.
    move=> t1 t2 /andP [LT ZS] NONE.
    (** Let's restate the claim in terms of [has], which we can contradict more
        easily. *)
    suff /hasP[j IN NCOMP]:
      has (fun j => ~~ online_completed_by j t2)  (critical_jobs t1 t2) by exists j.
    (** By contradiction: suppose that all critical jobs are complete at time
        [t2]. *)
    apply: contraT => /hasPn COMP.
    (** As a stepping stone, we observe that an incomplete critical job
        necessarily exists if the total remaining cost bound is non-zero. *)
    have NCOMP: \sum_(j <- critical_jobs t1 t2)
                  remaining_cost_bound online_job_cost j t2 > 0
                -> exists2 j, (j \in critical_jobs t1 t2)
                             & ~~ online_completed_by j t2.
    { rewrite sum_nat_gt0 => /hasP [j IN NZ].
      exists j; first by move: IN; rewrite filter_predT.
      rewrite /online_completed_by/completed_by -ltnNge.
      move: NZ; rewrite /remaining_cost_bound/job_cost.
      by lia. }
    (** Hence we proceed to show that the total remaining job cost is non-zero
        at time [t2]. *)
    suff NZ: \sum_(j <- critical_jobs t1 t2) remaining_cost_bound online_job_cost j t2 > 0.
    { have [j' IN' NCOMP'] := NCOMP NZ.
      move: (COMP j' IN') => /negPn.
      by move: NCOMP' => /negP. }
    (** In the following, we exploit the assumption that no critical job is
        scheduled at time [t1] implies that the critical jobs collectively
        receive no service at that time. Before we can use that fact, though, we
        must first reshape the sum of remaining cost bounds to expose the
        collective service received at time [t1] in the formula. *)
    move: ZS; rewrite /remaining_cost_bound.
    (** First, split the sum of remaining cost bounds into a sum of job costs
        and a sum of service received. *)
    rewrite !sumnB => [|j _|j _]; try exact: service_at_most_cost.
    move=> /eqP ZS.
    (** Next, split the service received into the service received up to (but
        not including) time [t1] and the service received during
        <<[t1 + 1,t2)>>.

        Note this leaves out the service received _at_ time [t1], which we know
        to be zero due to the assumption that no critical job is scheduled at
        time [t1]. *)
    rewrite [X in _ - X]big_seq_cond.
    under [X in _ - X]eq_bigr => j IN.
    { rewrite  -(service_cat _ j t1 t2) // -service_during_first_plus_later //.
      rewrite service_at_is_scheduled_at.
      have -> //=: scheduled_at online_sched j t1 = false.
      { move: IN; rewrite andbT => IN.
        by apply/negbTE/NONE. }
      rewrite add0n.
      over. }
    rewrite -big_seq_cond big_split_idem //=.
    (** Observe that the sum of [service_during] in the goal matches the
        definition of [service_of_jobs], for which there are useful lemmas in
        Prosa. *)
    rewrite -/(service_of_jobs _ predT _ t1.+1 t2).
    (** Rewrite the goal to expose that we need to show that the service
        received by the critical jobs during <<[t1 + 1, t2)>> is strictly less
        than [t2 - t1]. *)
    rewrite subnDA ZS.
    (** Recall a basic fact about [service_of_jobs] on unit-speed uniprocessors:
        the total amount of service received in an interval is trivially
        upper-bounded by the interval length. *)
    have: service_of_jobs online_sched predT (critical_jobs t1 t2) t1.+1 t2 <= t2 - (t1.+1).
    { apply: service_of_jobs_le_length_of_interval' => //.
      exact: critical_jobs_uniq. }
    (** The goal then follows immediately from simple arithmetic. *)
    by lia.
  Qed.

  (** From the preceding stepping stone, we can easily prove that
      [schedulability_transferred] implies
      [transfer_schedulability_criterion online_job_cost]. *)

  Theorem online_transfer_schedulability_criterion_necessity :
    schedulability_transferred -> transfer_schedulability_criterion online_job_cost.
  Proof.
    (** Consider a slackless interval <<[t1, t2)>>. *)
    move=> TRANS t1 t2 SL.
    (** To prove the claim, it suffices to show that one of the critical jobs is
        scheduled at [t1]. *)
    suff: has (fun j => scheduled_at online_sched j t1) (critical_jobs t1 t2)
      by move=> /hasP [j IN SCHED]; exists j; apply/andP; split.
    (** By contradiction: suppose there is no such job scheduled at [t1]. *)
    apply: contraT.
    rewrite -all_predC => /allP => NSCHED.
    (** From the stepping stone lemma, we have that some job finishes late as a
        result. *)
    have [j [IN NCOMP]]: exists j, (j \in critical_jobs t1 t2) /\ ~~ online_completed_by j t2
      by apply: delay_if_no_critical_job_is_scheduled.
    move: IN; rewrite mem_filter => /andP[ /andP[COMP _] _].
    (** But this contradicts the precondition that no job finishes later than in
        the reference schedule. *)
    move: (TRANS j t2 COMP) => COMP'.
    by move: NCOMP => /negP.
  Qed.

  (** ** Sufficiency Theorem w.r.t. Reference Job Costs *)

  (** Using the generic argument for [job_cost_bound := ref_job_cost], we
      establish that [transfer_schedulability_criterion] is a sufficient
      condition for [schedulability_transferred] to hold even if job costs are
      over-approximated. *)

  Theorem ref_transfer_schedulability_criterion_sufficiency :
    transfer_schedulability_criterion ref_job_cost -> schedulability_transferred.
  Proof.
    move=> CRIT j t2 COMP.
    (** By contradiction: suppose [j] is not complete in the online schedule at
        time [t], but it is complete in the reference schedule. *)
    apply: contraT => NCOMP.
    (** Observe that [ref_job_cost] trivially "bounds" [ref_job_cost]. *)
    have BOUNDED : forall j, ref_job_cost j <= ref_job_cost j by done.
    (** There is necessarily a contiguously slackless interval <<[t1, t2)>>. *)
    have [t1 /andP[CSL IN]] :=
      slackless_interval_existence _ H_bounded_job_costs BOUNDED CRIT j t2 COMP NCOMP.
    (** That means that [j] is complete at time [t2], which contradicts the
        initial assumption that [j] is incomplete at time [t2]. *)
    suff: online_completed_by j t2 by move: NCOMP => /negP.
    by apply: (slackless_interval_completion _ H_bounded_job_costs CRIT j t1).
  Qed.

  (** For completeness' sake, we once more lift the sufficient condition to the
      level of job deadlines. *)

  Corollary ref_transfer_schedulability_criterion_ensures_schedulability :
    transfer_schedulability_criterion ref_job_cost ->
    (forall j, ref_job_meets_deadline j -> online_job_meets_deadline j).
  Proof.
    move=> CRIT j MET.
    apply: deadlines_met => //.
    exact: ref_transfer_schedulability_criterion_sufficiency.
  Qed.

  (** Without further restrictions, it is not possible to establish necessity
      for [job_cost_bound := ref_job_cost]. *)

End TransferSchedulability.



