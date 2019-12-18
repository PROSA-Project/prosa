Require Export prosa.analysis.facts.transform.replace_at.
Require Export prosa.analysis.facts.behavior.deadlines.

(** In this file, we establish invariants about schedules in which two
    allocations have been swapped, as for instance it is done in the
    classic EDF optimality proof. *)

Section SwappedFacts.
  (** For any given type of jobs... *)
  Context {Job : JobType}.
  (** ... any given type of processor states: *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** ...consider any given reference schedule. *)
  Variable sched: schedule PState.

  (** Suppose we are given two specific times [t1] and [t2]. *)
  Variable t1 t2: instant.

  (** In the following, let [sched'] denote the schedule in which the
     allocations at [t1] and [t2] have been swapped. *)
  Let sched' := swapped sched t1 t2.
  
  (** First, we note that the trivial case where t1 == t2 is not interesting
     because then the two schedules are identical. *)
  Lemma trivial_swap:
    t1 = t2 ->
    forall t,
      sched t = sched' t.
  Proof.
    rewrite /sched' => <- t.
    rewrite /swapped /replace_at.
    case: (boolP (t1 == t)); last by done.
    by move /eqP ->.
  Qed.

  (** In this trivial case, the amount of service received hence
     is obviously always identical. *)
  Lemma trivial_swap_service_invariant:
    t1 = t2 ->
    forall t j,
      service sched j t = service sched' j t.
  Proof.
    move=> SAME t j.
    rewrite /service /service_during /service_at.
    apply eq_big_nat => t' RANGE.
    by rewrite trivial_swap.
  Qed.

  (** In any case, the two schedules do not differ at non-swapped times. *)
  Lemma swap_other_times_invariant:
    forall t,
      t <> t1 ->
      t <> t2 ->
      sched t = sched' t.
  Proof.
    move=> t NOT_t1 NOT_t2.
    by rewrite /sched' /swapped !rest_of_schedule_invariant //.
  Qed.

  (** By definition, if a job is scheduled at t2 in the original
     schedule, then it is found at t1 in the new schedule. *)
  Lemma swap_job_scheduled_t1:
    forall j,
      scheduled_at sched' j t1 =
      scheduled_at sched j t2.
  Proof.
    move=> j.
    rewrite /scheduled_at /sched' /swapped /replace_at.
    case: (boolP(t2 == t1)) => [/eqP EQ|NE].
    - by rewrite EQ.
    - by rewrite ifT.
  Qed.

  (** Similarly, a job scheduled at t1 in the original schedule is
     scheduled at t2 after the swap. *)
  Lemma swap_job_scheduled_t2:
    forall j,
      scheduled_at sched' j t2 =
      scheduled_at sched j t1.
  Proof.
    move=> j.
    rewrite /sched' /scheduled_at /swapped /replace_at.
    case: (boolP(t2 == t1)) => [/eqP EQ|NE].
    - by rewrite ifT.
    - by rewrite ifT.
  Qed.

  (** If a job is scheduled at any time not involved in the swap, then
     it remains scheduled at that time in the new schedule. *)
  Lemma swap_job_scheduled_other_times:
    forall j t,
      t1 != t ->
      t2 != t ->
      scheduled_at sched' j t =
      scheduled_at sched j t.
  Proof.
    move=> j t /eqP NOT_t1 /eqP NOT_t2.
    rewrite /scheduled_at.
    by rewrite swap_other_times_invariant //; apply: not_eq_sym.
  Qed.

  (** To make case analysis more convenient, we summarize the preceding
     three lemmas as a disjunction. *)
  Corollary swap_job_scheduled_cases:
    forall j t,
      scheduled_at sched' j t ->
      scheduled_at sched' j t = scheduled_at sched j t
      \/
      t = t1 /\ scheduled_at sched' j t = scheduled_at sched j t2
      \/
      t = t2 /\ scheduled_at sched' j t = scheduled_at sched j t1.
  Proof.
    move=> j t SCHED.
    destruct (t1 == t) eqn:T1.
    - right. left. move: T1 => /eqP T1.
      split => //.
      by rewrite -swap_job_scheduled_t1 T1.
    - destruct (t2 == t) eqn:T2.
      + right. right. move: T2 => /eqP T2.
        split => //.
        by rewrite -swap_job_scheduled_t2 T2.
      + left. move: T1 T2 => /eqP/eqP T1 /eqP/eqP T2.
        by rewrite -swap_job_scheduled_other_times.
  Qed.

  (** From this, we can easily conclude that no jobs have appeared out
     of thin air: if a job scheduled at some time in the new schedule,
     then it was also scheduled at some time in the original
     schedule. *)
  Corollary swap_job_scheduled:
    forall j t,
      scheduled_at sched' j t ->
      exists t',
        scheduled_at sched j t'.
  Proof.
    move=> j t SCHED.
    move: (SCHED).
    move: (swap_job_scheduled_cases j t SCHED) => [->|[[_ ->] | [_ ->]]].
    - by exists t.
    - by exists t2.
    - by exists t1.
  Qed.

  (** Mirroring swap_job_scheduled_cases above, we also state a
     disjunction for case analysis under the premise that a job is
     scheduled in the original schedule. *)
  Lemma swap_job_scheduled_original_cases:
    forall j t,
      scheduled_at sched j t ->
      scheduled_at sched' j t = scheduled_at sched j t
      \/
      t = t1 /\ scheduled_at sched' j t2 = scheduled_at sched j t
      \/
      t = t2 /\ scheduled_at sched' j t1 = scheduled_at sched j t.
  Proof.
    move=> j t SCHED.
    destruct (t1 == t) eqn:T1.
    - right; left. move: T1 => /eqP T1.
      split => //.
      by rewrite swap_job_scheduled_t2 T1.
    - destruct (t2 == t) eqn:T2.
      + right; right. move: T2 => /eqP T2.
        split => //.
        by rewrite swap_job_scheduled_t1 T2.
      + left. move: T1 T2 => /eqP/eqP T1 /eqP/eqP T2.
        by rewrite swap_job_scheduled_other_times.
  Qed.

  (** Thus, we can conclude that no jobs are lost: if a job is
     scheduled at some point in the original schedule, then it is also
     scheduled at some point in the new schedule. *)
  Corollary swap_job_scheduled_original:
    forall j t,
      scheduled_at sched j t ->
      exists t',
        scheduled_at sched' j t'.
  Proof.
    move=> j t SCHED.
    move: (SCHED).
    move: (swap_job_scheduled_original_cases j t SCHED) => [<-|[[_ <-] | [_ <-]]].
    - by exists t.
    - by exists t2.
    - by exists t1.
  Qed.

  (** In the following, we lift the above basic invariants to
      statements about invariants about the cumulative amount of
      service received. *)
  
  (** To avoid dealing with symmetric cases, assume in the following
     that t1 and t2 are ordered. *)
  Hypothesis H_well_ordered: t1 <= t2.

  (** As another trivial invariant, we observe that nothing has changed
     before time t1. *)
  Lemma swap_before_invariant:
    forall t,
      t < t1 ->
      sched t = sched' t.
  Proof.
    move=> t t_lt_t1.
    move: (ltn_leq_trans t_lt_t1 H_well_ordered) => t_lt_t2.
    by apply swap_other_times_invariant => /eqP /eqP EQ; subst;
       [move: t_lt_t1|move: t_lt_t2]; rewrite ltnn.
  Qed.

  (** Similarly, nothing has changed after time t2. *)
  Lemma swap_after_invariant:
    forall t,
      t2 < t ->
      sched t = sched' t.
  Proof.
    move=> t t2_lt_t.
    move: (leq_ltn_trans H_well_ordered t2_lt_t) => t1_lt_t.
    by apply swap_other_times_invariant => /eqP /eqP EQ; subst;
       [move: t1_lt_t|move: t2_lt_t]; rewrite ltnn.
  Qed.

  (** Thus, we observe that, before t1, the two schedules are identical with
     regard to the service received by any job because they are identical. *)
  Corollary service_before_swap_invariant:
    forall t,
      t <= t1 ->
      forall (j : Job),
        service sched j t = service sched' j t.
  Proof.
    move => t le_tt1 j.
    rewrite /service.
    rewrite -!service_at_other_times_invariant //; left; first by done.
    apply leq_trans with (n := t1) => //;
      by apply ltnW.
  Qed.

  (** Likewise, we observe that, *after* t2, the swapped schedule again does not
     differ with regard to the service received by any job. *)
  Lemma service_after_swap_invariant:
    forall t,
      t2 < t ->
      forall (j : Job),
        service sched j t = service sched' j t.
  Proof.
    move => t t2t j.
    move: H_well_ordered. rewrite leq_eqVlt => /orP [/eqP EQ|t1_lt_t2];
      first by apply trivial_swap_service_invariant.
    have TIME: 0 <= t1 < t
      by apply /andP; split; try apply ltn_trans with (n := t2); done.
    rewrite /service !service_in_replaced// /service_at// /replace_at //.
    rewrite ifT// ifT// ifF;
      last by apply ltn_eqF; exact.
    rewrite subn_abba //.
    rewrite -(service_split_at_point _ _ _ t1 _) /service_at //.
    apply leq_trans with (n := service_during sched j 0 t1 + service_in j (sched t1));
      [rewrite addnC|]; by apply leq_addr.
  Qed.

  (** Finally, we note that, trivially, jobs that are not involved in
     the swap receive invariant service. *)
  Lemma service_of_others_invariant:
    forall t j,
      ~~ scheduled_in j (sched t1) ->
      ~~ scheduled_in j (sched t2) ->
      service sched j t = service sched' j t.
  Proof.
    move=> t j NOT1 NOT2.
    move: H_well_ordered. rewrite leq_eqVlt => /orP [/eqP EQ|t1_lt_t2];
      first by apply trivial_swap_service_invariant.
    rewrite /service.
    rewrite -!service_during_of_others_invariant // !/replace_at //;
            [rewrite ifT// | rewrite ifT// | rewrite ifF// ].
      by apply ltn_eqF.
  Qed.

End SwappedFacts.

(** In the following section, we observe that, if the original
    schedule satisfies certain properties, then so does the new
    scheduled obtained by swapping the allocations at times [t1] and
    [t2]. *)
Section SwappedScheduleProperties.
  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.
  (** ... any given type of processor states: *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** ...consider any given reference schedule. *)
  Variable sched: schedule PState.

  (** Suppose we are given two specific times [t1] and [t2]... *)
  Variable t1 t2: instant.

  (** ...such that [t1] is no later than [t2]. *)
  Hypothesis H_order: t1 <= t2.

  (** We let [sched'] denote the schedule in which the allocations at
      [t1] and [t2] have been swapped. *)
  Let sched' := swapped sched t1 t2.

  (** First, we observe that if jobs never accumulate more service than
      required, then that's still the case after the swap. *)
  Lemma swapped_service_bound:
    (forall j t, service sched  j t <= job_cost j) ->
    (forall j t, service sched' j t <= job_cost j).
  Proof.
    move=> COMP.
    rewrite /completed_jobs_dont_execute => j  t.
    wlog: t /  (t2 < t); last first.
    {
      move=> LATE.
      move: H_order. rewrite leq_eqVlt => /orP [/eqP EQ| LT].
      - by rewrite -(trivial_swap_service_invariant sched t1 t2) //.
      - by rewrite -(service_after_swap_invariant sched t1 t2) //.
    }
    {
      move=> ARGUMENT.
      case: (boolP (t2 < t)); first by apply (ARGUMENT t).
      rewrite -leqNgt => EARLY.
      apply leq_trans with (n := service sched' j t2.+1).
      - apply service_monotonic.
        by apply leq_trans with (n := t2) => //.
      - by apply (ARGUMENT t2.+1).
    }
  Qed.

  (** From the above service bound, we conclude that, if if completed jobs don't
     execute in the original schedule, then that's still the case after the
     swap, assuming an ideal unit-service model (i.e., scheduled jobs receive
     exactly one unit of service). *)
  Lemma swapped_completed_jobs_dont_execute:
    unit_service_proc_model PState ->
    ideal_progress_proc_model PState ->
    completed_jobs_dont_execute sched ->
    completed_jobs_dont_execute sched'.
  Proof.
    move=> UNIT IDEAL COMP.
    apply ideal_progress_completed_jobs => //.
    apply swapped_service_bound.
    by move=> j; apply service_at_most_cost.
  Qed.

  (** Suppose all jobs in the original schedule come from some arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

  (** ...then that's still the case in the new schedule. *)
  Lemma swapped_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched' arr_seq.
  Proof.
    move: H_from_arr_seq. rewrite /jobs_come_from_arrival_sequence => ARR_sched j t SCHED.
    move: (swap_job_scheduled sched _ _ j t SCHED) => [t' SCHED'].
    by apply (ARR_sched j t' SCHED').
  Qed.

End SwappedScheduleProperties.

(** In the next section, we consider a special case of swaps: namely,
    when the job moved earlier has an earlier deadline than the job
    being moved to a later allocation, assuming that the former has
    not yet missed its deadline, which is the core transformation of
    the classic EDF optimality proof. *)
Section EDFSwap.
  (** For any given type of jobs with costs and deadlines... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job}.
  (** ... any given type of processor states... *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** ...consider a given reference schedule... *)
  Variable sched: schedule PState.

  (** ...in which complete jobs don't execute... *)
  Hypothesis H_completed_jobs:
    completed_jobs_dont_execute sched.

  (** ...and scheduled jobs always receive service. *)
  Hypothesis H_scheduled_implies_serviced: ideal_progress_proc_model PState.

  (** Suppose we are given two specific times [t1] and [t2]... *)
  Variable t1 t2: instant.

  (** ...that are ordered. *)
  Hypothesis H_well_ordered: t1 <= t2.

  (** Further, assume that, if there are jobs scheduled at times t1 and t2, then
     they either have the same deadline or violate EDF, ... *)
  Hypothesis H_not_EDF:
    forall j1 j2,
      scheduled_at sched j1 t1 ->
      scheduled_at sched j2 t2 ->
      job_deadline j1 >=  job_deadline j2.

  (** ...and that we don't move idle times or deadline misses earlier,
     i.e., if t1 is not an idle time, then neither is t2 and whatever
     job is scheduled at time t2 has not yet missed its deadline. *)
  Hypothesis H_no_idle_time_at_t2:
    forall j1,
      scheduled_at sched j1 t1 ->
      exists j2, scheduled_at sched j2 t2 /\ job_deadline j2 > t2.

  (** Consider the schedule obtained from swapping the allocations at times t1 and t2. *)
  Let sched' := swapped sched t1 t2.

  (** The key property of this transformation is that, for any job that
     meets its deadline in the original schedule, we have not
     introduced any deadline misses, which we establish by considering
     a number of different cases. *)
  Section NoNewDeadlineMissesCases.

    (** Consider any job... *)
    Variable j: Job.

    (** ... that meets its deadline in the original schedule. *)
    Hypothesis H_deadline_met: job_meets_deadline sched j.

    (** First we observe that jobs that are not involved in the swap
       still meet their deadlines. *)
    Lemma uninvolved_implies_deadline_met:
      ~~ scheduled_at sched j t1 ->
      ~~ scheduled_at sched j t2 ->
      job_meets_deadline sched' j.
    Proof.
      rewrite /scheduled_at => NOT_t1 NOT_t2.
      rewrite -service_invariant_implies_deadline_met; first by exact H_deadline_met.
      by apply: service_of_others_invariant.
    Qed.

    (** Next, we observe that a swap is unproblematic for the job scheduled at
       time t2. *)
    Lemma moved_earlier_implies_deadline_met:
      scheduled_at sched j t2 ->
      job_meets_deadline sched' j.
    Proof.
      move=> AT_t2.
      rewrite -service_invariant_implies_deadline_met; first by exact H_deadline_met.
      apply service_after_swap_invariant => //.
      by apply scheduled_at_implies_later_deadline with (sched0 := sched) => //.
    Qed.

    (** Finally, we observe is also unproblematic for the job that is
       moved to a later allocation. *)
    Lemma moved_later_implies_deadline_met:
      scheduled_at sched j t1 ->
      job_meets_deadline sched' j.
    Proof.
      move=> AT_t1.
      move: (H_no_idle_time_at_t2 j AT_t1) => [j2 [AT_t2 DL2]].
      move: (H_not_EDF j j2 AT_t1 AT_t2) => DL2_le_DL1.
      rewrite -service_invariant_implies_deadline_met; first by exact H_deadline_met.
      apply service_after_swap_invariant => //.
      apply ltn_leq_trans with (n := job_deadline j2) => //.
    Qed.

  End NoNewDeadlineMissesCases.

  (** From the above case analysis, we conclude that no deadline misses
     are introduced in the schedule obtained from swapping the
     allocations at times t1 and t2. *)
  Theorem edf_swap_no_deadline_misses_introduced:
    forall j, job_meets_deadline sched j -> job_meets_deadline sched' j.
  Proof.
    move=> j DL_MET.
    case: (boolP (scheduled_at sched j t1)) => AT_t1.
    - by apply moved_later_implies_deadline_met.
    - case (boolP (scheduled_at sched j t2)) => AT_t2.
      + by apply moved_earlier_implies_deadline_met.
      + by apply uninvolved_implies_deadline_met.
  Qed.

 End EDFSwap.
