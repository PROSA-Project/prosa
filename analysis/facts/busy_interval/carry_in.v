Require Export prosa.analysis.facts.model.workload.
Require Export prosa.analysis.facts.model.ideal.service_of_jobs.
Require Export prosa.analysis.facts.busy_interval.quiet_time.
Require Export prosa.analysis.facts.busy_interval.existence.
Require Export prosa.analysis.definitions.work_bearing_readiness.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.util.tactics.

(** * Busy Interval From Workload Bound *)

(** In the following, we derive an alternative condition for the existence of a
    busy interval based on the total workload. If the total workload generated
    by the task set is bounded, then there necessarily exists a moment without
    any carry-in workload, from which it follows that a busy interval has ended. *)
Section BusyIntervalExistence.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arr_seq : valid_arrival_sequence arr_seq.

  (** Allow for any fully-consuming uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.
  Hypothesis H_fully_consuming_proc_model : fully_consuming_proc_model PState.

  (** Next, consider any schedule of the arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume a given reflexive JLFP policy. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** Further, allow for any work-bearing notion of job readiness ... *)
  Context `{!JobReady Job PState}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ** Times without Carry-In *)

  (** As the first step, we derive a sufficient condition for the existence of a
      no-carry-in instant for uniprocessor for JLFP schedulers. *)

  (** We start by noting that, trivially, the processor has no carry-in at the
      beginning (i.e., has no carry-in at time instant [0]). *)
  Lemma no_carry_in_at_zero :
    no_carry_in arr_seq sched 0.
  Proof. by move=> j _ +; rewrite /arrived_before ltn0. Qed.

  (** Next, we relate idle times to the no-carry-in condition. First, the
      presence of a pending job implies that the processor isn't idle due to
      work-conservation. *)
  Lemma pending_job_not_idle :
    forall j t,
      arrives_in arr_seq j ->
      pending sched j t ->
      ~ is_idle arr_seq sched t.
  Proof.
    move=> j t ARR PEND IDLE.
    have [jhp [ARRhp [READYhp _]]] :
      exists j_hp : Job, arrives_in arr_seq j_hp /\ job_ready sched j_hp t /\ hep_job j_hp j
      by apply: H_job_ready.
    move: IDLE; rewrite is_idle_iff => /eqP; rewrite scheduled_job_at_none => // IDLE.
    have [j_other SCHED]:  exists j_other : Job, scheduled_at sched j_other t
      by apply: H_work_conserving ARRhp _; apply/andP.
    by move: (IDLE j_other) => /negP.
  Qed.

  (** Second, an idle time implies no carry in at this time instant. *)
  Lemma idle_instant_no_carry_in :
    forall t,
      is_idle arr_seq sched t ->
      no_carry_in arr_seq sched t.
  Proof.
    move=> t IDLE j ARR HA.
    apply/negPn/negP =>  NCOMP.
    apply: (pending_job_not_idle j t) => //.
    by apply/andP; split; rewrite // /has_arrived ltnW.
  Qed.

  (** Moreover, an idle time implies no carry in at the next time instant, too. *)
  Lemma idle_instant_next_no_carry_in :
    forall t,
      is_idle arr_seq sched t ->
      no_carry_in arr_seq sched t.+1.
  Proof.
    move=> t IDLE j ARR HA.
    apply/negPn/negP => NCOMP.
    apply: (pending_job_not_idle j t) => //.
    apply/andP; split; rewrite // /has_arrived.
    by apply: incompletion_monotonic NCOMP.
  Qed.

  (** ** Bounded-Workload Assumption *)

  (** We now introduce the central assumption from which we deduce the existence
      of a busy interval. *)

  (** To this end, recall the notion of the total service of all jobs within
      some time interval <<[t1, t2)>>. *)
  Let total_service t1 t2 :=
    service_of_jobs sched predT (arrivals_between arr_seq 0 t2) t1 t2.

  (** We assume that, for some positive [Δ], the sum of the total
      blackout and the total workload generated in any interval of
      length [Δ] starting with no carry-in is bounded by [Δ]. Note
      that this assumption bounds the total workload of jobs released
      in a time interval <<[t, t + Δ)>> regardless of their
      priorities. *)
  Variable Δ : duration.
  Hypothesis H_delta_positive : Δ > 0.
  Hypothesis H_workload_is_bounded :
    forall t,
      no_carry_in arr_seq sched t ->
      blackout_during sched t (t + Δ) + total_workload_between arr_seq t (t + Δ) <= Δ.

  (** In the following, we also require a unit-speed processor. *)
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

  (** ** Existence of a No-Carry-In Instant *)

  (** Next we prove that, if for any time instant [t] there is a point where the
      total workload generated since [t] is upper-bounded by the length of the
      interval, there must exist a no-carry-in instant. *)
  Section ProcessorIsNotTooBusy.

    (** As a stepping stone, we prove in the following section that for any time
        instant [t] there exists another time instant <<t' ∈ (t, t + Δ]>> such
        that the processor has no carry-in at time [t']. *)
    Section ProcessorIsNotTooBusyInduction.

      (** Consider an arbitrary time instant [t] ... *)
      Variable t : duration.

      (** ... such that there is no carry-in at time [t]. *)
      Hypothesis H_no_carry_in : no_carry_in arr_seq sched t.

      (** First, recall that the total service is bounded by the total
          workload. Therefore the sum of the total blackout and the
          total service of jobs in the interval <<[t, t + Δ)>> is
          bounded by [Δ]. *)
      Lemma total_service_is_bounded_by_Δ :
        blackout_during sched t (t + Δ) + total_service t (t + Δ) <= Δ.
      Proof.
        have EQ: \sum_(t <= x < t + Δ) 1 = Δ.
        { by rewrite big_const_nat iter_addn mul1n addn0 -{2}[t]addn0 subnDl subn0. }
        rewrite -{3}EQ {EQ}.
        rewrite /total_service /blackout_during /supply.blackout_during.
        rewrite /service_of_jobs/service_during/service_at exchange_big //=.
        rewrite -big_split //= leq_sum //; move => t' _.
        have [BL|SUP] := blackout_or_supply sched t'.
        { rewrite -[1]addn0; apply leq_add; first by case: (is_blackout).
          rewrite leqn0; apply/eqP; apply big1 => j _.
          eapply no_service_during_blackout in BL.
          by apply: BL. }
        { rewrite /is_blackout SUP add0n.
          exact: service_of_jobs_le_1. }
      Qed.

      (** Next we consider two cases:
          (1) The case when the sum of blackout and service is strictly less than [Δ], and
          (2) the case when the sum of blackout and service is equal to [Δ]. *)

      (** In the first case, we use the pigeonhole principle to
          conclude that there is an idle time instant; which in turn
          implies existence of a time instant with no carry-in. *)
      Lemma low_total_service_implies_existence_of_time_with_no_carry_in :
        blackout_during sched t (t + Δ) + total_service t (t + Δ) < Δ ->
        exists δ,
          δ < Δ /\ no_carry_in arr_seq sched (t.+1 + δ).
      Proof.
        rewrite /total_service-{3}[Δ]addn0 -{2}(subnn t) addnBA // [Δ + t]addnC => LTS.
        have [t_idle [/andP [LEt GTe] IDLE]]: exists t0 : nat,
                                                t <= t0 < t + Δ
                                                /\ is_idle arr_seq sched t0.
        { apply: low_service_implies_existence_of_idle_time_rs =>//.
          rewrite !subnKC in LTS; try by apply leq_addr.
          by rewrite addKn. }
        move: LEt; rewrite leq_eqVlt; move => /orP [/eqP EQ|LT].
        { exists 0; split => //.
          rewrite addn0 EQ => s ARR BEF.
          by apply: idle_instant_next_no_carry_in. }
        have EX: exists γ, t_idle = t + γ.
        { by exists (t_idle - t); rewrite subnKC // ltnW. }
        move: EX => [γ EQ].
        move : GTe LT; rewrite EQ ltn_add2l -{1}[t]addn0 ltn_add2l => GTe LT.
        exists (γ.-1); split.
        - apply leq_trans with γ.
          + by rewrite prednK.
          + by rewrite ltnW.
        - rewrite -subn1 -addn1 -addnA subnKC // => s ARR BEF.
          exact: idle_instant_no_carry_in.
      Qed.

      (** In the second case, the sum of blackout and service within
          the time interval <<[t, t + Δ)>> is equal to [Δ]. We also
          know that the total workload is lower-bounded by the total
          service and upper-bounded by [Δ]. Therefore, the total
          workload is equal to the total service, which implies
          completion of all jobs by time [t + Δ] and hence no carry-in
          at time [t + Δ]. *)
      Lemma completion_of_all_jobs_implies_no_carry_in :
        blackout_during sched t (t + Δ) + total_service t (t + Δ) = Δ ->
        no_carry_in arr_seq sched (t + Δ).
      Proof.
        rewrite /total_service => EQserv s ARR BEF.
        move: (H_workload_is_bounded t) => WORK.
        have EQ: total_workload_between arr_seq 0 (t + Δ)
                 = service_of_jobs sched predT (arrivals_between arr_seq 0 (t + Δ)) 0 (t + Δ);
          last exact: workload_eq_service_impl_all_jobs_have_completed.
        have CONSIST: consistent_arrival_times arr_seq by [].
        have COMPL := all_jobs_have_completed_impl_workload_eq_service
                        _ arr_seq CONSIST sched
                        H_jobs_must_arrive_to_execute
                        H_completed_jobs_dont_execute
                        predT 0 t t.
        feed_n 2 COMPL => //.
        { move=> j A B; apply: H_no_carry_in.
          - apply: in_arrivals_implies_arrived =>//.
          - by have : arrived_between j 0 t
                        by apply: (in_arrivals_implies_arrived_between arr_seq). }
        apply/eqP; rewrite eqn_leq; apply/andP; split;
          last by apply: service_of_jobs_le_workload.
        rewrite /total_workload_between/total_workload (workload_of_jobs_cat arr_seq t);
          last by apply/andP; split; [|rewrite leq_addr].
        - rewrite (service_of_jobs_cat_scheduling_interval _ _ _ _ _ _ _ t) //;
            last by apply/andP; split; [|rewrite leq_addr].
          + rewrite COMPL -addnA leq_add2l.
            rewrite -service_of_jobs_cat_arrival_interval;
              last by apply/andP; split; [|rewrite leq_addr].
            by evar (b : nat); rewrite -(leq_add2l b) EQserv.
      Qed.

    End ProcessorIsNotTooBusyInduction.

    (** Finally, we show that any interval of length [Δ] contains a time instant
        with no carry-in. *)
    Lemma processor_is_not_too_busy :
      forall t, exists δ,
        δ < Δ /\ no_carry_in arr_seq sched (t + δ).
    Proof.
      elim=> [|t [δ [LE FQT]]];
        first by exists 0; split; [ | rewrite addn0; apply: no_carry_in_at_zero].
      move: (posnP δ) => [Z|POS]; last first.
      - exists (δ.-1); split.
        + by apply: leq_trans LE; rewrite prednK.
        + by rewrite -subn1 -addn1 -addnA subnKC //.
      - move: FQT; rewrite Z addn0 => FQT {LE}.
        move: (total_service_is_bounded_by_Δ t); rewrite leq_eqVlt => /orP [/eqP EQ | LT].
        + exists (Δ.-1); split; first by rewrite prednK.
          rewrite addSn -subn1 -addn1 -addnA subnK //.
          by apply: completion_of_all_jobs_implies_no_carry_in.
        + by apply:low_total_service_implies_existence_of_time_with_no_carry_in.
    Qed.

  End ProcessorIsNotTooBusy.

  (** ** Busy Interval Existence *)

  (** Consider an arbitrary job [j] with positive cost. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** We show that there must exist a busy interval <<[t1, t2)>> that
      contains the arrival time of [j]. *)
  Theorem busy_interval_from_total_workload_bound :
    exists t1 t2,
      t1 <= job_arrival j < t2
      /\ t2 <= t1 + Δ
      /\ busy_interval arr_seq sched j t1 t2.
  Proof.
    rename H_from_arrival_sequence into ARR, H_job_cost_positive into POS.
    edestruct (exists_busy_interval_prefix
                 arr_seq H_valid_arr_seq
                 sched j ARR H_priority_is_reflexive (job_arrival j))
      as [t1 [PREFIX GE]]; first by apply: job_pending_at_arrival.
    move: GE => /andP [GE1 _].
    exists t1.
    have [δ [LE nCAR]]: exists δ : nat, δ < Δ /\ no_carry_in arr_seq sched (t1.+1 + δ)
      by apply: processor_is_not_too_busy => //.
    have QT : quiet_time arr_seq sched j (t1.+1 + δ) by apply: no_carry_in_implies_quiet_time.
    have EX: exists t2, ((t1 < t2 <= t1.+1 + δ) && quiet_time_dec arr_seq sched j t2).
    { exists (t1.+1 + δ); apply/andP; split.
      - by apply/andP; split; first rewrite addSn ltnS leq_addr.
      - exact/quiet_time_P. }
    move: (ex_minnP EX) => [t2 /andP [/andP [GTt2 LEt2] QUIET] MIN]; clear EX.
    have NEQ: t1 <= job_arrival j < t2.
    { apply/andP; split=> [//|].
      rewrite ltnNge; apply/negP => CONTR.
      have [_ [_ [NQT _]]] := PREFIX. 
      have {}NQT := NQT t2.
      feed NQT; first by (apply/andP; split; [|rewrite ltnS]).
      by apply: NQT; apply/quiet_time_P. }
    exists t2; split=> [//|]; split.
    { by apply: (leq_trans LEt2); rewrite addSn ltn_add2l. }
    { move: PREFIX => [_ [QTt1 [NQT _]]]; repeat split=> //; last by exact/quiet_time_P.
      move => t /andP [GEt LTt] QTt.
      feed (MIN t);
        last by move: LTt; rewrite ltnNge; move => /negP LTt; apply: LTt.
      apply/andP; split.
      + by apply/andP; split; last (apply leq_trans with t2; [apply ltnW |]).
      + exact/quiet_time_P. }
  Qed.

End BusyIntervalExistence.
