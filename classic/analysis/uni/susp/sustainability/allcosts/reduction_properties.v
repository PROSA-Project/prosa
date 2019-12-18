Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.valid_schedule
               prosa.classic.model.schedule.uni.susp.build_suspension_table
               prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.analysis.uni.susp.sustainability.allcosts.reduction.
Require Import prosa.classic.model.schedule.uni.transformation.construction.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we prove several properties about the schedule we constructed
   in the sustainability proof. *)
Module SustainabilityAllCostsProperties.

  Import ScheduleWithSuspensions Suspension Priority SuspensionIntervals
         PlatformWithSuspensions ResponseTime ScheduleConstruction
         SuspensionTableConstruction ValidSuspensionAwareSchedule.

  Module reduction := SustainabilityAllCosts.
  
  Section ReductionProperties.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (** Basic Setup & Setting*)
    
    (* Consider any job arrival sequence with consistent job arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    
    (* Assume any (schedule-independent) JLDP policy that is reflexive, transitive and total,
       i.e., that indicates "higher-or-equal priority". *)
    Variable higher_eq_priority: JLDP_policy Job.
    Hypothesis H_priority_is_reflexive: JLDP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: JLDP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: JLDP_is_total arr_seq higher_eq_priority.
    
    (* Next, consider any suspension-aware schedule of the arrival sequence... *)
    Variable sched_susp: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched_susp arr_seq.

    (* ...and the associated job suspension times. *)
    Variable job_suspension_duration: job_suspension Job.

    (* Assume that, in this schedule, jobs only execute after they arrive... *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched_susp.

    (* ...and no longer than their execution costs. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched_susp.

    (* Also assume that the schedule is work-conserving if there are non-suspended jobs, ... *)
    Hypothesis H_work_conserving:
      work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp.

    (* ...that the schedule respects job priorities... *)
    Hypothesis H_respects_priority:
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq
                           sched_susp higher_eq_priority.

    (* ...and that suspended jobs are not allowed to be scheduled. *)
    Hypothesis H_respects_self_suspensions:
      respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp.
    
    (** Reduction Setup *)

    (* Now we prove properties about the reduction.
       Let j be the job to be analyzed with arrival time arr_j. *)
    Variable j: Job.
    Let arr_j := job_arrival j.

    (* Suppose that we want to prove that the response time of job j in sched_susp
       is upper-bounded by some value R. This allows us to restrict our analysis
       to the finite scheduling window [0, arr_j + R) during the reduction. *)
    Variable R: time.

    (* Next, consider any job cost inflation... *)
    Variable inflated_job_cost: Job -> time.

    (* ...in which the cost of every job is no less than in the original schedule. *)
    Hypothesis H_job_costs_do_not_decrease:
      forall any_j, inflated_job_cost any_j >= job_cost any_j.

    (* Recall the schedule we constructed from sched_susp using these inflated costs. *)
    Let sched_new := reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority
                                         sched_susp inflated_job_cost j R.

    (* Also recall the predicate we defined for a suspended job in the new schedule... *)
    Let suspended_in_sched_new :=
      reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
                                 sched_susp job_suspension_duration inflated_job_cost j R.
    
    (* ...and the corresponding suspension table. *)
    Let reduced_suspension_duration :=
      reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
                                   sched_susp job_suspension_duration inflated_job_cost j R.
        
    (* For simplicity, let's define some local names. *)
    Let job_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_job job_arrival job_cost sched_susp.
    Let job_response_time_in_sched_new_bounded_by :=
      is_response_time_bound_of_job job_arrival inflated_job_cost sched_new.
    Let suspended_in_sched_susp :=
      suspended_at job_arrival job_cost job_suspension_duration sched_susp.
    Let job_is_late := reduction.job_is_late job_cost sched_susp inflated_job_cost sched_new.
    Let build_schedule := reduction.build_schedule job_arrival job_cost arr_seq higher_eq_priority
                                                   sched_susp inflated_job_cost j R.
    Let late_or_sched_jobs := reduction.jobs_that_are_late_or_scheduled_in_sched_susp
                                job_arrival job_cost arr_seq sched_susp inflated_job_cost sched_new.
    Let hp_job := reduction.highest_priority_job job_arrival arr_seq higher_eq_priority
                                                 inflated_job_cost sched_new.
    Let hp_late_job := reduction.highest_priority_late_job job_arrival job_cost arr_seq
                                       higher_eq_priority sched_susp inflated_job_cost sched_new.
    Let completed_in_sched_susp := completed_by job_cost sched_susp.
    Let completed_in_sched_new := completed_by inflated_job_cost sched_new.
    
    (** Properties of the Schedule Construction  *)

    (* In this section, we prove that the new schedule is equivalent to its construction function. *)
    Section PropertiesOfScheduleConstruction.

      (* By showing that the construction function depends only on the service, ... *)
      Lemma sched_new_depends_only_on_service:
        forall sched1 sched2 t,
          (forall j, service sched1 j t = service sched2 j t) ->
          build_schedule sched1 t = build_schedule sched2 t.
      Proof.
        intros sched1 sched2 t SAME.
        rewrite /build_schedule /reduction.build_schedule.
        case: (_ < _).
        {
          rewrite /reduction.highest_priority_late_job; f_equal.
          apply eq_in_filter; intros j0 IN0; f_equal;
          first by rewrite /pending /completed_by SAME.
          by f_equal; rewrite /reduction.job_is_late SAME.
        }
        {
          rewrite /reduction.highest_priority_job; f_equal.
          apply eq_in_filter; intros j0 IN0.
          by rewrite /pending /completed_by SAME.
        }
      Qed.

      (* ...we infer that the new schedule is equivalent to the construction function. *)
      Corollary sched_new_uses_construction_function:
        forall t,
          sched_new t = build_schedule sched_new t.
      Proof.
        by ins; apply service_dependent_schedule_construction,
                sched_new_depends_only_on_service.
      Qed.

    End PropertiesOfScheduleConstruction.

    (** Basic Properties of the Generated Schedule *)
      
    (* In this section, we prove some properties about the generated schedule that
       only depend on the construction function but not on suspension times. *)
    Section BasicScheduleProperties.

      (* First, we show that scheduled jobs come from the arrival sequence. *)
      Lemma sched_new_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched_new arr_seq.
      Proof.
        move => j0 t /eqP SCHEDn.
        rewrite /scheduled_at sched_new_uses_construction_function in SCHEDn.
        rewrite /build_schedule /reduction.build_schedule in SCHEDn.
        case (ltnP t (arr_j + R)) => [LT | GE].
        {
          rewrite LT /reduction.highest_priority_late_job in SCHEDn;
          apply seq_min_in_seq in SCHEDn.
          rewrite mem_filter in SCHEDn.
          move: SCHEDn => /andP [_ IN].
          by eapply in_arrivals_implies_arrived; eauto 1.
        }
        {
          rewrite ltnNge GE /= in SCHEDn.
          rewrite /reduction.highest_priority_job in SCHEDn; apply seq_min_in_seq in SCHEDn.
          rewrite mem_filter in SCHEDn.
          move: SCHEDn => /andP [_ IN].
          by eapply in_arrivals_implies_arrived; eauto 1.
        }
      Qed.

      (* Next, we show that jobs do not execute before their arrival times... *)
      Lemma sched_new_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched_new.
      Proof.
        move => j0 t /eqP SCHEDn.
        rewrite /scheduled_at sched_new_uses_construction_function in SCHEDn.
        rewrite /build_schedule /reduction.build_schedule in SCHEDn.
        case (ltnP t (arr_j + R)) => [LT | GE].
        {
          rewrite LT /reduction.highest_priority_late_job in SCHEDn;
          apply seq_min_in_seq in SCHEDn.
          rewrite mem_filter in SCHEDn.
          by move: SCHEDn => /andP [/andP [/andP [ARR _] _] _].
        }
        {
          rewrite ltnNge GE /= in SCHEDn.
          rewrite /reduction.highest_priority_job in SCHEDn; apply seq_min_in_seq in SCHEDn.
          rewrite mem_filter in SCHEDn.
          by move: SCHEDn => /andP [/andP [ARR _] _].
        }
      Qed.

      (* ...nor longer than their execution costs. *)
      Lemma sched_new_completed_jobs_dont_execute:
        completed_jobs_dont_execute inflated_job_cost sched_new.
      Proof.
        intros j0 t.
        induction t;
          first by rewrite /service /service_during big_geq //.
        rewrite /service /service_during big_nat_recr //=.
        rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LT]; last first.
        {
          apply: leq_trans LT; rewrite -addn1.
          by apply leq_add; last by apply leq_b1.
        }
        rewrite -[inflated_job_cost _]addn0; apply leq_add; first by rewrite -EQ.
        rewrite leqn0 eqb0 /scheduled_at.
        rewrite sched_new_uses_construction_function /build_schedule
                /reduction.build_schedule.
        case: (_ < _); rewrite /reduction.highest_priority_job
                               /reduction.highest_priority_late_job.
        { apply/eqP; intro SCHEDn.
          apply seq_min_in_seq in SCHEDn.
          rewrite mem_filter in SCHEDn.
          move: SCHEDn => /andP [/andP [/andP [_ NOTCOMP] _] _].
            by rewrite /completed_by EQ leqnn in NOTCOMP.
        }
        { apply/eqP; intro SCHEDn.
          apply seq_min_in_seq in SCHEDn.
          rewrite mem_filter in SCHEDn.
          move: SCHEDn => /andP [/andP [_ NOTCOMP] _].
            by rewrite /completed_by EQ leqnn in NOTCOMP.
        }
      Qed. 

    End BasicScheduleProperties.

    (** Service Invariants *)

    (* In this section, we prove some service invariants guaranteed by the new schedule
       up to time (arr_j + R).
       Note that these properties follow directly from the schedule construction and
       do not depend on suspension times. *)
    Section ServiceInvariant.

      (* Let t be any time in the interval [0, arr_j + R]. *)
      Variable t: time.
      Hypothesis H_before_R: t <= arr_j + R.

      (* By induction on time, we prove that for any job, the service received up to
         time t in the new schedule is no more than the service received up to time t in
         the original schedule, plus the difference between job costs due to inflation. *)
      Lemma sched_new_service_invariant:
        forall any_j,
          service sched_new any_j t
            <= service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j).
      Proof.
        rename H_priority_is_total into TOTAL, H_priority_is_transitive into TRANS,
               H_respects_priority into PRIO, H_work_conserving into WORK.
        rename t into t', H_before_R into BEFORE.
        move: t' BEFORE.
        induction t';
          first by intros _ j0; rewrite /service /service_during big_geq.
        intros LTr; feed IHt'; first by apply ltnW.
        intros j0.
        case (boolP (scheduled_at sched_new j0 t')) => [SCHEDn| NOTSCHEDn]; last first.
        {
          apply negbTE in NOTSCHEDn.
          rewrite /service /service_during big_nat_recr //=.
          rewrite /service_at NOTSCHEDn addn0.
          apply: (leq_trans (IHt' j0)).
          by rewrite leq_add2r extend_sum.
        }
        move: (SCHEDn) => IN.
        rewrite /scheduled_at sched_new_uses_construction_function in IN.
        rewrite /build_schedule /reduction.build_schedule LTr in IN; move: IN => /eqP IN.
        rewrite /reduction.highest_priority_late_job in IN.
        apply seq_min_in_seq in IN; rewrite mem_filter in IN.
        move: IN => /andP [/andP [PEND OR] IN].
        move: OR => /orP [LT | SCHEDs].
        {
          apply leq_trans with (n := service sched_new j0 t' + 1);
            first by rewrite /service/service_during big_nat_recr // leq_add ?leq_b1.
          rewrite addn1.
          by apply: (leq_trans LT); rewrite leq_add2r extend_sum.
        }
        {
          rewrite /service /service_during big_nat_recr // big_nat_recr //=.
          rewrite /service_at SCHEDn SCHEDs -addnA [1 + _]addnC addnA leq_add2r.
          by apply IHt'.
        }
      Qed.

      (* From the previous lemma, we conclude that any job that completes in the new
         schedule up to time t must have completed in the original schedule as well. *)
      Corollary sched_new_jobs_complete_later:
        forall any_j,
          completed_by inflated_job_cost sched_new any_j t ->
          completed_by job_cost sched_susp any_j t.
      Proof.
        intros j0 COMPn.
        unfold completed_by in *.
        rewrite -(leq_add2r (inflated_job_cost j0 - job_cost j0)).
        rewrite subnKC; last by eauto 1.
        apply leq_trans with (service sched_new j0 t); first by done.
          by apply sched_new_service_invariant.
      Qed.
      
    End ServiceInvariant.

    (** Properties of the Suspension Predicate *)
    
    (* In order to prove schedule properties that depend on suspension times, we first
       prove some facts about the suspension predicate we defined. *)
    Section SuspensionPredicate.

      (* Let any_j be any job. *)
      Variable any_j: Job.

      (* First, we show that if the suspension predicate holds for any_j at time t,
         then any_j must have arrived... *)
      Lemma suspended_in_sched_new_implies_arrived:
        forall t,
          suspended_in_sched_new any_j t -> has_arrived job_arrival any_j t.
      Proof.
        rename any_j into j0.
        move => t /andP [/andP [LT SUSPs] _].
        by eapply suspended_implies_arrived; eauto 1.
      Qed.

      (* ...and cannot have completed. *)
      Lemma suspended_in_sched_new_implies_not_completed:
        forall t,
          suspended_in_sched_new any_j t -> ~~ completed_in_sched_new any_j t.
      Proof.
        rename any_j into j0.
        move => t /andP [/andP [LT SUSPs] _].
        apply/negP; intro COMPn.
        apply suspended_implies_not_completed in SUSPs.
        apply sched_new_jobs_complete_later in COMPn; last by apply ltnW.
        by rewrite COMPn in SUSPs.
      Qed.

      (* Next, we show that if the suspension predicate changes from false at time t
         to true at time (t + 1), then any_j must be scheduled at time t. *)
      Lemma executes_before_suspension_in_sched_new:
        forall t,
          t < arr_j + R ->
          has_arrived job_arrival any_j t ->
          ~~ suspended_in_sched_new any_j t ->
          suspended_in_sched_new any_j t.+1 ->
          scheduled_at sched_new any_j t.
      Proof.
        rename any_j into j0.
        intros t LTr ARR NOTSUSPn SUSPn'.
        rewrite negb_and LTr /= negbK -/suspended_in_sched_susp -/job_is_late in NOTSUSPn.
        move: NOTSUSPn => /orP [NOTSUSPs | LATE]; last first.
        {
          apply contraT; intro NOTSCHEDn.
          move: SUSPn' => /andP [_ NOTLATE].
          rewrite /job_is_late /reduction.job_is_late -leqNgt -/sched_new in LATE NOTLATE.
          have GT: service sched_new j0 t < service sched_new j0 t.+1.
          {
            apply: (leq_trans LATE); apply: (leq_trans _ NOTLATE).
            by rewrite leq_add2r extend_sum.
          }
          rewrite /service/service_during big_nat_recr// -addn1 leq_add2l in GT.
          rewrite lt0n eqb0 negbK in GT.
          by rewrite GT in NOTSCHEDn.
        }
        move: (SUSPn') => /andP [/andP [_ SUSPs'] NOTLATE'].
        rewrite -/suspended_in_sched_susp in SUSPs'.
        rewrite /reduction.job_is_late -/sched_new -leqNgt in NOTLATE'.
        apply contraT; intro NOTSCHEDn.
        have SAME: service sched_new j0 t.+1 = service sched_new j0 t.
        {
          apply negbTE in NOTSCHEDn.
          by rewrite /service /service_during big_nat_recr //= /service_at NOTSCHEDn addn0.
        }
        rewrite SAME {SAME} in NOTLATE'.
        have INV := sched_new_service_invariant t (ltnW LTr) j0.
        have SCHEDs: ~~ scheduled_at sched_susp j0 t.
        {
          apply contraT; rewrite negbK; intro SCHEDs.
          have BUG: service sched_susp j0 t + 1 <= service sched_susp j0 t.
          {
            rewrite -(leq_add2r (inflated_job_cost j0 - job_cost j0)).
            apply: (leq_trans _ INV); apply: (leq_trans _ NOTLATE').
            rewrite leq_add2r.
            by rewrite /service /service_during big_nat_recr //= /service_at SCHEDs.
          }
          by rewrite addn1 ltnn in BUG.
        }
        suff BUG: scheduled_at sched_susp j0 t by rewrite BUG in SCHEDs.
        by eapply executes_before_suspension; eauto 1.
      Qed.

      (* For simplicity, let's call suspension_start the time following the last
         execution of a job. *)
      Let suspension_start := time_after_last_execution job_arrival.

      (* Then, we prove that if any_j is suspended at time t, it does not receive
         any service between time t and the previous beginning of suspension. *)
      Lemma suspended_in_sched_new_no_service_since_execution:
        forall t t_mid,
          suspended_in_sched_new any_j t ->
          suspension_start sched_new any_j t <= t_mid < t ->
          service sched_new any_j t <= service sched_new any_j t_mid.
      Proof.
        have BEFORE := executes_before_suspension_in_sched_new.
        rename any_j into j0.
        induction t; first by intros t_susp _; rewrite ltn0 andbF.
        move => t_mid SUSPn' /andP [GE LT].
        move: (SUSPn') => /andP [/andP [LTr' SUSPs'] _].
        have LTr: t < arr_j + R by apply: (ltn_trans _ LTr').
        have ARR: has_arrived job_arrival j0 t.+1.
          by apply suspended_implies_arrived in SUSPs'.
        rewrite /has_arrived leq_eqVlt in ARR; move: ARR => /orP [/eqP EQ | ARR].
        {
          rewrite /service /service_during.
          rewrite (cumulative_service_before_job_arrival_zero job_arrival) ?EQ //.
          by apply sched_new_jobs_must_arrive_to_execute.
        }
        case (boolP (scheduled_at sched_new j0 t)) => [SCHEDn | NOTSCHEDn]; last first.
        {
          apply leq_trans with (n := service sched_new j0 t).
          {
            apply negbTE in NOTSCHEDn; rewrite /service/service_during.
            by rewrite big_nat_recr //= /service_at NOTSCHEDn addn0.
          }
          case (boolP (t_mid == t)) => [/eqP EQ | DIFF]; first by subst.
          apply IHt.
          {
            apply contraT; intro NOTSUSPn.
            suff SCHEDn: scheduled_at sched_new j0 t by rewrite SCHEDn in NOTSCHEDn.
            by apply BEFORE.
          }
          apply/andP; split.
          {
            apply: (leq_trans _ GE); apply last_execution_monotonic; last by done.
            by apply sched_new_jobs_must_arrive_to_execute.
          }
          by rewrite ltn_neqAle -ltnS LT andbT.
        }
        set start := suspension_start sched_new.
        apply leq_trans with (n := service sched_new j0 (start j0 t.+1));
          last by apply extend_sum.
        apply extend_sum; first by done.
        rewrite /start /suspension_start /time_after_last_execution.
        have EX: [exists t0:'I_t.+1, scheduled_at sched_new j0 t0].
          by apply/existsP; exists (Ordinal (ltnSn t)).
        rewrite EX -addn1 leq_add2r addn1.
        have GEt := @leq_bigmax_cond _ (fun x:'I_t.+1 => scheduled_at sched_new j0 x)
                                        id (Ordinal (ltnSn t)).
        by apply GEt.
      Qed.

      (* Next, we prove that if the suspension predicate holds for any_j at time t,
         then the latest execution of any_j in the new schedule is no earlier than
         its latest execution in the original schedule. *)
      Lemma suspended_in_sched_new_suspension_starts_no_earlier:
        forall t,
          has_arrived job_arrival any_j t ->
          suspended_in_sched_new any_j t ->
          suspension_start sched_susp any_j t <= suspension_start sched_new any_j t.
      Proof.
        have BEFORE := executes_before_suspension_in_sched_new.
        rename any_j into j0.
        induction t.
        {
          intros ARR SUSPs; apply leq_trans with (n := 0); last by done.
          rewrite /suspension_start /time_after_last_execution.
          have NOTEX: [exists t0: 'I_0, scheduled_at sched_susp j0 t0] = false.
            by apply negbTE; rewrite negb_exists; apply/forallP; intros [x LT0].
          by rewrite NOTEX {NOTEX}.
        }
        {
          intros ARR SUSPn'.
          move: (SUSPn') => /andP [/andP [LTr _] _].
          have LTr': t < arr_j + R by apply: (ltn_trans _ LTr).
          rewrite /has_arrived leq_eqVlt in ARR; move: ARR => /orP [/eqP EQ | ARR].
          {
            have LAST := last_execution_after_arrival.
            rewrite /suspension_start /has_arrived in LAST *.
            apply leq_trans with (n := job_arrival j0);
              last by apply LAST, sched_new_jobs_must_arrive_to_execute.
            rewrite /time_after_last_execution.
            suff NOTEX: [exists t0: 'I_t.+1, scheduled_at sched_susp j0 t0] = false
              by rewrite NOTEX.
            apply negbTE; rewrite negb_exists; apply/forallP; intros t0.
            apply/negP; intro SCHED0.
            apply H_jobs_must_arrive_to_execute in SCHED0.
            suff BUG: t0 < t0 by rewrite ltnn in BUG.
            by apply: (leq_trans _ SCHED0); rewrite EQ.
          }
          rewrite ltnS in ARR.
          case (boolP (suspended_in_sched_new j0 t)) => [SUSPn | NOTSUSPn].
          {
            apply leq_trans with (n := suspension_start sched_new j0 t); last first.
            {
              apply last_execution_monotonic; last by done.
              by apply sched_new_jobs_must_arrive_to_execute.
            }
            apply leq_trans with (n := suspension_start sched_susp j0 t); [|by apply IHt].
            apply eq_leq, same_service_implies_same_last_execution.
            rewrite /service /service_during big_nat_recr //= /service_at.
            case (boolP (scheduled_at sched_susp j0 t)); last by rewrite addn0.
            intros SCHEDs; apply H_respects_self_suspensions in SCHEDs.
            by move: SUSPn => /andP [/andP [_ SUSPs] _].
          }
          move: (SUSPn') => /andP [/andP [_ SUSPs']] _.
          have SCHEDn := BEFORE t LTr' ARR NOTSUSPn SUSPn'.
          apply leq_trans with (n := t.+1);
            first by move: SUSPs' => /andP [_ /andP [LE _]].
          rewrite /suspension_start /time_after_last_execution.
          have EX: [exists t0:'I_t.+1, scheduled_at sched_new j0 t0].
            by apply/existsP; exists (Ordinal (ltnSn t)).
          rewrite EX -addn1 leq_add2r addn1.
          have GE := @leq_bigmax_cond _ (fun x:'I_t.+1 => scheduled_at sched_new j0 x)
                                        id (Ordinal (ltnSn t)).
          by apply GE.
        }
      Qed.

      (* using the previous lemmas, we conclude that the suspension predicate is continuous
         between any suspension point and the last execution of the job. *)
      Lemma suspended_in_sched_new_is_continuous:
        forall t t_mid,
          suspended_in_sched_new any_j t ->
          suspension_start sched_new any_j t <= t_mid < t ->
          suspended_in_sched_new any_j t_mid.
      Proof.
        have NOSERV := suspended_in_sched_new_no_service_since_execution.
        have NOEARLIER := suspended_in_sched_new_suspension_starts_no_earlier.
        rename any_j into j0; intros t.
        induction t_mid as [k IH] using strong_ind.
        have INV := sched_new_service_invariant.
        move => SUSPn /andP [GE LT].
        move: (SUSPn) => /andP [/andP [LTr SUSPt] NOTLATEt].
        rewrite -/job_is_late in NOTLATEt.
        apply/andP; split; last first.
        {
          rewrite /reduction.job_is_late -/sched_new -2!leqNgt in NOTLATEt *.
          feed (INV t); [by apply ltnW | specialize (INV j0)].
          set Sn := service sched_new in INV NOTLATEt *.
          set Ss := service sched_susp in INV NOTLATEt *.
          set cost0 := job_cost j0 in INV NOTLATEt *.
          set cost0' := inflated_job_cost j0 in INV NOTLATEt *.
          have SAME: Sn j0 t = Ss j0 t + (cost0' - cost0).
            by apply/eqP; rewrite eqn_leq; apply/andP.
          clear INV.
          apply leq_trans with (n := Ss j0 t + (cost0' - cost0));
            first by rewrite leq_add2r; apply extend_sum; last by apply ltnW.
          rewrite -SAME {SAME}.
          by apply NOSERV; rewrite ?SUSPn ?LTr ?SUSPt ?GE ?LT.
        }
        apply/andP; split; first by apply: (ltn_trans _ LTr).
        apply suspended_in_suspension_interval with (t0 := t); try done.
        {
          apply/negP; intro COMPmid.
          apply suspended_implies_not_completed in SUSPt.
          suff BUG: completed_by job_cost sched_susp j0 t by rewrite BUG in SUSPt.
            by apply completion_monotonic with (t0 := k); [ apply ltnW |].
        }
        apply/andP; split;
          last by apply: (ltn_trans LT); move: SUSPt => /andP [_ /andP [_ GTt]].
        apply: (leq_trans _ GE).
        apply NOEARLIER; try done.
        by apply suspended_implies_arrived in SUSPt.
      Qed. 

    End SuspensionPredicate.

    (** Properties of the Suspension Table *)

    (* In this section, we prove some properties about the suspension table. *)
    Section SuspensionTable.
      
      (* First, we show that no job ever suspends after (arr_j + R). *)
      Lemma suspended_in_sched_new_only_inside_window:
        forall any_j t,
          arr_j + R <= t ->
          ~~ suspended_at job_arrival inflated_job_cost reduced_suspension_duration
                          sched_new any_j t.
      Proof.
        intros any_j t LE.
        case (boolP (has_arrived job_arrival any_j t)) => [ARR | NOTARR]; last first.
        {
          apply/negP; intro SUSP.
          apply suspended_implies_arrived in SUSP;
            last by apply sched_new_jobs_must_arrive_to_execute.
          by rewrite SUSP in NOTARR.
        }
        apply suspension_duration_no_suspension_after_t_max; try done;
          first by apply sched_new_jobs_must_arrive_to_execute.
        intros j0 t0 LT.
        rewrite /reduction.suspended_in_sched_new LT /=.
        move => /andP [SUSPs _].
        by apply suspended_implies_arrived in SUSPs.
      Qed.

      (* Next, using the lemmas about the suspension predicate, we show that the suspension
         predicate for the new schedule matches the generated suspension table.
         (see model/schedule/uni/susp/build_suspension_table.v) *)
      Lemma sched_new_suspension_matches:
        forall any_j t,
          t < arr_j + R ->
          suspended_in_sched_new any_j t =
          suspended_at job_arrival inflated_job_cost reduced_suspension_duration sched_new any_j t.
      Proof.
        apply suspension_duration_matches_predicate_up_to_t_max;
          first by apply sched_new_jobs_must_arrive_to_execute.
        - by intros j0 t LT SUSP; apply suspended_in_sched_new_implies_arrived.
        - by intros j0 t LT SUSP; apply suspended_in_sched_new_implies_not_completed.
        - by intros j0 t LT SUSP; apply suspended_in_sched_new_is_continuous.
      Qed.
     
      (* Recall the definition of cumulative suspension in both schedules. *)
      Let cumulative_suspension_in_sched_susp :=
        cumulative_suspension job_arrival job_cost job_suspension_duration sched_susp.
      Let cumulative_suspension_in_sched_new :=
        cumulative_suspension job_arrival inflated_job_cost reduced_suspension_duration sched_new.

      (* To conclude, we prove that the cumulative suspension in the new schedule is no
         larger than in the original schedule,... *)
      Lemma sched_new_has_shorter_suspension:
        forall any_j t,
          cumulative_suspension_in_sched_new any_j t
          <= cumulative_suspension_in_sched_susp any_j t.
      Proof.
        intros j0 t.
        apply leq_sum; intros i _.
        case (ltnP i (arr_j + R)) => [LTr | GEr].
        {
          rewrite -sched_new_suspension_matches //.
          rewrite /suspended_in_sched_new /reduction.suspended_in_sched_new.
          rewrite LTr /=.
          by case: (X in (_ && X)); rewrite ?andbT ?andbF.
        }
        {
          apply leq_trans with (n := 0); last by done.
          rewrite leqn0 eqb0.
          case (boolP (has_arrived job_arrival j0 i)) => [ARR | NOTARR];
            first by apply suspended_in_sched_new_only_inside_window.
          apply/negP; intro SUSPn.
          apply suspended_implies_arrived in SUSPn; first by rewrite SUSPn in NOTARR.
          by apply sched_new_jobs_must_arrive_to_execute.
        }
      Qed.

      (* ... which implies that the total suspension is also no larger. *)
      Corollary sched_new_has_shorter_total_suspension:
        forall any_j,
          total_suspension inflated_job_cost reduced_suspension_duration any_j <=
          total_suspension job_cost job_suspension_duration any_j.
      Proof.
        intros any_j.
        apply leq_trans with (n := cumulative_suspension_in_sched_new any_j (arr_j + R)).
        {
          unfold total_suspension, reduced_suspension_duration, reduction.reduced_suspension_duration,
                 build_suspension_duration.
          rewrite -/sched_new.
          set SUSP_new := _ job_arrival job_cost _ _ _ _ _ _ _.
          set cost' := inflated_job_cost.
          set arr := job_arrival j.
          apply leq_trans with (n := \sum_(0 <= t < cost' any_j) \sum_(0 <= t0 < arr + R)
                              if (service sched_new any_j t0 == t) then SUSP_new any_j t0 else false);
            first by apply leq_sum; ins; rewrite big_mkcond; apply leq_sum; ins; case: (_ == _).
          rewrite exchange_big /=.
          apply leq_sum_nat; move => i /= LT _.
          case COMP: (completed_in_sched_new any_j i).
          { apply leq_trans with 0; last by done.
            rewrite big_nat_cond big1 //; move => s /= LTs.
            case EQ: (_ == _); last by done.
            move: EQ => /eqP EQ; rewrite andbT -EQ {EQ} in LTs.
              by exfalso; move: LTs; rewrite ltnNge; move => /negP LTs; apply: LTs.
          }
          { apply negbT in COMP; rewrite -ltnNge in COMP.
            set s := service sched_new any_j i; rewrite -/s in COMP.
            rewrite -> big_cat_nat with (n := s); [simpl | by done | by apply ltnW].
            rewrite -> big_cat_nat with (m := s) (n := s.+1); [simpl | by done | by done].
            rewrite big_nat_cond big1; last first.
            {
              move => i0; rewrite andbT; move => /= LT0.
              by case EQ: (_ == _) => //; move: EQ => /eqP EQ; subst; rewrite ltnn in LT0.
            }
            rewrite add0n big_nat_recr //= eq_refl big_geq // add0n.
            rewrite big_nat_cond big1; [rewrite addn0 |]; last first.
            {
              move => i0; rewrite andbT; move => /andP [LT0 _].
              rewrite ltn_neqAle in LT0; move: LT0 => /andP [NEQ _].
              by apply negbTE in NEQ; rewrite NEQ.
            }
            by rewrite -sched_new_suspension_matches.
          }
        }
        apply leq_trans with (n := cumulative_suspension_in_sched_susp any_j (arr_j + R));
          first by apply sched_new_has_shorter_suspension.
        by apply cumulative_suspension_le_total_suspension.
      Qed.
      
    End SuspensionTable.

    (** Suspension-Related Schedule Properties *)

    (* Having shown that the suspension table matches the suspension predicate,
       we now analyze the suspension predicate and prove that the generated
       schedule satisfies all the remaining properties. *)
    Section AdditionalScheduleProperties.
    
      (* First, we show that the new schedule respects self-suspensions. *)
      Lemma sched_new_respects_self_suspensions:
        respects_self_suspensions job_arrival inflated_job_cost reduced_suspension_duration sched_new.
      Proof.
        move => j0 t /eqP SCHEDn; apply/negP.
        case (ltnP t (arr_j + R)) => [LTr | GEr];
          last by apply suspended_in_sched_new_only_inside_window.
        rewrite -sched_new_suspension_matches /suspended_in_sched_new //.
        rewrite negb_and negbK.
        rewrite /scheduled_at sched_new_uses_construction_function in SCHEDn.
        rewrite /build_schedule /reduction.build_schedule in SCHEDn.
        case (ltnP t (arr_j + R)) => [LT | GE]; last by rewrite ltnNge GE.
        rewrite LT /reduction.highest_priority_late_job in SCHEDn.
        apply seq_min_in_seq in SCHEDn.
        rewrite mem_filter in SCHEDn.
        move: SCHEDn => /andP [/andP [PEND OR] _].
        move: OR => /orP [SERV | SCHED]; first by rewrite SERV orbT.
        apply/orP; left.
        rewrite negb_and; apply/orP; right.
        by apply/negP; apply H_respects_self_suspensions.
      Qed.

      (* Next, we prove that the new schedule is (suspension-aware) work-conserving... *)
      Lemma sched_new_work_conserving:
        work_conserving job_arrival inflated_job_cost reduced_suspension_duration
                        arr_seq sched_new.
      Proof.
        have COMPnew := sched_new_completed_jobs_dont_execute.
        have MATCH := sched_new_suspension_matches.
        rename H_work_conserving into WORKs, H_respects_priority into PRIOs.
        intros j0 t IN BACK.
        move: BACK => /andP [/andP[PEND NOTSCHED] NOTSUSP].
        rewrite /scheduled_at sched_new_uses_construction_function in NOTSCHED *.
        rewrite /build_schedule /reduction.build_schedule in NOTSCHED *.
        case: (ltnP t (arr_j + R)) => [BEFORE | AFTER]; last first.
        {
          clear NOTSUSP; rewrite ltnNge AFTER /= in NOTSCHED.
          rewrite -/hp_job in NOTSCHED *.
          destruct (hp_job t) eqn:SCHEDn; first by exists s.
          exfalso; clear NOTSCHED.
          suff NOTNONE: hp_job t != None by rewrite SCHEDn in NOTNONE.
          move: (PEND) => /andP [ARR NOTCOMPn].
          have IN0: j0 \in jobs_arrived_up_to arr_seq t.
            by eapply arrived_between_implies_in_arrivals; eauto 1.
          apply seq_min_exists with (x := j0).
          by rewrite mem_filter PEND IN0.
        }
        rewrite -MATCH // in NOTSUSP.
        rewrite /suspended_in_sched_new negb_and negbK in NOTSUSP.
        rewrite BEFORE /= in NOTSUSP NOTSCHED.
        rewrite -/hp_late_job in NOTSCHED *.
        destruct (hp_late_job t) eqn:SCHEDn; first by exists s.
        exfalso; clear NOTSCHED.
        suff NOTNONE: hp_late_job t != None by rewrite SCHEDn in NOTNONE.
        move: (PEND) => /andP [ARR NOTCOMPn].
        have IN0: j0 \in jobs_arrived_up_to arr_seq t.
          by eapply arrived_between_implies_in_arrivals; eauto 1.
        move: NOTSUSP => /orP [NOTSUSPs | LT]; last first.
        { clear SCHEDn; apply seq_min_exists with (x := j0).
            by rewrite mem_filter PEND IN0 andbT LT.
        }
        case (boolP (completed_by job_cost sched_susp j0 t)) => [COMPs | NOTCOMPs].
        { clear SCHEDn; apply seq_min_exists with (x := j0).
          rewrite mem_filter PEND IN0 andbT /=.
          apply/orP; left.
          apply leq_trans with (n := job_cost j0 + (inflated_job_cost j0 - job_cost j0));
            last by rewrite leq_add2r.
          rewrite subnKC; last by apply H_job_costs_do_not_decrease.
            by rewrite ltnNge.
        }
        case (boolP (scheduled_at sched_susp j0 t)) => [SCHEDs | NOTSCHEDs].
        { clear SCHEDn; apply seq_min_exists with (x := j0).
          by rewrite mem_filter PEND IN0 andbT SCHEDs orbT.
        }
        feed (WORKs j0 t IN); first by repeat (apply/andP; split).
        move: WORKs => [j_hp SCHEDhp].
        clear SCHEDn; apply seq_min_exists with (x := j_hp).
        have ARRhp: has_arrived job_arrival j_hp t.
          by apply H_jobs_must_arrive_to_execute.
        have ARRINhp: arrives_in arr_seq j_hp.
          by eapply H_jobs_come_from_arrival_sequence; eauto 1.
        have INhp: j_hp \in jobs_arrived_up_to arr_seq t.
          by eapply arrived_between_implies_in_arrivals; eauto 1.
        rewrite mem_filter INhp andbT SCHEDhp orbT andbT.
        apply/andP; split; first by done.
        apply contraT; rewrite negbK; intro COMPhpN.
        have COMPhpS: completed_by job_cost sched_susp j_hp t.
          by apply sched_new_jobs_complete_later; first by apply ltnW.
        by apply completed_implies_not_scheduled in COMPhpS;
          first by rewrite SCHEDhp in COMPhpS.
      Qed.

      (* ...and respects job priorities. *)
      Lemma sched_new_respects_policy:
        respects_JLDP_policy job_arrival inflated_job_cost reduced_suspension_duration
                             arr_seq sched_new higher_eq_priority.
      Proof.
        have MATCH := sched_new_suspension_matches.
        rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL,
               H_priority_is_reflexive into REFL, H_work_conserving into WORKs,
               H_respects_priority into PRIOs.
        move => j1 j2 t ARRin BACK /eqP SCHED.
        move: BACK => /andP [/andP [PEND NOTSCHED] NOTSUSPn].
        rewrite /scheduled_at sched_new_uses_construction_function /build_schedule
                /reduction.build_schedule in SCHED NOTSCHED *.
        case: (ltnP t (arr_j + R)) => [BEFORE | AFTER]; last first.
        {
          rewrite ltnNge AFTER /= in SCHED NOTSCHED.
          rewrite /reduction.highest_priority_job in SCHED NOTSCHED.
          set jobs := reduction.pending_jobs _ _ _ _ _ in SCHED NOTSCHED.
          have IN: j1 \in jobs.
          {
            rewrite mem_filter PEND /=.
            move: PEND => /andP [ARR _].
            by eapply arrived_between_implies_in_arrivals; eauto 1.
          }
          apply seq_min_computes_min with (y := j1) in SCHED; try (by done).
          by intros x y; rewrite 2!mem_filter; move => /andP [_ INx] /andP [_ INy];
            apply TOTAL; eapply in_arrivals_implies_arrived; eauto 2.
        }
        rewrite BEFORE in SCHED NOTSCHED.
        rewrite /reduction.highest_priority_late_job in SCHED NOTSCHED.
        set jobs := _ sched_new t in SCHED NOTSCHED.
        rewrite -MATCH // negb_and negbK in NOTSUSPn.
        have TOT: forall x y, x \in jobs -> y \in jobs ->
                      higher_eq_priority t x y || higher_eq_priority t y x.
        {
          intros x y INx INy; rewrite 2!mem_filter in INx INy.
          move: INx INy => /andP [_ INx] /andP [_ INy].
          by apply TOTAL; eapply in_arrivals_implies_arrived; eauto 1.
        }
        have ARR1: has_arrived job_arrival j1 t by move: PEND => /andP [ARR _].
        have IN1: j1 \in jobs_arrived_up_to arr_seq t.
          by eapply arrived_between_implies_in_arrivals; eauto 1.
        move: NOTSUSPn => /orP [NOTSUSPs | LT]; last first.
        {
          apply seq_min_computes_min with (l := jobs); try done.
          by rewrite mem_filter IN1 andbT PEND LT.
        }
        rewrite BEFORE /= in NOTSUSPs.
        case (boolP (scheduled_at sched_susp j1 t)) => [SCHEDs | NOTSCHEDs].
        { 
          apply seq_min_computes_min with (l := jobs); try done.
          by rewrite mem_filter IN1 andbT PEND SCHEDs orbT.
        }
        case (boolP (completed_by job_cost sched_susp j1 t)) => [COMPs | NOTCOMPs].
        { 
          apply seq_min_computes_min with (l := jobs); try (by done).
          rewrite mem_filter PEND /= IN1 andbT.
          apply/orP; left.
          rewrite /reduction.job_is_late.
          apply leq_trans with (job_cost j1 + (inflated_job_cost j1 - job_cost j1)); last by rewrite leq_add2r.
          rewrite subnKC; last by eauto 1.            
          move: PEND => /andP [_ NOTCOMP].
            by rewrite ltnNge.
        }
        feed (WORKs j1 t ARRin); first by repeat (apply/andP; split).
        move: WORKs => [j_hp SCHEDhp].
        apply: (TRANS _ j_hp);
          last by apply PRIOs; try done; repeat (apply/andP; split).
        have ARRhp: has_arrived job_arrival j_hp t.
          by apply H_jobs_must_arrive_to_execute.
        have ARRINhp: arrives_in arr_seq j_hp.
          by eapply H_jobs_come_from_arrival_sequence; eauto 1.
        have INhp: j_hp \in jobs_arrived_up_to arr_seq t.
          by eapply arrived_between_implies_in_arrivals; eauto 1.
        apply seq_min_computes_min with (l := jobs); try done.
        rewrite mem_filter INhp andbT SCHEDhp orbT andbT.
        apply/andP; split; first by done.
        apply contraT; rewrite negbK; intro COMPhpN.
        have COMPhpS: completed_by job_cost sched_susp j_hp t.
          by apply sched_new_jobs_complete_later; first by apply ltnW.
        by apply completed_implies_not_scheduled in COMPhpS;
          first by rewrite SCHEDhp in COMPhpS.
      Qed.

    End AdditionalScheduleProperties.

    (** Final Remarks *)

    Section FinalRemarks.

      (* To summarize, we conclude that the new schedule is a valid suspension-aware schedule ...  *)
      Remark sched_new_is_valid:
        valid_suspension_aware_schedule job_arrival arr_seq higher_eq_priority
                                  reduced_suspension_duration inflated_job_cost sched_new.
      Proof.
        repeat split.
        - by apply sched_new_jobs_come_from_arrival_sequence.
        - by apply sched_new_jobs_must_arrive_to_execute.
        - by apply sched_new_completed_jobs_dont_execute.
        - by apply sched_new_work_conserving.
        - by apply sched_new_respects_policy.
        - by apply sched_new_respects_self_suspensions.
      Qed.

      (* ...and that if the analyzed job j has response-time bound R in the schedule,
         then it also has response-time bound R in the original schedule. *)
      Remark sched_new_response_time_of_job_j:
        job_response_time_in_sched_new_bounded_by j R ->
        job_response_time_in_sched_susp_bounded_by j R.
      Proof.
        by apply sched_new_jobs_complete_later.
      Qed.
     
    End FinalRemarks.
    
  End ReductionProperties.
  
End SustainabilityAllCostsProperties.
