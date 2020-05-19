Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction.
Require Import prosa.classic.model.schedule.uni.transformation.construction.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we prove that the in the generated suspension-aware schedule, 
   the response time of the job whose cost is inflated does not decrease. *)
Module SustainabilitySingleCostProperties.

  Import ScheduleWithSuspensions Suspension Priority SuspensionIntervals
         PlatformWithSuspensions ResponseTime ScheduleConstruction.

  Module reduction := SustainabilitySingleCost.
  
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

    (* Now we prove properties about the reduction. Let j be any job. *)
    Variable j: Job.
    Let arr_j := job_arrival j.

    (* Next, consider any job cost inflation... *)
    Variable inflated_job_cost: Job -> time.

    (* ...that does not decrease the cost of job j... *)
    Hypothesis H_cost_of_j_does_not_decrease: inflated_job_cost j >= job_cost j.

    (* ...and that preserves the cost of the remaining jobs. *)
    Hypothesis H_inflation_only_for_job_j:
      forall any_j,
        any_j != j ->
        inflated_job_cost any_j = job_cost any_j.

    (* Recall the schedule we constructed from sched_susp by inflating the cost of job j. *)
    Let sched_susp_highercost := reduction.sched_susp_highercost job_arrival arr_seq higher_eq_priority
                                                  sched_susp job_suspension_duration inflated_job_cost.
        
    (* For simplicity, we define some local names for the definitions related to both schedules. *)
    Let job_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_job job_arrival job_cost sched_susp.
    Let job_response_time_in_sched_susp_highercost_bounded_by :=
      is_response_time_bound_of_job job_arrival inflated_job_cost sched_susp_highercost.
    Let ready_jobs := reduction.ready_jobs job_arrival arr_seq job_suspension_duration
                                           inflated_job_cost sched_susp_highercost.
    Let hp_job := reduction.highest_priority_job job_arrival arr_seq higher_eq_priority
                                   job_suspension_duration inflated_job_cost sched_susp_highercost.
    Let completed_in_sched_susp := completed_by job_cost sched_susp.
    Let completed_in_sched_susp_highercost := completed_by inflated_job_cost sched_susp_highercost.
    Let suspended_in_sched_susp :=
      suspended_at job_arrival job_cost job_suspension_duration sched_susp.
    Let suspended_in_sched_susp_highercost :=
      suspended_at job_arrival inflated_job_cost job_suspension_duration sched_susp_highercost.
    Let service_in_sched_susp := service sched_susp.
    Let service_in_sched_susp_highercost := service sched_susp_highercost.
    
    (** Properties of the Schedule Construction  *)

    (* In this section, we prove that the new schedule uses its construction function. *)
    Section PropertiesOfScheduleConstruction.

      (* Recall the construction function of the new schedule. *)
      Let build_schedule := reduction.build_schedule job_arrival arr_seq higher_eq_priority
                                               sched_susp job_suspension_duration inflated_job_cost.
      
      (* By showing that the construction function depends only on the schedule prefix, ... *)
      Lemma sched_susp_highercost_depends_only_on_prefix:
        forall sched1 sched2 t,
          (forall t0, t0 < t -> sched1 t0 = sched2 t0) ->
          build_schedule sched1 t = build_schedule sched2 t.
      Proof.
        intros sched1 sched2 t ALL.
        rewrite /build_schedule /reduction.build_schedule /reduction.highest_priority_job.
        have COMP: forall j, completed_by inflated_job_cost sched1 j t =
                             completed_by inflated_job_cost sched2 j t.
        {
          intros j0; rewrite /completed_by; f_equal.
          apply eq_big_nat; move => i /= LTi.
          by rewrite /service_at /scheduled_at ALL.
        }
        set pend1 := pending _ _ sched1.
        set pend2 := pending _ _ sched2.
        set susp1 := suspended_at _ _ _ sched1.
        set susp2 := suspended_at _ _ _ sched2.
        have SAME: forall j, pend1 j t = pend2 j t.
        {
          intros j0; rewrite /pend1 /pend2 /pending.
          by case: has_arrived => //=; rewrite COMP.
        }
        set readyjobs := reduction.ready_jobs _ _ _ _.
        have EX: forall j0, [exists t0: 'I_t, scheduled_at sched1 j0 t0] =
                            [exists t0: 'I_t, scheduled_at sched2 j0 t0].
        {
          intros j0; apply/idP/idP.
          - by move => /existsP [t0 SCHED]; apply/existsP; exists t0; rewrite /scheduled_at -ALL.
          - by move => /existsP [t0 SCHED]; apply/existsP; exists t0; rewrite /scheduled_at ALL.
        }
        have BEG: forall j0, time_after_last_execution job_arrival sched1 j0 t =
                             time_after_last_execution job_arrival sched2 j0 t.
        {
          intros j0; rewrite /time_after_last_execution EX.
          case: ifP => _; last by done.
          by f_equal; apply eq_bigl; intros t0; rewrite /scheduled_at ALL.
        }
        have SUSP: forall j0, has_arrived job_arrival j0 t ->
                              suspension_duration job_arrival job_suspension_duration sched1 j0 t =
                              suspension_duration job_arrival job_suspension_duration sched2 j0 t.
        {
          intros j0 ARR0; rewrite /suspension_duration BEG; f_equal.
          rewrite /service /service_during big_nat_cond [in RHS]big_nat_cond.
          apply congr_big; try (by done).
          move => i /= /andP [LTi _].
          rewrite /service_at /scheduled_at ALL //.
          apply: (leq_trans LTi).
          by apply last_execution_bounded_by_identity.
        }        
        have SAMEsusp: forall j0, has_arrived job_arrival j0 t -> susp1 j0 t = susp2 j0 t.
          by intros j0 ARR0; rewrite /susp1 /susp2 /suspended_at COMP BEG SUSP.
        have SAMEready: readyjobs sched1 t = readyjobs sched2 t.
        {
          apply eq_in_filter; intros j0 IN.
          rewrite -/pend1 -/pend2 SAME; f_equal.
          rewrite /suspended_at COMP BEG SUSP; first by done.
          by rewrite /has_arrived -ltnS; eapply in_arrivals_implies_arrived_before; eauto 1.
        }
        rewrite SAMEready; desf; try (by done); rewrite SAME SAMEsusp in Heq1; try (by done);
        by apply H_jobs_must_arrive_to_execute; apply/eqP.
      Qed.

      (* ...we infer that the new schedule is indeed based on the construction function. *)
      Corollary sched_susp_highercost_uses_construction_function:
        forall t,
          sched_susp_highercost t = build_schedule sched_susp_highercost t.
      Proof.
        by ins; apply prefix_dependent_schedule_construction,
                      sched_susp_highercost_depends_only_on_prefix.
      Qed.

    End PropertiesOfScheduleConstruction.

    (** Basic Properties of the Generated Schedule *)
      
    (* In this section, we prove that sched_susp_highercost is a valid suspension-aware schedule. *)
    Section ScheduleIsValid.

      (* First, we show that scheduled jobs come from the arrival sequence. *)
      Lemma sched_susp_highercost_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched_susp_highercost arr_seq.
      Proof.
        rename H_jobs_come_from_arrival_sequence into FROM.
        move => j0 t /eqP SCHED.
        rewrite sched_susp_highercost_uses_construction_function /reduction.build_schedule
                -/hp_job in SCHED.
        destruct (hp_job t) as [j_hp|] eqn:HP; last by done.
        have IN: j_hp \in ready_jobs t.
          by rewrite /hp_job /reduction.highest_priority_job in HP; apply seq_min_in_seq in HP.
        have ARRhp: arrives_in arr_seq j_hp.
        {
          rewrite mem_filter in IN; move: IN => /andP [/andP _ IN].
          by apply in_arrivals_implies_arrived in IN.
        }
        destruct (sched_susp t) eqn:SCHEDs; last by case: SCHED => SAME; subst.
        move: SCHEDs => /eqP SCHEDs; apply FROM in SCHEDs.
        case: ifP SCHED; first by move => /andP [PEND _]; case => <-.
        by move => NOTPEND; case => <-.
      Qed.

      (* Next, we show that jobs do not execute before their arrival times... *)
      Lemma sched_susp_highercost_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched_susp_highercost.
      Proof.
        have FUNC := sched_susp_highercost_uses_construction_function.
        rename H_jobs_must_arrive_to_execute into MUST.
        move => j0 t /eqP SCHED.
        rewrite FUNC /reduction.build_schedule -/hp_job in SCHED.
        destruct (hp_job t) as [j_hp|] eqn:HP; last by done.
        have IN: j_hp \in ready_jobs t.
          by rewrite /hp_job /reduction.highest_priority_job in HP; apply seq_min_in_seq in HP.
        have ARRhp: has_arrived job_arrival j_hp t.
        {
          rewrite mem_filter in IN; move: IN => /andP [/andP _ IN].
          by eapply in_arrivals_implies_arrived_before in IN; eauto.
        }
        destruct (sched_susp t) eqn:SCHEDs; last by case: SCHED => SAME; subst.
        case: ifP SCHED;
          first by move => /andP [PEND _]; case => <-; apply MUST; apply/eqP.
        by move => NOTPEND; case => <-.
      Qed.

      (* ...nor longer than their execution costs. *)
      Lemma sched_susp_highercost_completed_jobs_dont_execute:
        completed_jobs_dont_execute inflated_job_cost sched_susp_highercost.
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
        rewrite sched_susp_highercost_uses_construction_function /reduction.build_schedule
                -/hp_job.
        destruct (hp_job t) as [j_hp|] eqn:HP; last by done.
        have IN: j_hp \in ready_jobs t.
          by rewrite /hp_job /reduction.highest_priority_job in HP; apply seq_min_in_seq in HP.
        have PENDhp: pending job_arrival inflated_job_cost sched_susp_highercost j_hp t. 
        {
          rewrite mem_filter in IN; move: IN => /andP [/andP [PEND _] IN].
          by eapply in_arrivals_implies_arrived_before in IN; eauto.
        }
        destruct (sched_susp t) eqn:SCHEDs; last first.
        { apply/eqP; case => SAME; subst j0.
          suff NOTPEND: ~~ pending job_arrival inflated_job_cost sched_susp_highercost j_hp t.
          - by rewrite PENDhp in NOTPEND.
          - by rewrite /pending negb_and; apply/orP; right; rewrite negbK /completed_by EQ.
        }
        { case: ifP => [PEND | NOTPEND]; apply/eqP; case => SAME; subst j0;
            last by move: PENDhp => /andP [_ NC]; rewrite /completed_by EQ leqnn in NC.
          move: PEND => /andP [/andP [/andP [_ NC] _] _].
          by rewrite /completed_by EQ leqnn in NC.
        }
      Qed.

      (* In addition, we prove that the new schedule is work-conserving,... *)
      Lemma sched_susp_highercost_work_conserving:
        work_conserving job_arrival inflated_job_cost job_suspension_duration
                        arr_seq sched_susp_highercost.
      Proof.
        intros j0 t IN BACK.
        move: BACK => /andP [/andP[PEND NOTSCHED] NOTSUSP].
        rewrite /scheduled_at sched_susp_highercost_uses_construction_function
                /reduction.build_schedule -/hp_job in NOTSCHED *.
        destruct (hp_job) as [j_hp|] eqn:HP.
        {
          destruct (sched_susp t) eqn:SCHEDs; last by exists j_hp.
          by case: ifP; intros _; [exists s | exists j_hp].
        }
        {
          have IN0: j0 \in ready_jobs t.
          {
            rewrite mem_filter PEND NOTSUSP /=.
            eapply arrived_between_implies_in_arrivals; eauto 1.
            by move: PEND => /andP [ARR _].
          }
          suff NOTNONE: hp_job t != None by rewrite HP in NOTNONE.
          by apply seq_min_exists with (x := j0).
        }
      Qed.

      (* ...respects job priorities, ... *)
      Lemma sched_susp_highercost_respects_policy:
        respects_JLDP_policy job_arrival inflated_job_cost job_suspension_duration
                             arr_seq sched_susp_highercost higher_eq_priority.
      Proof.
        rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL,
               H_priority_is_reflexive into REFL.
        move => j1 j2 t IN BACK /eqP SCHED.
        move: BACK => /andP [/andP [PEND NOTSCHED] NOTSUSP].
        rewrite /scheduled_at sched_susp_highercost_uses_construction_function /reduction.build_schedule
                -/hp_job in SCHED NOTSCHED *.
        set pend := pending _ _ _ in SCHED NOTSCHED.
        have ALL: forall j_hi j_lo, hp_job t = Some j_hi ->
                                    j_lo \in ready_jobs t ->
                                    higher_eq_priority t j_hi j_lo.
        {
          intros j_hi j_lo SOME INlo; move: SCHED => MIN.
          rewrite /hp_job /reduction.highest_priority_job in SOME.
          apply seq_min_computes_min with (y := j_lo) in SOME; try (by done). 
          intros x y; rewrite mem_filter [y \in _]mem_filter /jobs_arrived_up_to.
          move => /andP [_ INx] /andP [_ INy].
          by apply TOTAL; eapply in_arrivals_implies_arrived; eauto 1.
        }
        destruct (hp_job t) as [j_hp |] eqn:HP; last by done.
        have HIGHER: higher_eq_priority t j_hp j1.
        {
          apply ALL; first by done.
          move: PEND => /andP [ARR NOTCOMP].
          rewrite mem_filter /pending ARR NOTCOMP NOTSUSP /=.
          by eapply arrived_between_implies_in_arrivals; eauto 1.
        }
        destruct (sched_susp t) eqn:SCHEDs; last by case: SCHED => SAME; subst j2. 
        move: SCHED; case: ifP => [/andP[ PENDs HPs] | NOTPENDs]; case => SAME; subst;
          first by apply (TRANS t (j_hp)).
        apply ALL; first by done.
        move: PEND => /andP [ARR NOTCOMP].
        rewrite mem_filter /pending ARR NOTCOMP NOTSUSP /=.
        by eapply arrived_between_implies_in_arrivals; eauto 1.
      Qed.

      (* ...and does not allow suspended jobs to be scheduled. *)
      Lemma sched_susp_highercost_respects_self_suspensions:
        respects_self_suspensions job_arrival inflated_job_cost
                                  job_suspension_duration sched_susp_highercost.
      Proof.
        rename H_respects_self_suspensions into SELF.
        move => j0 t /eqP SCHED SUSP.
        set suspended := suspended_at _ _ _ _ in SUSP. 
        rewrite sched_susp_highercost_uses_construction_function /reduction.build_schedule
                -/hp_job in SCHED.
        destruct (hp_job t) as [j_hp|] eqn:HP; last by done.
        have IN: j_hp \in ready_jobs t.
          by rewrite /hp_job /reduction.highest_priority_job in HP; apply seq_min_in_seq in HP.
        have NOTSUSP: ~~ suspended j_hp t.
        {
          by rewrite mem_filter in IN; move: IN => /andP [/andP [_ NOTs] _].
        }
        destruct (sched_susp t) eqn:SCHEDs;
          last by case: SCHED => SAME; subst; rewrite SUSP in NOTSUSP.
        case: ifP SCHED; last by move => _; case => SAME; subst; rewrite SUSP in NOTSUSP.
        move: SCHEDs; move => /eqP SCHEDs /andP [/andP [PEND NOTSUSPs] _]; case => SAME; subst.
        by rewrite -/suspended SUSP in NOTSUSPs.
      Qed.
            
    End ScheduleIsValid.

    (** Scheduling Invariant *)

    (* In this section, we compare the two schedules to determine they are the same
       while job j has not completed in sched_susp. *)
    Section SchedulingInvariant.

      (* To prove that the schedules are the same, we use induction over time. *)
      Section InductiveStep.

        (* Consider any time t by which job j has not completed in sched_susp. *)
        Variable t: time.
        Hypothesis H_j_has_not_completed: ~~ completed_in_sched_susp j t.

        (* Induction Hypothesis:
           Assume that at every time prior to time t, any job that is scheduled
           in sched_susp is also scheduled in sched_susp_highercost. *)
        Hypothesis H_schedules_are_the_same:
          forall k any_j,
            k < t ->
            scheduled_at sched_susp any_j k = scheduled_at sched_susp_highercost any_j k.

        (* Then, let k be any time no later than t. *)
        Variable k: time.
        Hypothesis H_k_before_t: k <= t.

        (* First, we prove that jobs complete at time k in sched_susp iff they
           complete in the new schedule. *)
        Lemma sched_susp_highercost_same_completion:
          forall any_j,
            completed_in_sched_susp any_j k = completed_in_sched_susp_highercost any_j k.
        Proof.
          rename H_j_has_not_completed into NOTCOMPj,
                 H_schedules_are_the_same into IH, H_cost_of_j_does_not_decrease into COSTj,
                 H_inflation_only_for_job_j into COSTother.
          have COMPLETIONw := sched_susp_highercost_completed_jobs_dont_execute.
          rewrite /completed_in_sched_susp/completed_in_sched_susp_highercost
                  /completed_by -ltnNge in NOTCOMPj *.
          intros any_j; apply/idP/idP.
          { intros COMPs.
            case (boolP (any_j == j)) => [/eqP EQ | NEQ]; subst.
            { unfold completed_jobs_dont_execute in *. 
              have BUG: service sched_susp j t >= job_cost j.
              { apply completion_monotonic with (t0 := k); try (by done); apply ltnW. }
                by exfalso; move: BUG; rewrite leqNgt; move => /negP BUG; apply: BUG.
            }
            rewrite COSTother //.
            apply leq_trans with (service sched_susp any_j k); first by done. 
            rewrite /service /service_during big_nat_cond [X in _ <= X]big_nat_cond.
            rewrite leq_sum //; move => i /= /andP [LT _].
              by rewrite /service_at IH //; apply: (leq_trans LT).
          }
          { intros COMPw.
            apply leq_trans with (n := inflated_job_cost any_j);
              first by case (boolP (any_j==j)) => [/eqP EQ | NEQ]; subst; rewrite ?COSTj ?COSTother.
            apply leq_trans with (service sched_susp_highercost any_j k); first by done.
            apply leq_sum_nat; move => i /= LT _.
            by rewrite /service_at IH //; apply: (leq_trans LT).
          }
        Qed.

        (* We also prove the execution patterns of the jobs coincide... *)
        Lemma sched_susp_highercost_same_time_after_last_exec:
          forall any_j,
            time_after_last_execution job_arrival sched_susp any_j k =
            time_after_last_execution job_arrival sched_susp_highercost any_j k.
        Proof.
          rename H_schedules_are_the_same into IH.
          intros any_j; rewrite /time_after_last_execution.
          have EXsame: [exists t0:'I_k, scheduled_at sched_susp any_j t0] =
                       [exists t0:'I_k, scheduled_at sched_susp_highercost any_j t0].
          {
            by apply/idP/idP; move => /existsP [t0 LT0];
            apply/existsP; exists t0; rewrite ?IH//-?IH//; apply leq_trans with (n := k).
          }
          rewrite EXsame {EXsame}; case: ifP => [EX | _]; last by done.
          f_equal; apply eq_bigl; intros i; rewrite IH //.
          by apply leq_trans with (n := k).
        Qed.

        (* ...and the jobs have the same suspension intervals, ... *)
        Lemma sched_susp_highercost_same_suspension_duration:
          forall any_j,
            has_arrived job_arrival any_j k ->
            suspension_duration job_arrival job_suspension_duration sched_susp any_j k =
            suspension_duration job_arrival job_suspension_duration sched_susp_highercost any_j k.
        Proof.
          intros any_j ARR.
          rewrite /suspension_duration /service /service_during; f_equal.
          rewrite sched_susp_highercost_same_time_after_last_exec.
          rewrite big_nat_cond [X in _ = X]big_nat_cond; apply eq_bigr.
          move => i /= /andP [LT _].
          rewrite /service_at H_schedules_are_the_same //.
          apply leq_trans with (n := k); last by done.
          apply: (leq_trans LT).
          by apply last_execution_bounded_by_identity.
        Qed.
        
        (* ...which implies that jobs suspend at time k in sched_susp iff they suspend
           in the new schedule as well. *)
        Lemma sched_susp_highercost_same_suspension:
          forall any_j,
            has_arrived job_arrival any_j k ->
            suspended_in_sched_susp any_j k = suspended_in_sched_susp_highercost any_j k.
        Proof.
          intros any_j ARR.
          rewrite /suspended_in_sched_susp /suspended_in_sched_susp_highercost /suspended_at.
          rewrite -/completed_in_sched_susp_highercost -sched_susp_highercost_same_completion.
          rewrite sched_susp_highercost_same_time_after_last_exec.
          by rewrite sched_susp_highercost_same_suspension_duration.
        Qed.

        (* Using the lemmas above, we conclude the inductive step by showing that the
           two schedules are the same at time k. *)
        Lemma sched_susp_highercost_same_schedule:
          forall any_j,
            scheduled_at sched_susp any_j k = scheduled_at sched_susp_highercost any_j k.
        Proof.
          have FUNC := sched_susp_highercost_uses_construction_function.
          have SELFw := sched_susp_highercost_respects_self_suspensions.
          have COMPLETIONw := sched_susp_highercost_completed_jobs_dont_execute.
          have LEMMAcomp := sched_susp_highercost_same_completion.
          have LEMMAsusp := sched_susp_highercost_same_suspension.
          rename H_jobs_must_arrive_to_execute into MUSTARR,
                 H_cost_of_j_does_not_decrease into HIGHER,
                 H_inflation_only_for_job_j into SAME,
                 H_respects_self_suspensions into SELFs,
                 H_work_conserving into WORKs, H_priority_is_reflexive into REFL,
                 H_respects_priority into PRIOs.
          rewrite /service_in_sched_susp /service_in_sched_susp_highercost /service /service_during.
          suff EQsched: sched_susp k = sched_susp_highercost k by rewrite /scheduled_at EQsched.
          rewrite /scheduled_at FUNC /reduction.build_schedule -/hp_job.
          destruct (hp_job k) as [j_hp|] eqn:HP; last first.
          {
            destruct (sched_susp k) as [j_s|] eqn:SCHEDs; last by done.
            suff NOTNONE: hp_job k != None by rewrite HP in NOTNONE.
            apply seq_min_exists with (x := j_s).
            have NOTCOMPs: ~~ completed_in_sched_susp j_s k.
            {
              apply/negP; intros COMP'.
              apply completed_implies_not_scheduled in COMP'; try (by done).
              by rewrite /scheduled_at SCHEDs eq_refl in COMP'.
            }
            have ARR: has_arrived job_arrival j_s k by apply MUSTARR; apply/eqP.
            have NOTCOMPw: ~~ completed_by inflated_job_cost sched_susp_highercost j_s k.
              by rewrite -/completed_in_sched_susp_highercost -LEMMAcomp //.
            have NOTSUSPs: ~~ suspended_in_sched_susp j_s k by apply/negP; apply SELFs; apply/eqP.
            have NOTSUSPw:  ~~ suspended_in_sched_susp_highercost j_s k by rewrite -LEMMAsusp //.
            have ARRw: j_s \in jobs_arrived_up_to arr_seq k.
            {
              eapply arrived_between_implies_in_arrivals; eauto 1.
              by apply H_jobs_come_from_arrival_sequence with (t := k); apply/eqP.
            }
            by rewrite mem_filter; repeat (apply/andP; split).
          }
          {
            have IN: j_hp \in ready_jobs k.
              by apply seq_min_in_seq with (rel := higher_eq_priority k).
            rewrite mem_filter in IN; move: IN => /andP [/andP [/andP [ARRhp NOTCOMPhp] NOTSUSP] IN].
            have ARRINhp: arrives_in arr_seq j_hp by apply in_arrivals_implies_arrived in IN.
            destruct (sched_susp k) as [j_s|] eqn:SCHEDs.
            {
              case: ifP => // NOTPEND.
              have PENDw: pending job_arrival inflated_job_cost sched_susp_highercost j_s k.
              {
                apply/andP; split; first by apply MUSTARR; apply/eqP.
                rewrite -/completed_in_sched_susp_highercost -LEMMAcomp //.
                apply/negP; intros COMPs.
                apply completed_implies_not_scheduled in COMPs; try (by done).
                by rewrite /scheduled_at SCHEDs eq_refl in COMPs.
              }
              have ARRs: has_arrived job_arrival j_s k by apply MUSTARR; apply/eqP.
              have NOTSUSPs:  ~~ suspended_in_sched_susp j_s k by apply/negP; apply SELFs; apply/eqP. 
              have NOTSUSPw:  ~~ suspended_in_sched_susp_highercost j_s k by rewrite -LEMMAsusp.
              rewrite -/suspended_in_sched_susp_highercost PENDw NOTSUSPw /= in NOTPEND.
              suff PRIOINV: higher_eq_priority k j_s j_hp by rewrite PRIOINV in NOTPEND.
              apply PRIOs; try (by done); last by apply/eqP.
              have NOTCOMPhp': ~~ completed_by job_cost sched_susp j_hp k.
                by rewrite -/completed_in_sched_susp LEMMAcomp.
              have NOTSCHEDhp: ~~ scheduled_at sched_susp j_hp k.
              {
                apply/negP; intro SCHEDs'.
                apply only_one_job_scheduled with (j1 := j_s) in SCHEDs'; subst; last by apply/eqP.
                suff BUG: higher_eq_priority k j_hp j_hp by rewrite BUG in NOTPEND.
                by apply REFL. 
              }
              have NOTSUSPhp: ~~ suspended_in_sched_susp j_hp k by rewrite LEMMAsusp.
              by repeat (apply/andP; split).
            }
            {
              have NOTCOMPhp': ~~ completed_by job_cost sched_susp j_hp k.
                by rewrite -/completed_in_sched_susp LEMMAcomp.
              have NOTSCHEDhp: ~~ scheduled_at sched_susp j_hp k by rewrite /scheduled_at SCHEDs.
              have NOTSUSPhp: ~~ suspended_in_sched_susp j_hp k by rewrite LEMMAsusp.
              feed (WORKs j_hp k ARRINhp); first by repeat (apply/andP; split).
              move: WORKs => [j_x SCHEDx].
              by rewrite /scheduled_at SCHEDs in SCHEDx.
            }
          }
        Qed.
        
      End InductiveStep.

      (* Using the inductive step above, we prove that before the completion of job j
         in sched_susp, the two schedules are exactly the same. *)
      Lemma scheduled_in_susp_iff_scheduled_in_wcet:
        forall t any_j,
          ~~ completed_in_sched_susp j t ->
          scheduled_at sched_susp any_j t = scheduled_at sched_susp_highercost any_j t.
      Proof.
        have LEMMAsched := sched_susp_highercost_same_schedule.
        induction t as [t IHtmp] using strong_ind.
        intros j' NOTCOMP.
        suff IH: forall k any_j, k < t ->
                   scheduled_at sched_susp any_j k = scheduled_at sched_susp_highercost any_j k.
          by apply LEMMAsched with (t := t).
        intros k any_j LT; apply IHtmp; first by done.
        apply/negP; intro COMPk.
        suff COMPt: completed_in_sched_susp j t by rewrite COMPt in NOTCOMP.
          by apply completion_monotonic with (t0 := k);[apply ltnW|].
      Qed.
      
    End SchedulingInvariant.

    (** Comparison of Response-time Bounds *)

    (* In this section, we use the scheduling invariant above to compare response-time bounds
       for job j in both schedules. *)
    Section ComparingResponseTimes.

      (* Assume that job j has positive cost. *)
      Hypothesis H_cost_j_positive: job_cost j > 0.

      (* Also assume that the response time of job j in sched_susp is equal to some value r... *)
      Variable r: time.
      Hypothesis H_response_time_bound_in_sched_susp:
        job_response_time_in_sched_susp_bounded_by j r.
      Hypothesis H_response_time_bound_is_tight:
        forall r', job_response_time_in_sched_susp_bounded_by j r' -> r <= r'.

      (* ...and that the response time of j in the new schedule is upper-bounded by some value R. *)
      Variable R: time.
      Hypothesis H_response_time_bound_in_sched_susp_highercost:
        job_response_time_in_sched_susp_highercost_bounded_by j R.

      (* Using the scheduling invariant, we show that job j receives the same service
         in both schedules up to time (arr_j + r). *)
      Lemma sched_susp_highercost_same_service_for_j:
        forall t,
          t <= arr_j + r ->
          service_in_sched_susp j t = service_in_sched_susp_highercost j t.
      Proof.
        rename H_response_time_bound_is_tight into TIGHT.
        have IFF := scheduled_in_susp_iff_scheduled_in_wcet.
        rewrite /service_in_sched_susp /service_in_sched_susp_highercost /service /service_during.
        induction t; first by intros _; rewrite big_geq // big_geq.
        intros LT.
        feed IHt; first by apply ltnW.
        rewrite big_nat_recr // big_nat_recr //=.
        f_equal; first by done.
        rewrite /service_at IFF; first by done.
        apply/negP; intro COMPt.
        suff BUG: t >= arr_j + r by rewrite leqNgt LT in BUG.
        have AFTER: arr_j <= t.
        { apply contraT; rewrite -ltnNge; intro BEFORE.
          suff BUG: ~~ completed_in_sched_susp j t by rewrite COMPt in BUG.
          rewrite /completed_in_sched_susp /completed_by /service /service_during.
          rewrite (cumulative_service_before_job_arrival_zero job_arrival) //; last by apply ltnW.
            by rewrite -ltnNge.
        }
        rewrite -[t](addKn arr_j) -addnBA //.
        rewrite leq_add2l; apply TIGHT.
        rewrite /job_response_time_in_sched_susp_bounded_by /is_response_time_bound_of_job.
          by rewrite subnKC.
      Qed.
       
      (* Next, since r is an exact response time bound, we show that r <= R... *)
      Lemma sched_susp_highercost_r_le_R: r <= R.
      Proof.
        have SAME := sched_susp_highercost_same_service_for_j.
        rename H_response_time_bound_in_sched_susp_highercost into RESPw,
               H_response_time_bound_in_sched_susp into RESPs,
               H_response_time_bound_is_tight into TIGHT,
               H_cost_of_j_does_not_decrease into COSTj. 
        unfold job_response_time_in_sched_susp_bounded_by, service_in_sched_susp_highercost,
               job_response_time_in_sched_susp_highercost_bounded_by, service_in_sched_susp,
               is_response_time_bound_of_job, completed_by, service in *.
        set Sw := service_during sched_susp_highercost in RESPw RESPs TIGHT SAME.
        set Ss := service_during sched_susp in RESPs TIGHT SAME.
        apply contraT; rewrite -ltnNge; intros LT.
        have RESPs': job_cost j == Ss j 0 (job_arrival j + r).
        { rewrite eqn_leq; apply/andP; split; try done.
            by apply H_completed_jobs_dont_execute.
        }
        suff BUG: job_cost j > inflated_job_cost j by rewrite ltnNge COSTj in BUG.
        move: RESPs RESPs' => _ /eqP RESPs; rewrite RESPs.
        apply leq_ltn_trans with (Sw j 0 (job_arrival j + R)); first by done.
        rewrite /Ss /service_during.
        rewrite -> big_cat_nat with (n := arr_j + R);
          [simpl | by done | by rewrite leq_add2l ltnW].
        rewrite -addn1; apply leq_add;
           first by rewrite -SAME; [apply leqnn | rewrite leq_add2l ltnW].
        rewrite lt0n; apply/eqP; intro ZERO.
        suff BUG: R >= r by rewrite leqNgt LT in BUG.
        apply TIGHT.
        rewrite -(leq_add2r 0) -{3}ZERO addn0.
        rewrite -big_cat_nat //=; last by rewrite leq_add2l ltnW.
          by rewrite RESPs.
      Qed.

      (* ...and also prove that R must be as large as the inflated job cost. *)
      Lemma R_bounds_inflated_cost: R >= inflated_job_cost j.
      Proof.
        apply leq_trans with (n := service sched_susp_highercost j (arr_j + R)); first by done.
        rewrite /service /service_during.
        rewrite (ignore_service_before_arrival job_arrival) //; first last.
        - by apply leq_addr.
        - by apply sched_susp_highercost_jobs_must_arrive_to_execute.
        by apply cumulative_service_le_delta.
      Qed.

      (* To conclude, we prove that the difference between the response-time bound and the job cost
         is larger in the new schedule. *)
      Theorem sched_susp_highercost_incurs_more_interference:
        r - job_cost j <= R - inflated_job_cost j.
      Proof.
        have GECOST := R_bounds_inflated_cost.
        have LEQ := sched_susp_highercost_r_le_R.
        have SAME := sched_susp_highercost_same_service_for_j.
        rename H_response_time_bound_in_sched_susp into RESPs,
               H_response_time_bound_in_sched_susp_highercost into RESPw.
        rewrite leq_subLR.
        rewrite addnBA; last by apply GECOST.
        apply leq_trans with
            (n := service_in_sched_susp j (arr_j + r) + R - service_in_sched_susp_highercost j (arr_j + R));
          last by rewrite leq_sub // leq_add2r.
        rewrite addnC.
        rewrite /service_in_sched_susp /service_in_sched_susp_highercost /service
                /service_during in SAME *.
        rewrite -> big_cat_nat with (n := arr_j+r) (p := arr_j+R);
          [simpl | by done | by rewrite leq_add2l].
        feed (SAME (arr_j + r)); first by apply leqnn.
        rewrite -/(service_during sched_susp_highercost _ _ _)
                -/(service_during sched_susp_highercost _ _ _)
                -/(service_during sched_susp _ _ _) in SAME *.
        set Ss := service_during sched_susp in SAME *; set Sw := service_during sched_susp_highercost.
        rewrite -subnBA;
          last by apply leq_trans with (n := Sw j 0 (arr_j + r)); [rewrite SAME | apply leq_addr].
        rewrite addnC -addnBA; last by rewrite SAME.
        apply leq_trans with (n := R - (Sw j (arr_j + r) (arr_j + R) + 0));
          last by rewrite leq_sub2l // leq_add2l; apply eq_leq; apply/eqP; rewrite subn_eq0 SAME.
        rewrite addn0 subh3 //.
        apply leq_trans with (n := r + \sum_(arr_j+r<=t<arr_j+R) 1);
          first by rewrite leq_add2l; apply leq_sum; intros t _; apply leq_b1.
          by simpl_sum_const; rewrite subnDl subnKC.
      Qed.      

    End ComparingResponseTimes.
    
  End ReductionProperties.
  
End SustainabilitySingleCostProperties.
