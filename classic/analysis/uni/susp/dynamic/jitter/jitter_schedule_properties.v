Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task
               prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.schedule.uni.schedulability prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.jitter.schedule
               prosa.classic.model.schedule.uni.jitter.valid_schedule
               prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.valid_schedule
               prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(* In this file, we prove several properties about the constructed jitter-aware schedule. *)
Module JitterScheduleProperties.

  Import Job SporadicTaskset Suspension Priority SuspensionIntervals Workload Service
         UniprocessorScheduleWithJitter Schedulability ResponseTime
         ScheduleConstruction ValidSuspensionAwareSchedule ValidJitterAwareSchedule.

  Module basic := schedule.UniprocessorSchedule.
  Module susp := ScheduleWithSuspensions.
  Module jitter_aware := Platform.
  Module susp_aware := PlatformWithSuspensions.
  Module job_jitter := JobWithJitter.
  Module reduction := JitterScheduleConstruction.
  
  Section ProvingScheduleProperties.

    Context {Task: eqType}.    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> Task.

    (** Basic Setup & Setting *)
    
    (* Let ts be any task set to be analyzed. *)
    Variable ts: seq Task.

    (* Next, consider any consistent job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    
    (* ...whose jobs come from task set ts. *)
    Hypothesis H_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Consider any FP policy that is reflexive, transitive and total. *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: FP_is_total_over_task_set higher_eq_priority ts.
    Let job_higher_eq_priority := FP_to_JLDP job_task higher_eq_priority.
    
    (* Consider the original job and task costs from the suspension-aware schedule. *)
    Variable job_cost: Job -> time.
    Variable task_cost: Task -> time.

    (* Assume that jobs have associated suspension times. *)
    Variable job_suspension_duration: job_suspension Job.
      
    (* Next, consider any valid suspension-aware schedule of this arrival sequence.
       (Note: see prosa.classic.model.schedule.uni.susp.valid_schedule.v for details) *)
    Variable sched_susp: schedule Job.
    Hypothesis H_valid_schedule:
      valid_suspension_aware_schedule job_arrival arr_seq job_higher_eq_priority
                                      job_suspension_duration job_cost sched_susp.

    (* Finally, recall the definition of a job response-time bound in sched_susp. *)
    Let job_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_job job_arrival job_cost sched_susp.

    (** Analysis Setup *)
    
    (* Now we proceed with the reduction. Let j be the job to be analyzed. *)
    Variable j: Job.
    Hypothesis H_from_arrival_sequence: arrives_in arr_seq j.

    (* For simplicity, let's give some local names for the parameters of this job... *)
    Let arr_j := job_arrival j.
    Let task_of_j := job_task j.

    (* ...and recall the definition of other higher-or-equal-priority tasks. *)
    Let other_hep_task tsk_other :=
      higher_eq_priority tsk_other task_of_j && (tsk_other != task_of_j).
    
    (* Moreover, assume that each job is associated a response-time bound R. *)
    Variable R: Job -> time.

    (** Instantiation of the Reduction *)

    (* Next, recall the jitter-aware schedule from the reduction. *)
    Let sched_jitter := reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority
                                               job_cost job_suspension_duration j R.
    Let inflated_job_cost := reduction.inflated_job_cost job_cost job_suspension_duration j.
    Let job_jitter := reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R.

    (** Schedule Construction *)

    (* In this section, we prove that the jitter-aware schedule uses its construction function. *)
    Section PropertiesOfScheduleConstruction.

      Let build_schedule := reduction.build_schedule job_arrival job_task arr_seq higher_eq_priority
                                                     job_cost job_suspension_duration j R.
      
      (* Then, by showing that the construction function depends only on the previous service, ... *)
      Lemma sched_jitter_depends_only_on_service:
        forall sched1 sched2 t,
          (forall j, service sched1 j t = service sched2 j t) ->          
          build_schedule sched1 t = build_schedule sched2 t.
      Proof.
        intros sched1 sched2 t ALL.
        rewrite /build_schedule /reduction.build_schedule /reduction.highest_priority_job_other_than_j.
        set pend1 := pending _ _ _ sched1.
        set pend2 := pending _ _ _ sched2.        
        have SAME': forall j, pend1 j t = pend2 j t.
        {
          intros j0; rewrite /pend1 /pend2 /pending.
          case: jitter_has_passed => //=.
          by rewrite /completed_by ALL.
        }
        set pendjobs := reduction.pending_jobs_other_than_j _ _ _ _ _ _ _ _.
        have SAME: pendjobs sched1 t = pendjobs sched2 t.
        {
          apply eq_in_filter; intros j0 IN.
          rewrite /pending; case: jitter_has_passed => //=.
          by rewrite /completed_by ALL.
        }
        rewrite SAME SAME'; by done.
      Qed.

      (* ...we infer that the generated schedule is indeed based on the construction function. *)
      Corollary sched_jitter_uses_construction_function:
        forall t,
          sched_jitter t = build_schedule sched_jitter t.
      Proof.
        by ins; apply service_dependent_schedule_construction, sched_jitter_depends_only_on_service.
      Qed.

    End PropertiesOfScheduleConstruction.

    (** Valid Schedule Properties *)
    
    (* In this section, we prove that sched_jitter is a valid jitter-aware schedule. *)
    Section ScheduleIsValid.

      (* For simplicity, let's recall some definitions from the schedule construction. *)
      Let pending_jobs_other_than_j :=
        reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority
                                            job_cost job_suspension_duration j R sched_jitter.
      Let hp_job_other_than_j :=
        reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority
                                                    job_cost job_suspension_duration j R sched_jitter.

      (* Also recall the definition of a valid jitter-aware schedule. *)
      Let is_valid_jitter_aware_schedule :=
        valid_jitter_aware_schedule job_arrival arr_seq job_higher_eq_priority
                                    inflated_job_cost job_jitter.
      
      (* First, we show that scheduled jobs come from the arrival sequence. *)
      Lemma sched_jitter_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched_jitter arr_seq.
      Proof.
        move: H_valid_schedule => [FROM _].
        move => j0 t /eqP SCHED.
        rewrite sched_jitter_uses_construction_function /reduction.build_schedule
                -/hp_job_other_than_j in SCHED.
        set pending_in_jitter := pending _ _ _ _ in SCHED.
        destruct (hp_job_other_than_j t) as [j_hp|] eqn:HP; last first.
        {
          case PENDj: (pending_in_jitter j t); rewrite PENDj in SCHED; last by done.
          by case: SCHED => SAME; subst j0.
        }
        {
          have IN: arrives_in arr_seq j_hp.
          {
            have IN: j_hp \in pending_jobs_other_than_j t.
            {
              rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in HP.
              by apply seq_min_in_seq in HP.
            }
            rewrite mem_filter in IN; move: IN => /andP [/andP _ IN].
            rewrite /actual_arrivals_up_to in IN.
            by apply in_actual_arrivals_between_implies_arrived in IN.
          }
          case PENDj: (pending_in_jitter j t); rewrite PENDj in SCHED;
            first by move: SCHED; case: (~~ _); case => SAME; subst.
          by case: SCHED => SAME; subst j0.
        }
      Qed.

      (* Next, we show that jobs do not execute before their arrival times... *)
      Lemma sched_jitter_jobs_execute_after_jitter:
        jobs_execute_after_jitter job_arrival job_jitter sched_jitter.
      Proof.
        move => j0 t /eqP SCHED.
        rewrite sched_jitter_uses_construction_function /reduction.build_schedule
                -/hp_job_other_than_j in SCHED.
        set pending_in_jitter := pending _ _ _ _ in SCHED.
        destruct (hp_job_other_than_j t) as [j_hp|] eqn:HP; last first.
        {
          case PENDj: (pending_in_jitter j t); rewrite PENDj in SCHED; last by done.
          by case: SCHED => SAME; subst j0; move: PENDj => /andP [ARR _].
        }
        {
          have ARR: jitter_has_passed job_arrival job_jitter j_hp t.
          {
            have IN: j_hp \in pending_jobs_other_than_j t.
            {
              rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in HP.
              by apply seq_min_in_seq in HP.
            }
            by rewrite mem_filter in IN; move: IN => /andP [/andP [/andP [ARR _] _] _].
          }
          case PENDj: (pending_in_jitter j t); rewrite PENDj in SCHED;
            last by case: SCHED => SAME; subst j0.
          move: SCHED; case: (~~ _); case => SAME; subst; last by done.
          by move: PENDj => /andP [ARRj _].
        }
      Qed.

      (* ...nor longer than their execution costs. *)
      Lemma sched_jitter_completed_jobs_dont_execute:
        completed_jobs_dont_execute inflated_job_cost sched_jitter.
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
        rewrite sched_jitter_uses_construction_function /reduction.build_schedule
                -/hp_job_other_than_j.
        destruct (hp_job_other_than_j t) as [j_hp|] eqn:HP; last first.
        { case PENDj: pending; last by done.
          apply/eqP; case => SAME; subst j0; move: PENDj => /andP [_ NOTCOMPj].
            by rewrite /completed_by EQ leqnn in NOTCOMPj.
        }
        rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in HP.
        apply seq_min_in_seq in HP; rewrite mem_filter /pending /completed_by in HP.
        move: HP => /andP [/andP [/andP [_ NOTCOMPhp] _] _].
        case PENDj: pending.
        {
          move: PENDj => /andP [_ NOTCOMPj].
          case: (~~ higher_eq_priority _ _); apply/eqP; case => SAME; subst j0;
            first by rewrite /completed_by EQ leqnn in NOTCOMPj.
          by rewrite EQ leqnn in NOTCOMPhp.
        }
        {
          apply/eqP; case => SAME; subst j0.
          by rewrite EQ leqnn in NOTCOMPhp.
        }
      Qed.

      (* In addition, we prove that the schedule is (jitter-aware) work-conserving... *)
      Lemma sched_jitter_work_conserving:
        jitter_aware.work_conserving job_arrival inflated_job_cost job_jitter arr_seq sched_jitter.
      Proof.
        intros j0 t IN BACK.
        move: BACK => /andP [PEND NOTSCHED].
        rewrite /scheduled_at sched_jitter_uses_construction_function
                /reduction.build_schedule -/hp_job_other_than_j in NOTSCHED *.
        destruct (hp_job_other_than_j t) as [j_hp|] eqn:HP.
        {
          case PENDj: pending; rewrite PENDj in NOTSCHED; last by exists j_hp.
          by case: (~~ _); [by exists j | by exists j_hp].
        }
        {
          case PENDj: pending; rewrite PENDj in NOTSCHED; first by exists j.
          rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in HP.
          case: (boolP (j0 == j)) => [EQ | NEQ];
            first by move: EQ => /eqP EQ; subst j0; rewrite PEND in PENDj.
          have IN0: j0 \in pending_jobs_other_than_j t.
          {
            rewrite mem_filter PEND NEQ /=.
            apply arrived_between_implies_in_actual_arrivals; try (by done).
            by move: PEND => /andP [ARR _].
          }
          move: HP => /eqP HP; rewrite -[_ == _]negbK in HP.
          exfalso; move: HP => /negP BUG; apply: BUG.
          by apply seq_min_exists with (x := j0).
        }
      Qed.

      (* ...and respects task priorities. *)
      Lemma sched_jitter_respects_policy:
        jitter_aware.respects_FP_policy job_arrival inflated_job_cost job_jitter
                                        job_task arr_seq sched_jitter higher_eq_priority.
      Proof.
        rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL,
               H_priority_is_reflexive into REFL, H_jobs_from_taskset into FROMTS.
        move => j1 j2 t IN BACK /eqP SCHED.
        move: BACK => /andP [PEND NOTSCHED].
        rewrite /scheduled_at sched_jitter_uses_construction_function /reduction.build_schedule
                -/hp_job_other_than_j in SCHED NOTSCHED *.
        set pend := pending _ _ _ _ in SCHED NOTSCHED.
        have ALL: forall j_hi j_lo, hp_job_other_than_j t = Some j_hi ->
                                    j_lo \in pending_jobs_other_than_j t ->
                                    higher_eq_priority (job_task j_hi) (job_task j_lo).
        {
          intros j_hi j_lo SOME INlo; move: SCHED => MIN.
          rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in SOME.
          apply seq_min_computes_min with (y := j_lo) in SOME; try (by done);
            first by intros x y z; apply TRANS.
          intros x y; rewrite mem_filter [y \in _]mem_filter /actual_arrivals_up_to.
          move => /andP [_ INx] /andP [_ INy].
          rewrite /FP_is_total_over_task_set /total_over_list in TOTAL.
          by apply/orP; apply TOTAL; apply FROMTS;
            eapply in_actual_arrivals_between_implies_arrived; eauto 1.
        }
        case PENDj: (pend j t); rewrite PENDj in SCHED NOTSCHED.
        {
          destruct (hp_job_other_than_j t) as [j_hp|] eqn:HP.
          {
            rewrite /FP_to_JLFP /= in SCHED NOTSCHED.
            case LP: (~~ higher_eq_priority (job_task j_hp) (job_task j));
              rewrite LP in SCHED NOTSCHED.
            {
              case: SCHED => SAME; subst j2.
              case: (boolP (j1 == j)) => [EQ | NEQ]; first by move: EQ => /eqP EQ; subst j1.
              apply (TRANS (job_task j_hp)).
              {
                have INhp: arrives_in arr_seq j_hp.
                {
                  rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in HP.
                  apply seq_min_in_seq in HP.
                  rewrite mem_filter in HP; move: HP => /andP [_ INhp].
                  rewrite /actual_arrivals_up_to in INhp.
                  by apply in_actual_arrivals_before_implies_arrived in INhp.
                }
                by exploit (TOTAL (job_task j) (job_task j_hp)); try (by apply FROMTS);
                  move => [HPj | HPhp]; last by rewrite HPhp in LP.
              }
              apply ALL; try (by done).
              move: PEND => /andP [ARR NOTCOMP].
              rewrite mem_filter /pending ARR NOTCOMP 2!andTb.
              by apply/andP; split; last by apply arrived_between_implies_in_actual_arrivals.
            }
            {
              case: SCHED => SAME; subst j2.
              case: (boolP (j1 == j)) => [EQ | NEQ];
                first by move: EQ => /eqP EQ; subst j1; apply negbT in LP; rewrite negbK in LP.
              apply ALL; try (by done).
              move: PEND => /andP [ARR NOTCOMP].
              rewrite mem_filter /pending ARR NOTCOMP 2!andTb.
              by apply/andP; split; last by apply arrived_between_implies_in_actual_arrivals.
            }
          }
          {
            case: SCHED => SAME; subst j2.
            case: (boolP (j1 == j)) => [EQ | NEQ]; first by move: EQ => /eqP EQ; subst j1.
            suff NOTNONE: hp_job_other_than_j t != None by rewrite HP in NOTNONE.
            apply seq_min_exists with (x := j1).
            move: PEND => /andP [ARR NOTCOMP].
            rewrite mem_filter /pending ARR NOTCOMP 2!andTb.
            by apply/andP; split; last by apply arrived_between_implies_in_actual_arrivals.
          }
        }
        {
          case: (boolP (j1 == j)) => [EQ | NEQ];
            first by move: EQ => /eqP EQ; subst j1; rewrite -/pend PENDj in PEND.
          apply ALL; first by done.
          move: PEND => /andP [ARR NOTCOMP].
          rewrite mem_filter /pending ARR NOTCOMP 2!andTb.
          by apply/andP; split; last by apply arrived_between_implies_in_actual_arrivals.
        }
      Qed.

      (* From the properties above, we conclude that the generated schedule is valid. *)
      Corollary sched_jitter_is_valid: is_valid_jitter_aware_schedule sched_jitter.
      Proof.
        repeat split.
        - by apply sched_jitter_jobs_come_from_arrival_sequence.
        - by apply sched_jitter_jobs_execute_after_jitter.
        - by apply sched_jitter_completed_jobs_dont_execute.
        - by apply sched_jitter_work_conserving.
        - by apply sched_jitter_respects_policy.
      Qed.
      
      (* Finally, we show that the generated schedule does not pick job j if
         there are other pending higher-or-equal-priority jobs. *)
      Lemma sched_jitter_does_not_pick_j:
        forall j_hp t,
          arrives_in arr_seq j_hp ->
          j_hp != j ->
          pending job_arrival inflated_job_cost job_jitter sched_jitter j_hp t ->
          higher_eq_priority (job_task j_hp) (job_task j) ->
          ~~ scheduled_at sched_jitter j t.
      Proof.
        rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL,
               H_jobs_from_taskset into FROMTS.
        move => j_hp t ARRinhp NEQ PENDhp HP; apply/negP; move => /eqP SCHEDj.
        rewrite sched_jitter_uses_construction_function /reduction.build_schedule
                -/hp_job_other_than_j in SCHEDj.
        set pend := pending _ _ _ _ in SCHEDj.
        have INhp: j_hp \in pending_jobs_other_than_j t.
        {
          rewrite mem_filter PENDhp NEQ /=. 
          apply arrived_between_implies_in_actual_arrivals; try (by done).
          rewrite /actual_arrival_between /=.
          by move: PENDhp => /andP [ARRhp _].
        }              
        case PENDj: (pend j t); rewrite PENDj in SCHEDj.
        {
          destruct (hp_job_other_than_j t) as [j_hp'|] eqn:HP'.
          {
            have ALL: forall j_lo,  j_lo \in pending_jobs_other_than_j t ->
                                    higher_eq_priority (job_task j_hp') (job_task j_lo).
            {
              intros j_lo INlo; move: HP' => MIN.
              rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in MIN.
              apply seq_min_computes_min with (y := j_lo) in MIN; try (by done);
                first by intros x y z; apply TRANS.
              intros x y; rewrite mem_filter [y \in _]mem_filter /actual_arrivals_up_to.
              move => /andP [_ INx] /andP [_ INy].
              by apply/orP; apply TOTAL; apply FROMTS;
                eapply in_actual_arrivals_between_implies_arrived; eauto 1.
            }
            case LP: (~~ higher_eq_priority (job_task j_hp') (job_task j)); rewrite LP in SCHEDj.
            {
              move: LP => /negP LP; apply: LP.
              by apply (TRANS (job_task j_hp)); first by apply ALL.
            }
            {
              case: SCHEDj => SAME; subst j_hp'.
              rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in HP'.
              by apply seq_min_in_seq in HP'; rewrite mem_filter eq_refl andbF /= in HP'.
            }
          }
          {
            suff NOTNONE: hp_job_other_than_j t != None by rewrite HP' in NOTNONE.
            by apply seq_min_exists with (x := j_hp).
          }
        }
        {
          rewrite /hp_job_other_than_j /reduction.highest_priority_job_other_than_j in SCHEDj.
          apply seq_min_in_seq in SCHEDj.
          by rewrite mem_filter eq_refl andbF in SCHEDj.
        }
      Qed.
      
    End ScheduleIsValid.

  End ProvingScheduleProperties.
  
End JitterScheduleProperties.