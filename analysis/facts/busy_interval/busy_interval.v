Require Export prosa.model.schedule.work_conserving.
Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.definitions.priority_inversion.
Require Export prosa.analysis.facts.behavior.all.
Require Export prosa.analysis.facts.model.service_of_jobs.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.readiness.basic.

(** * Existence of Busy Interval for JLFP-models *)
(** In this module we derive a sufficient condition for existence of
    busy intervals for uni-processor for JLFP schedulers. *)
Section ExistsBusyIntervalJLFP.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.    

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  
  (** Next, consider any ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
  
  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}. 
  
  (** For simplicity, let's define some local names. *)
  Let job_pending_at := pending sched.
  Let job_completed_by := completed_by sched.
  Let arrivals_between := arrivals_between arr_seq.
  
  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** Consider an arbitrary job [j]. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_task : job_of_task tsk j.
  Hypothesis H_job_cost_positive : job_cost_positive j.
  
  (** Recall the list of jobs that arrive in any interval. *)
  Let quiet_time t1 := quiet_time arr_seq sched j t1.
  Let quiet_time_dec t1 := quiet_time_dec arr_seq sched j t1.
  Let busy_interval_prefix t1 t2 := busy_interval_prefix arr_seq sched j t1 t2.
  Let busy_interval t1 t2 := busy_interval arr_seq sched j t1 t2.
  Let is_priority_inversion_bounded_by K := priority_inversion_of_job_is_bounded_by arr_seq sched j K.
  
  (** We begin by proving a basic lemma about completion of the job within its busy interval. *)
  Section BasicLemma.

    (** Assume that the priority relation is reflexive. *)
    Hypothesis H_priority_is_reflexive : reflexive_priorities.

    (** Consider any busy interval <<[t1, t2)>> of job [j]. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_interval : busy_interval t1 t2.
    
    (** We prove that job j completes by the end of the busy interval. *)
    Lemma job_completes_within_busy_interval: 
      job_completed_by j t2.
    Proof.
      rename H_priority_is_reflexive into REFL, H_busy_interval into BUSY.
      move: BUSY => [[_ [_ [_ /andP [_ ARR]]]] QUIET].
      apply QUIET; try done.
      apply (REFL 0).
    Qed.

  End BasicLemma.
  
  (** In this section, we prove that during a busy interval there
         always exists a pending job. *)
  Section ExistsPendingJob.
    
    (** Let [[t1, t2]] be any interval where time t1 is quiet and time t2 is not quiet. *)
    Variable t1 t2 : instant.
    Hypothesis H_interval : t1 <= t2.
    Hypothesis H_quiet : quiet_time t1.
    Hypothesis H_not_quiet : ~ quiet_time t2.
    
    (** Then, we prove that there is a job pending at time t2
         that has higher or equal priority (with respect of [tsk]). *)
    Lemma not_quiet_implies_exists_pending_job:
      exists j_hp,
        arrives_in arr_seq j_hp /\
        arrived_between j_hp t1 t2 /\
        hep_job j_hp j /\
        ~ job_completed_by j_hp t2. 
    Proof.
      rename H_quiet into QUIET, H_not_quiet into NOTQUIET.
      destruct (has (fun j_hp => (~~ job_completed_by j_hp t2) && hep_job j_hp j)
                    (arrivals_between t1 t2)) eqn:COMP.
      { move: COMP => /hasP [j_hp ARR /andP [NOTCOMP HP]].
        move: (ARR) => INarr.
        apply in_arrivals_implies_arrived_between in ARR; last by done.
        apply in_arrivals_implies_arrived in INarr.
          by exists j_hp; repeat split; last by apply/negP.
      }
      {
        apply negbT in COMP; rewrite -all_predC in COMP.
        move: COMP => /allP COMP.
        exfalso; apply NOTQUIET; intros j_hp IN HP ARR.
        destruct (ltnP (job_arrival j_hp) t1) as [BEFORE | AFTER];
          first by specialize (QUIET j_hp IN HP BEFORE); apply completion_monotonic with (t := t1).
        feed (COMP j_hp).
          by eapply arrived_between_implies_in_arrivals; eauto 1; apply/andP; split.
            by rewrite /= HP andbT negbK in COMP.
      }
    Qed.

  End ExistsPendingJob.
  
  (** In this section, we prove that during a busy interval the
         processor is never idle. *)
  Section ProcessorAlwaysBusy.

    (** Assume that the schedule is work-conserving ... *)
    Hypothesis H_work_conserving : work_conserving arr_seq sched.

    (** ... and the priority relation is reflexive and transitive. *)
    Hypothesis H_priority_is_reflexive : reflexive_priorities. 
    Hypothesis H_priority_is_transitive : transitive_priorities.
    
    (** Consider any busy interval prefix <<[t1, t2)>>. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_interval_prefix : busy_interval_prefix t1 t2.

    (** We prove that if the processor is idle at a time instant t, then 
           the next time instant [t+1] will be a quiet time. *)
    Lemma idle_time_implies_quiet_time_at_the_next_time_instant:
      forall (t : instant),
        is_idle sched t ->
        quiet_time t.+1.
    Proof.
      intros t IDLE jhp ARR HP AB.
      apply negbNE; apply/negP; intros NCOMP.
      rewrite /arrived_before ltnS in AB.
      move:(H_work_conserving _ t ARR) => WC.
      feed WC.
      { apply/andP. split.
        - apply/negPn/negP; rewrite negb_and; intros COMP.
          move: COMP => /orP; rewrite Bool.negb_involutive; move => [/negP CON|COM]; auto.
          move: NCOMP => /negP NCOMP; apply: NCOMP.
            by apply completion_monotonic with t.
        - by move: IDLE => /eqP IDLE; rewrite /scheduled_at scheduled_in_def IDLE. 
      }
      move: IDLE WC => /eqP IDLE [jo SCHED].
        by rewrite scheduled_at_def IDLE in SCHED.
    Qed.

    (** Next, we prove that at any time instant t within the busy interval there exists a job 
           [jhp] such that (1) job [jhp] is pending at time [t] and (2) job [jhp] has higher-or-equal
           priority than task [tsk]. *)
    Lemma pending_hp_job_exists:
      forall t,
        t1 <= t < t2 ->
        exists jhp,
          arrives_in arr_seq jhp /\
          job_pending_at jhp t /\
          hep_job jhp j.
    Proof.
      move => t /andP [GE LT]; move: (H_busy_interval_prefix) => [_ [QTt [NQT REL]]].
      move: (ltngtP t1.+1 t2) => [GT|CONTR|EQ]; first last.
      - subst t2; rewrite ltnS in LT.
        have EQ: t1 = t by apply/eqP; rewrite eqn_leq; apply/andP; split.
        subst t1; clear GE LT.
        exists j; repeat split; try done.
        + move: REL; rewrite ltnS -eqn_leq eq_sym; move => /eqP REL.
            by rewrite -REL; eapply job_pending_at_arrival; eauto 2.
        + by apply (H_priority_is_reflexive 0).
      - by exfalso; move_neq_down CONTR; eapply leq_ltn_trans; eauto 2.
      - have EX: exists hp__seq: seq Job,
        forall j__hp, j__hp \in hp__seq <-> arrives_in arr_seq j__hp /\ job_pending_at j__hp t /\ hep_job j__hp j.
        { exists (filter (fun jo => (job_pending_at jo t) && (hep_job jo j)) (arrivals_between 0 t.+1)).
          intros; split; intros T.
          - move: T; rewrite mem_filter; move => /andP [/andP [PEN HP] IN].
            repeat split; eauto using in_arrivals_implies_arrived.
          - move: T => [ARR [PEN HP]].
            rewrite mem_filter; apply/andP; split; first (apply/andP; split); try done.
            eapply arrived_between_implies_in_arrivals; try done.
              by apply/andP; split; last rewrite ltnS; move: PEN => /andP [T _].
        } move: EX => [hp__seq SE]; case FL: (hp__seq) => [ | jhp jhps].
        + subst hp__seq; exfalso.
          move: GE; rewrite leq_eqVlt; move => /orP [/eqP EQ| GE].
          * subst t.
            apply NQT with t1.+1; first by apply/andP; split.
            intros jhp ARR HP ARRB; apply negbNE; apply/negP; intros NCOMP.
            move: (SE jhp) => [_ SE2].
            rewrite in_nil in SE2; feed SE2; [clear SE2 | by done].
            repeat split; try done; first apply/andP; split; try done.
            apply/negP; intros COMLP.
            move: NCOMP => /negP NCOMP; apply: NCOMP.
              by apply completion_monotonic with t1.
          * apply NQT with t; first by apply/andP; split.
            intros jhp ARR HP ARRB; apply negbNE; apply/negP; intros NCOMP.
            move: (SE jhp) => [_ SE2].
            rewrite in_nil in SE2; feed SE2; [clear SE2 | by done].
              by repeat split; auto; apply/andP; split; first apply ltnW.
        + move: (SE jhp)=> [SE1 _]; subst; clear SE.
            by exists jhp; apply SE1; rewrite in_cons; apply/orP; left.
    Qed.
    
    (** We prove that at any time instant [t] within <<[t1, t2)>> the processor is not idle. *)
    Lemma not_quiet_implies_not_idle:
      forall t,
        t1 <= t < t2 ->
        ~ is_idle sched t.
    Proof.
      intros t NEQ IDLE.
      move: (pending_hp_job_exists _ NEQ) => [jhp [ARR [PEND HP]]].
      unfold work_conserving in *.
      feed (H_work_conserving _ t ARR).
      apply/andP; split; first by done.
      move: IDLE => /eqP IDLE; rewrite scheduled_at_def IDLE; by done.
      move: (H_work_conserving) => [jo SCHED].
      move: IDLE SCHED => /eqP IDLE SCHED.
        by rewrite scheduled_at_def IDLE in SCHED.
    Qed.
    
  End ProcessorAlwaysBusy.

  (** In section we prove a few auxiliary lemmas about quiet time and service.  *)
  Section QuietTimeAndServiceOfJobs.

    (** Assume that the schedule is work-conserving ... *)
    Hypothesis H_work_conserving : work_conserving arr_seq sched.

    (** ... and there are no duplicate job arrivals. *)
    Hypothesis H_arrival_sequence_is_a_set:
      arrival_sequence_uniq arr_seq.

    (** Let [t1] be a quiet time. *)
    Variable t1 : instant.
    Hypothesis H_quiet_time : quiet_time t1.
    
    (** Assume that there is no quiet time in the interval (t1, t1 + Δ]. *)
    Variable Δ : duration.
    Hypothesis H_no_quiet_time : forall t, t1 < t <= t1 + Δ -> ~ quiet_time t.

    (** For clarity, we introduce a notion of the total service of jobs released in 
           time interval <<[t_beg, t_end)>> during the time interval [t1, t1 + Δ). *)
    Let service_received_by_hep_jobs_released_during t_beg t_end :=
      service_of_higher_or_equal_priority_jobs
        sched (arrivals_between t_beg t_end) j t1 (t1 + Δ).

    (** We prove that jobs with higher-than-or-equal priority that
           released before time instant t1 receive no service after 
           time instant t1. *)
    Lemma hep_jobs_receive_no_service_before_quiet_time:
      service_received_by_hep_jobs_released_during t1 (t1 + Δ) =
      service_received_by_hep_jobs_released_during 0 (t1 + Δ).
    Proof.
      intros.
      rewrite /service_received_by_hep_jobs_released_during
              /service_of_higher_or_equal_priority_jobs
              /service_of_jobs /arrivals_between.
      rewrite [in X in _ = X](arrivals_between_cat _ _ t1);
        [ | | rewrite leq_addr]; try done.
      rewrite big_cat //=.
      rewrite -{1}[\sum_(j <- arrivals_between _ (t1 + Δ) | _)
                    service_during sched j t1 (t1 + Δ)]add0n.
      apply/eqP. rewrite eqn_add2r eq_sym exchange_big //=.
      rewrite big1_seq //.
      move => t' /andP [_ NEQ]; rewrite mem_iota in NEQ.
      rewrite big1_seq //.
      move => jhp /andP [HP ARR].
      apply/eqP; rewrite eqb0. rewrite -scheduled_at_def.
      apply (completed_implies_not_scheduled _ _ H_completed_jobs_dont_execute).
      apply completion_monotonic with t1; [ move: NEQ => /andP [T1 _] | ]; try done.
      apply H_quiet_time; try done.
      - by eapply in_arrivals_implies_arrived; eauto 2.
      - by eapply in_arrivals_implies_arrived_before; eauto 2.
    Qed.
    
    (** Next we prove that the total service within a "non-quiet" 
        time interval <<[t1, t1 + Δ)>> is exactly Δ. *)
    Lemma no_idle_time_within_non_quiet_time_interval:
      service_of_jobs sched predT (arrivals_between 0 (t1 + Δ)) t1 (t1 + Δ) = Δ.
    Proof.
      intros; unfold service_of_jobs, service_of_higher_or_equal_priority_jobs.
      rewrite -{3}[Δ](sum_of_ones t1) exchange_big //=.
      apply/eqP; rewrite eqn_leq; apply/andP; split.
      { rewrite leq_sum //.
        move => t' _.
        have SCH := service_of_jobs_le_1 sched predT (arrivals_between 0 (t1 + Δ)) _ t'. 
          by eauto using arrivals_uniq.
      }
      { rewrite [in X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond //=; rewrite leq_sum //.
        move => t' /andP [/andP [LT GT] _].
        apply/sum_seq_gt0P.
        ideal_proc_model_sched_case_analysis_eq sched t' jo.
        { exfalso; move: LT; rewrite leq_eqVlt; move => /orP [/eqP EQ|LT].
          { subst t'.
            feed (H_no_quiet_time t1.+1); first by apply/andP; split.
            apply: H_no_quiet_time.
              by apply idle_time_implies_quiet_time_at_the_next_time_instant.
          }
          { feed (H_no_quiet_time t'); first by apply/andP; split; last rewrite ltnW.
            apply: H_no_quiet_time; intros j_hp IN HP ARR.
            apply contraT; intros NOTCOMP.
            destruct (scheduled_at sched j_hp t') eqn:SCHEDhp;
              first by rewrite scheduled_at_def EqIdle in SCHEDhp.
            apply negbT in SCHEDhp.
            feed (H_work_conserving j_hp t' IN);
              first by repeat (apply/andP; split); first by apply ltnW.
            move: H_work_conserving => [j_other SCHEDother].
              by rewrite scheduled_at_def EqIdle in SCHEDother.
          }              
        }
        { exists jo; split.
          - apply arrived_between_implies_in_arrivals; try done.
            apply H_jobs_come_from_arrival_sequence with t'; try done.
            apply/andP; split; first by done.
            apply H_jobs_must_arrive_to_execute in Sched_jo.
              by apply leq_ltn_trans with t'. 
          - by rewrite lt0b -scheduled_at_def. 
        }
      }
    Qed.
    
  End QuietTimeAndServiceOfJobs.

  (** In this section, we show that the length of any busy interval
      is bounded, as long as there is enough supply to accommodate
      the workload of tasks with higher or equal priority. *)
  Section BoundingBusyInterval.

    (** Assume that the schedule is work-conserving, ... *)
    Hypothesis H_work_conserving : work_conserving arr_seq sched.

    (** ... and there are no duplicate job arrivals, ... *)
    Hypothesis H_arrival_sequence_is_a_set:
      arrival_sequence_uniq arr_seq.        

    (** ... and the priority relation is reflexive and transitive. *)
    Hypothesis H_priority_is_reflexive: reflexive_priorities.
    Hypothesis H_priority_is_transitive: transitive_priorities.
    
    (** Next, we recall the notion of workload of all jobs released in a given interval
           <<[t1, t2)>> that have higher-or-equal priority w.r.t the job j being analyzed. *)
    Let hp_workload t1 t2 :=
      workload_of_higher_or_equal_priority_jobs j (arrivals_between t1 t2).

    (** With regard to the jobs with higher-or-equal priority that are released
           in a given interval <<[t1, t2)>>, we also recall the service received by these
           jobs in the same interval [t1, t2). *)
    Let hp_service t1 t2 :=
      service_of_higher_or_equal_priority_jobs
        sched (arrivals_between t1 t2) j t1 t2.

    (** Now we begin the proof. First, we show that the busy interval is bounded. *)
    Section BoundingBusyInterval.

      (** Suppose that job j is pending at time t_busy. *)
      Variable t_busy : instant.
      Hypothesis H_j_is_pending : job_pending_at j t_busy.
      
      (** First, we show that there must exist a busy interval prefix. *)
      Section LowerBound.

        (** Since job j is pending, there is a (potentially unbounded)
               busy interval that starts no later than with the arrival of j. *)
        Lemma exists_busy_interval_prefix:
          exists t1,
            busy_interval_prefix t1 t_busy.+1 /\
            t1 <= job_arrival j <= t_busy.
        Proof.
          rename H_j_is_pending into PEND, H_work_conserving into WORK.
          destruct ([exists t:'I_t_busy.+1, quiet_time_dec t]) eqn:EX.
          - set last0 := \max_(t < t_busy.+1 | quiet_time_dec t) t.
            move: EX => /existsP [t EX].
            have PRED: quiet_time_dec last0 by apply (bigmax_pred t_busy.+1 (quiet_time_dec) t).
            have QUIET: quiet_time last0.
            { intros j_hp IN HP ARR; move: PRED => /allP PRED; feed (PRED j_hp).
              - by eapply arrived_between_implies_in_arrivals; eauto.
              - by rewrite HP implyTb in PRED.
            } 
            exists last0.
            have JAIN: last0 <= job_arrival j <= t_busy.
            { apply/andP; split; last by move: PEND => /andP [ARR _].
              move_neq_up BEFORE.
              move: PEND => /andP [_ NOTCOMP].
              feed (QUIET j H_from_arrival_sequence); first by apply (H_priority_is_reflexive 0).
              specialize (QUIET BEFORE).
              apply completion_monotonic with (t' := t_busy) in QUIET; first by rewrite QUIET in NOTCOMP. 
                by apply bigmax_ltn_ord with (i0 := t).
            }
            repeat split; try done.
            + by apply bigmax_ltn_ord with (i0 := t).
            + move => t0 /andP [GTlast LTbusy] QUIET0.
              have PRED0: quiet_time_dec t0.
              apply/allP; intros j_hp ARR; apply/implyP; intros HP.
              apply QUIET0; eauto 2 using in_arrivals_implies_arrived, in_arrivals_implies_arrived_before.
              move_neq_down GTlast.
                by eapply (@leq_bigmax_cond _ (fun (x: 'I_t_busy.+1) => quiet_time_dec x) (fun x => x) (Ordinal LTbusy)).
          -  apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL.
             exists 0; split; last by apply/andP; split; last by move: PEND => /andP [ARR _].
             repeat split; first by intros j_hp _ _ ARR; rewrite /arrived_before ltn0 in ARR.
             move => t /andP [GE LT].
             specialize (ALL (Ordinal LT)); move: ALL => /negP ALL.
             intros QUIET; apply ALL; simpl.
             apply/allP; intros j_hp ARR; apply/implyP; intros HP.
             apply QUIET; eauto 2 using in_arrivals_implies_arrived, in_arrivals_implies_arrived_before.
             apply/andP; split; first by done.
               by move: PEND => /andP [ARR _].
        Qed.             

      End LowerBound.
      
      (** Next we prove that, if there is a point where the requested workload
             is upper-bounded by the supply, then the busy interval eventually ends. *)
      Section UpperBound.

        (** Consider any busy interval prefix of job j. *)
        Variable t1 : instant.
        Hypothesis H_is_busy_prefix : busy_interval_prefix t1 t_busy.+1.
        
        (** Let priority_inversion_bound be a constant which bounds
             length of a priority inversion. *)
        Variable priority_inversion_bound: instant.
        Hypothesis H_priority_inversion_is_bounded:
          is_priority_inversion_bounded_by priority_inversion_bound.
        
        (** Next, assume that for some positive delta, the sum of requested workload
               at time [t1 + delta] and constant priority_inversion_bound is bounded by 
               delta (i.e., the supply). *)
        Variable delta : duration.
        Hypothesis H_delta_positive : delta > 0.
        Hypothesis H_workload_is_bounded :
          priority_inversion_bound + hp_workload t1 (t1 + delta) <= delta.

        (** If there is a quiet time by time (t1 + delta), it trivially follows that
               the busy interval is bounded.
               Thus, let's consider first the harder case where there is no quiet time,
               which turns out to be impossible. *)
        Section CannotBeBusyForSoLong.
          
          (** Assume that there is no quiet time in the interval (t1, t1 + delta]. *)
          Hypothesis H_no_quiet_time:
            forall t, t1 < t <= t1 + delta -> ~ quiet_time t.                

          (** Since the interval is always non-quiet, the processor is always busy
                 with tasks of higher-or-equal priority or some lower priority job which was scheduled,
                 i.e., the sum of service done by jobs with actual arrival time in <<[t1, t1 + delta)>> 
                 and priority inversion equals delta. *)
          Lemma busy_interval_has_uninterrupted_service: 
            delta <= priority_inversion_bound + hp_service t1 (t1 + delta).
          Proof. 
            move: H_is_busy_prefix => [H_strictly_larger [H_quiet [_ EXj]]].
            destruct (delta <= priority_inversion_bound) eqn:KLEΔ.
            { by apply leq_trans with priority_inversion_bound; last rewrite leq_addr. }
            apply negbT in KLEΔ; rewrite -ltnNge in KLEΔ. 
            apply leq_trans with (cumulative_priority_inversion sched j t1 (t1 + delta) + hp_service t1 (t1 + delta)).
            { rewrite /hp_service hep_jobs_receive_no_service_before_quiet_time //.
              rewrite /service_of_higher_or_equal_priority_jobs /service_of_jobs sum_pred_diff. 
              rewrite addnBA; last first.
              { by rewrite big_mkcond //= leq_sum //; intros j' _; case (hep_job j' j). } 
              rewrite addnC -addnBA.
              { intros. have TT := no_idle_time_within_non_quiet_time_interval.
                  by unfold service_of_jobs in TT; rewrite TT // leq_addr.
              } 
              { rewrite /cumulative_priority_inversion /is_priority_inversion exchange_big //=.
                apply leq_sum_seq; move => t II _.
                rewrite mem_index_iota in II; move: II => /andP [GEi LEt].
                case SCHED: (sched t) => [j1 | ]; simpl; first last.
                { rewrite leqn0 big1_seq //. }
                { case PRIO1: (hep_job j1 j); simpl; first last.
                  - rewrite <- SCHED.
                    have SCH := service_of_jobs_le_1 sched _ _ _ t; eauto using arrivals_uniq. 
                  - rewrite leqn0 big1_seq; first by done.
                    move => j2 /andP [PRIO2 ARRj2].
                    case EQ: (j1 == j2).
                    + by move: EQ => /eqP EQ; subst j2; rewrite PRIO1 in PRIO2.
                    + apply/eqP; rewrite eqb0; apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                        by inversion CONTR; clear CONTR; subst j2; rewrite PRIO1 in PRIO2. } } }
            { rewrite leq_add2r.
              destruct (t1 + delta <= t_busy.+1) eqn:NEQ; [ | apply negbT in NEQ; rewrite -ltnNge in NEQ].
              - apply leq_trans with (cumulative_priority_inversion sched j t1 t_busy.+1); last eauto 2.
                  by rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + delta)) //=; rewrite leq_addr.
              -  apply H_priority_inversion_is_bounded; repeat split; try done.
                 + by rewrite -addn1 leq_add2l.
                 + move => t' /andP [LT GT]; apply H_no_quiet_time.
                     by apply/andP; split; [ | rewrite ltnW ].
                 + move: EXj => /andP [T1 T2].
                     by apply/andP; split; [done | apply ltn_trans with (t_busy.+1)].
            }
          Qed.
          
          (** Moreover, the fact that the interval is not quiet also implies
                 that there's more workload requested than service received. *)
          Lemma busy_interval_too_much_workload:
            hp_workload t1 (t1 + delta) > hp_service t1 (t1 + delta).
          Proof.
            have PEND := not_quiet_implies_exists_pending_job.
            rename H_no_quiet_time into NOTQUIET, 
            H_is_busy_prefix into PREFIX.
            set l := arrivals_between t1 (t1 + delta).
            set hep := hep_job.
            unfold hp_service, service_of_higher_or_equal_priority_jobs, service_of_jobs,
            hp_workload, workload_of_higher_or_equal_priority_jobs, workload_of_jobs.
            fold arrivals_between l hep.
            move: (PREFIX) => [_ [QUIET _]].
            move: (NOTQUIET) => NOTQUIET'.
            feed (NOTQUIET' (t1 + delta)).
            { by apply/andP; split; first
                by rewrite -addn1 leq_add2l.
            }
            feed (PEND t1 (t1 + delta)); first by apply leq_addr.
            specialize (PEND QUIET NOTQUIET').
            move: PEND => [j0 [ARR0 [/andP [GE0 LT0] [HP0 NOTCOMP0]]]].
            have IN0: j0 \in l.
            { by eapply arrived_between_implies_in_arrivals; eauto 1; apply/andP; split. }
            have UNIQ: uniq l by eapply arrivals_uniq; eauto 1.
            rewrite big_mkcond [\sum_(_ <- _ | _ _ _)_]big_mkcond //=.
            rewrite (bigD1_seq j0); [simpl | by done | by done].
            rewrite (bigD1_seq j0); [simpl | by done | by done].
            rewrite /hep HP0.
            rewrite -add1n addnA [1 + _]addnC addn1.
            apply leq_add; last first.
            {
              apply leq_sum; intros j1 NEQ.
              destruct (hep_job j1 j); last by done.
                by apply cumulative_service_le_job_cost, ideal_proc_model_provides_unit_service.
            }
            rewrite ignore_service_before_arrival; rewrite //; [| by apply ltnW].
            rewrite <- ignore_service_before_arrival with (t2:=0); rewrite //; [|by apply ltnW].
              by rewrite ltnNge; apply/negP.
          Qed.               
          
          (** Using the two lemmas above, we infer that the workload is larger than the
                 interval length. However, this contradicts the assumption H_workload_is_bounded. *)
          Corollary busy_interval_workload_larger_than_interval:
            priority_inversion_bound + hp_workload t1 (t1 + delta)  > delta.
          Proof.
            apply leq_ltn_trans with (priority_inversion_bound + hp_service t1 (t1 + delta)).
            apply busy_interval_has_uninterrupted_service.
            rewrite ltn_add2l.
            apply busy_interval_too_much_workload.
          Qed.
          
        End CannotBeBusyForSoLong.  

        (** Since the interval cannot remain busy for so long, we prove that
               the busy interval finishes at some point t2 <= t1 + delta. *)
        Lemma busy_interval_is_bounded:
          exists t2,
            t2 <= t1 + delta /\
            busy_interval t1 t2.
        Proof. 
          move: H_is_busy_prefix => [LT [QT [NQ NEQ]]].
          destruct ([exists t2:'I_(t1 + delta).+1, (t2 > t1) && quiet_time_dec t2]) eqn:EX.
          - have EX': exists (t2 : instant), ((t1 < t2 <= t1 + delta) && quiet_time_dec t2).
            { move: EX => /existsP [t2 /andP [LE QUIET]].
              exists t2; apply/andP; split; last by done.
                by apply/andP; split; last (rewrite -ltnS; apply ltn_ord). }
            move: (ex_minnP EX') => [t2 /andP [/andP [GT LE] QUIET] MIN]; clear EX EX'.
            exists t2; split; [ | split; [repeat split | ]]; try done.
            + move => t /andP [GT1 LT2] BUG. 
              feed (MIN t); first (apply/andP; split).
              * by apply/andP; split; last by apply leq_trans with (n := t2); eauto using ltnW. 
              * apply/allP; intros j_hp ARR; apply/implyP; intro HP.
                apply BUG; eauto 2 using in_arrivals_implies_arrived, ARR, in_arrivals_implies_arrived_before.
                  by apply leq_ltn_trans with (p := t2) in MIN; first by rewrite ltnn in MIN.
            + move: NEQ => /andP [IN1 IN2].
              apply/andP; split; first by done.
              apply leq_ltn_trans with t_busy; eauto 2.
              rewrite ltnNge; apply/negP; intros CONTR.
              apply NQ with t2.
              * by apply/andP; split; last rewrite ltnS.
              * intros jhp ARR HP AB. 
                move: QUIET => /allP QUIET; feed (QUIET jhp).
                eapply arrived_between_implies_in_arrivals; eauto 2.
                  by move: QUIET => /implyP QUIET; apply QUIET.
            + intros j_hp IN HP ARR.
              move: QUIET => /allP QUIET; feed (QUIET j_hp).
              * by eapply arrived_between_implies_in_arrivals; last apply ARR.
              * by move: QUIET => /implyP QUIET; apply QUIET.
          - apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL'.
            have ALL: forall t, t1 < t <= t1 + delta -> ~ quiet_time t.
            { move => t /andP [GTt LEt] QUIET; rewrite -ltnS in LEt.
              specialize (ALL' (Ordinal LEt)); rewrite negb_and /= GTt orFb in ALL'. 
              move: ALL' => /negP ALL'; apply ALL'; clear ALL'.
              apply/allP; intros j_hp ARR; apply/implyP; intro HP.
              apply QUIET; eauto 2 using in_arrivals_implies_arrived, ARR, in_arrivals_implies_arrived_before.
            } clear ALL'; exfalso.
            have TOOMUCH := busy_interval_workload_larger_than_interval.
            have BOUNDED := H_workload_is_bounded.
              by move: (leq_trans (TOOMUCH ALL) BOUNDED); rewrite ltnn.                  
        Qed.
        
      End UpperBound.

    End BoundingBusyInterval.

    (** In this section, we show that from a workload bound we can infer
           the existence of a busy interval. *)
    Section BusyIntervalFromWorkloadBound.

      (** Let priority_inversion_bound be a constant that bounds the length of a priority inversion. *)
      Variable priority_inversion_bound: duration.
      Hypothesis H_priority_inversion_is_bounded:
        is_priority_inversion_bounded_by priority_inversion_bound.

      (** Assume that for some positive delta, the sum of requested workload at
             time (t1 + delta) and priority inversion is bounded by delta (i.e., the supply). *)
      Variable delta: duration.
      Hypothesis H_delta_positive: delta > 0.
      Hypothesis H_workload_is_bounded:
        forall t, priority_inversion_bound + hp_workload t (t + delta) <= delta.

      (** Next, we assume that job j has positive cost, from which we can
             infer that there is a time in which j is pending. *)
      Hypothesis H_positive_cost: job_cost j > 0.

      (** Therefore there must exists a busy interval <<[t1, t2)>> that
             contains the arrival time of j. *)
      Corollary exists_busy_interval:
        exists t1 t2, 
          t1 <= job_arrival j < t2 /\
          t2 <= t1 + delta /\
          busy_interval t1 t2.
      Proof. 
        have PREFIX := exists_busy_interval_prefix.
        move: (H_workload_is_bounded) => WORK.
        feed (PREFIX (job_arrival j)).
        { apply/andP; split; first by apply leqnn.
          rewrite /completed_by /service.
          rewrite ignore_service_before_arrival // /service_during.
          rewrite big_geq; last by apply leqnn.
            by rewrite -ltnNge.
        }
        move: PREFIX => [t1 [PREFIX /andP [GE1 GEarr]]].
        have BOUNDED := busy_interval_is_bounded
                          (job_arrival j) t1  PREFIX priority_inversion_bound _ delta
                          H_delta_positive.            
        feed_n 2 BOUNDED; try done.
        move: BOUNDED => [t2 [GE2 BUSY]].
        exists t1, t2; split.
        { apply/andP; split; first by done.
          apply contraT; rewrite -leqNgt; intro BUG.
          move: BUSY PREFIX => [[LE12 _] QUIET] [_ [_ [NOTQUIET _]]].
          feed (NOTQUIET t2); first by apply/andP; split.
            by exfalso; apply NOTQUIET.
        }
          by split. 
      Qed.
      
    End BusyIntervalFromWorkloadBound.

    (** If we know that the workload is bounded, we can also use the
           busy interval to infer a response-time bound. *)
    Section ResponseTimeBoundFromBusyInterval.

      (** Let priority_inversion_bound be a constant that bounds the length of a priority inversion. *)
      Variable priority_inversion_bound: duration.
      Hypothesis H_priority_inversion_is_bounded:
        is_priority_inversion_bounded_by priority_inversion_bound.

      (** Assume that for some positive delta, the sum of requested workload at
             time (t1 + delta) and priority inversion is bounded by delta (i.e., the supply). *)
      Variable delta: duration.
      Hypothesis H_delta_positive: delta > 0.
      Hypothesis H_workload_is_bounded:
        forall t, priority_inversion_bound + hp_workload t (t + delta) <= delta.

      (** Then, job j must complete by (job_arrival j + delta). *)
      Lemma busy_interval_bounds_response_time:
        job_completed_by j (job_arrival j + delta).
      Proof.
        have BUSY := exists_busy_interval priority_inversion_bound _ delta.
        move: (posnP (@job_cost _ H2 j)) => [ZERO|POS].
        { by rewrite /job_completed_by /completed_by ZERO. }
        feed_n 4 BUSY; try by done.
        move: BUSY => [t1 [t2 [/andP [GE1 LT2] [GE2 BUSY]]]].
        apply completion_monotonic with (t := t2); try (by done);
          first by apply leq_trans with (n := t1 + delta); [| by rewrite leq_add2r].
        apply job_completes_within_busy_interval with (t1 := t1); try by done.
      Qed.

    End ResponseTimeBoundFromBusyInterval.

  End BoundingBusyInterval.

End ExistsBusyIntervalJLFP.
