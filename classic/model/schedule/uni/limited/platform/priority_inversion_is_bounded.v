Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.limited.platform.definitions
               prosa.classic.model.schedule.uni.limited.busy_interval.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Priority inversion is bounded *)
(** In this module we prove that any priority inversion that occurs in the model with bounded 
    nonpreemptive segments defined in module prosa.classic.model.schedule.uni.limited.platform.definitions 
    is bounded. *)
Module PriorityInversionIsBounded.

  Import Job Priority UniprocessorSchedule LimitedPreemptionPlatform BusyIntervalJLFP. 

  Section PriorityInversionIsBounded.

    Context {Task: eqType}.
    Variable task_max_nps task_cost: Task -> time.    
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_max_nps job_cost: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    
    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched. 
    
    (* Consider a JLFP policy that indicates a higher-or-equal priority relation,
       and assume that the relation is reflexive and transitive. *)
    Variable higher_eq_priority: JLFP_policy Job.
    Hypothesis H_priority_is_reflexive: JLFP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: JLFP_is_transitive higher_eq_priority.

    (* We consider an arbitrary function can_be_preempted which defines 
       a preemption model with bounded nonpreemptive segments. *)
    Variable can_be_preempted: Job -> time -> bool.
    Let preemption_time := preemption_time sched can_be_preempted.
    Hypothesis H_correct_preemption_model:
      correct_preemption_model arr_seq sched can_be_preempted.
    Hypothesis H_model_with_bounded_nonpreemptive_segments:
      model_with_bounded_nonpreemptive_segments
        job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps. 

    (* Next, we assume that the schedule is a work-conserving schedule... *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

    (* ... and the schedule respects the policy defined by the 
       can_be_preempted function (i.e., bounded nonpreemptive segments). *)
    Hypothesis H_respects_policy:
      respects_JLFP_policy_at_preemption_point
        job_arrival job_cost arr_seq sched can_be_preempted higher_eq_priority.

    (* Let's define some local names for clarity. *)
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.

    (* Finally, we introduce the notion of the maximal length of (potential) priority 
       inversion at a time instant t, which is defined as the maximum length of 
       nonpreemptive segments among all jobs that arrived so far. Note that 
       the value [job_max_nps j_lp] is at least ε for any job j_lp, so the maximal
       length of priority inversion cannot be negative. *)
    Definition max_length_of_priority_inversion (j: Job) (t: time) :=
      \max_(j_lp <- jobs_arrived_before arr_seq t | ~~ higher_eq_priority j_lp j)
       (job_max_nps j_lp - ε).

    (** Next we prove that a priority inversion of a job is bounded by 
        function max_length_of_priority_inversion. *)

    (** Note that any bound on function max_length_of_priority_inversion will also be 
        a bound on the maximal priority inversion. This bound may be different 
        for different scheduler and/or task models. Thus, we don't define such a bound 
        in this module. *)

    (* Consider any job j of tsk with positive job cost. *)
    Variable j: Job.
    Hypothesis H_j_arrives: arrives_in arr_seq j.
    Hypothesis H_job_cost_positive: job_cost_positive job_cost j.
    
    (* Consider any busy interval prefix [t1, t2) of job j. *)
    Variable t1 t2: time.
    Hypothesis H_busy_interval_prefix:
      busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2.
    
    (* In this section, we prove that at any time instant after any preemption point
       (inside the busy interval), the processor is always busy scheduling a 
       job with higher or equal priority. *)
    Section PreemptionTimeAndPriorityInversion. 
      
      (* First, we show that the processor at any preemptive point is always 
         busy scheduling a job with higher or equal priority. *)
      Lemma not_quiet_implies_exists_scheduled_hp_job_at_preemption_point:
        forall t, 
          t1 <= t < t2 ->
          preemption_time t ->
          exists j_hp,
            arrived_between job_arrival j_hp t1 t2 /\
            higher_eq_priority j_hp j /\
            job_scheduled_at j_hp t.
      Proof.
        move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET INBI]]].
        rename H_work_conserving into WORK, H_respects_policy into PRIO,
        H_jobs_come_from_arrival_sequence into CONS.
        move => t /andP [GEt LEt] PREEMPTP.            
        have NOTIDLE := not_quiet_implies_not_idle
                          job_arrival job_cost arr_seq _
                          sched higher_eq_priority j _ _ _ _ _ t1 t2 _ t.
        feed_n 8 NOTIDLE; eauto 2.
        unfold is_idle, FP_is_transitive, transitive in *.
        destruct (sched t) as [j_hp|] eqn:SCHED; [clear NOTIDLE | by exfalso; apply NOTIDLE].
        move: SCHED => /eqP SCHED.
        exists j_hp.
        have HP: higher_eq_priority j_hp j.
        { apply contraT; move => /negP NOTHP; exfalso.
          have TEMP: t <= t2.-1; first by rewrite -subn1 subh3 // addn1.
          rewrite leq_eqVlt in TEMP; move: TEMP => /orP [/eqP EQUALt2m1 | LTt2m1];
                                                    first rewrite leq_eqVlt in GEt; first move: GEt => /orP [/eqP EQUALt1 | LARGERt1].
          { subst t; clear LEt.
            rewrite -EQUALt1 in SCHED; move: EQUALt1 => /eqP EQUALt1.
            destruct (job_scheduled_at j t1) eqn:SCHEDj.
            { simpl. have EQ:= only_one_job_scheduled sched j j_hp t1 SCHEDj SCHED.
                by subst j; apply NOTHP. 
            }
            { apply NOTHP.
              apply PRIO with t1; try done.
              - by move: EQUALt1 => /eqP EQUALt1; rewrite EQUALt1.
              - apply/andP; split; last first.
                + by move: SCHEDj; rewrite /job_scheduled_at; move => /negP /negP SCHEDj.
                + have EQ: t1 = job_arrival j.
                  { rewrite -eqSS in EQUALt1.
                    have EQ: t2 = t1.+1.
                    { rewrite prednK in EQUALt1; first by apply/eqP; rewrite eq_sym.
                      apply negbNE; rewrite -eqn0Ngt; apply/neqP; intros EQ0.
                      move: INBI; rewrite EQ0; move => /andP [_ CONTR].
                        by rewrite ltn0 in CONTR.
                    } clear EQUALt1.
                      by move: INBI; rewrite EQ ltnS -eqn_leq; move => /eqP INBI.
                  }
                    by rewrite EQ; eapply job_pending_at_arrival; eauto 2.
            } 
          }
          { feed (NOTQUIET t); first by apply/andP; split.
            apply NOTQUIET; intros j_hp' IN HP ARR.
            apply contraT; move => /negP NOTCOMP'; exfalso.
            have BACK: backlogged job_arrival job_cost sched j_hp' t.
            { apply/andP; split.
              - apply/andP; split. unfold arrived_before, has_arrived in *. by rewrite ltnW. 
                apply/negP; intro COMP; apply NOTCOMP'.
                  by apply completion_monotonic with (t0 := t).
              - apply/negP; intro SCHED'.
                apply only_one_job_scheduled with (j1 := j_hp) in SCHED'; last by done.
                  by apply NOTHP; subst. 
            }
            feed (PRIO j_hp' j_hp t PREEMPTP IN BACK); first by done.
              by apply NOTHP; apply H_priority_is_transitive with j_hp'. 
          }
          {
            unfold quiet_time in *.
            feed (NOTQUIET t.+1). apply/andP; split.
            - by apply leq_ltn_trans with t1.
            - rewrite -subn1 ltn_subRL addnC in LTt2m1.
                by rewrite -[t.+1]addn1.
                apply NOTQUIET.
                unfold quiet_time in *; intros j_hp' IN HP ARR.
                apply contraT; move => /negP NOTCOMP'; exfalso.
                have BACK: backlogged job_arrival job_cost sched j_hp' t.
                { apply/andP; split; last first.
                  { apply/negP; intro SCHED'.
                    apply only_one_job_scheduled with (j1 := j_hp) in SCHED'; last by done.
                    apply NOTHP.
                      by subst. 
                  }
                  apply/andP; split. unfold arrived_before, has_arrived in *. by done. 
                  apply/negP; intro COMP; apply NOTCOMP'.
                    by apply completion_monotonic with (t0 := t).
                }
                feed (PRIO j_hp' j_hp t PREEMPTP IN BACK); first by done.
                  by apply NOTHP; apply H_priority_is_transitive with j_hp'. 
          }
        }
        repeat split; [| by done | by done].
        move: (SCHED) => PENDING.
        eapply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING; [| by eauto | by done].
        apply/andP; split; last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _]. 
        apply contraT; rewrite -ltnNge; intro LT; exfalso.
        feed (QUIET j_hp); first by eapply CONS, SCHED.
        specialize (QUIET HP LT).
        have COMP: job_completed_by j_hp t by apply completion_monotonic with (t0 := t1).
        apply completed_implies_not_scheduled in COMP; last by done.
          by move: COMP => /negP COMP; apply COMP.
      Qed.

      (* In addition, we prove that every nonpreemptive segment 
         always begins with a preemption time. *)
      Lemma scheduling_of_any_segment_starts_with_preemption_time: 
        forall j t,
          job_scheduled_at j t ->
          exists pt,
            job_arrival j <= pt <= t /\
            preemption_time pt /\
            (forall t', pt <= t' <= t -> job_scheduled_at j t').
      Proof. 
        intros s t SCHEDst.
        have EX: exists t',
            (t' <= t)
              && (job_scheduled_at s t')
              && (all (fun t'' => job_scheduled_at s t'') (iota t' (t - t').+1 )).
        { exists t.
          apply/andP; split; [ by apply/andP; split | ].
          apply/allP; intros t'.
          rewrite mem_iota.
          rewrite subnn addn1 ltnS -eqn_leq.
            by move => /eqP EQ; subst t'. } 
        have MIN := ex_minnP EX. 
        move: MIN => [mpt /andP [/andP [LT1 SCHEDsmpt] /allP ALL] MIN]; clear EX.
        destruct mpt.
        { exists 0; repeat split.
          - apply/andP; split; last by done.
              by apply H_jobs_must_arrive_to_execute in SCHEDsmpt.
          - by eapply zero_is_pt; eauto 2.
          - by intros; apply ALL; rewrite mem_iota subn0 add0n ltnS. }
        { have NSCHED: ~~ job_scheduled_at s mpt.
          { apply/negP; intros SCHED. 
            feed (MIN mpt).
            apply/andP; split; [by apply/andP; split; [ apply ltnW | ] | ].
            apply/allP; intros t'.
            rewrite mem_iota addnS ltnS. 
            move => /andP [GE LE].
            move: GE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LT].
            subst t'. by done.
            apply ALL.
            rewrite mem_iota addnS ltnS.
            apply/andP; split; first by done.
            apply leq_trans with (mpt + (t - mpt)); first by done.
            rewrite !subnKC; last rewrite ltnW; by done.
              by rewrite ltnn in MIN. }
          have PP: preemption_time mpt.+1.
          { apply first_moment_is_pt with (arr_seq0 := arr_seq) (j0 := s); eauto 2. }
          exists mpt.+1; repeat split; try done.
          - apply/andP; split; last by done.
              by apply H_jobs_must_arrive_to_execute in SCHEDsmpt.
          - move => t' /andP [GE LE].
            apply ALL; rewrite mem_iota.
            rewrite addnS ltnS subnKC; last by done.
              by apply/andP; split.
        }
      Qed. 
      
      (* Next we prove that at any time instant after a preemption point the
         processor is always busy with a job with higher or equal priority. *) 
      Lemma not_quiet_implies_exists_scheduled_hp_job_after_preemption_point:
        forall tp t,
          preemption_time tp ->
          t1 <= tp < t2 ->
          tp <= t < t2 ->
          exists j_hp,
            arrived_between job_arrival j_hp t1 t.+1 /\ 
            higher_eq_priority j_hp j /\
            job_scheduled_at j_hp t.
      Proof.
        move: (H_jobs_come_from_arrival_sequence) (H_work_conserving) => CONS WORK.
        move: (H_respects_policy) => PRIO.              
        move => tp t PRPOINT /andP [GEtp LTtp] /andP [LEtp LTt].
        have NOTIDLE := not_quiet_implies_not_idle
                          job_arrival job_cost arr_seq _ sched higher_eq_priority
                          j _ _ _ _ _ t1 t2 _ t.
        feed_n 8 NOTIDLE; eauto 2.
        apply/andP; split; [by apply leq_trans with tp | by done].
        destruct (sched t) as [j_hp|] eqn:SCHED;
          last by exfalso; apply NOTIDLE; rewrite /is_idle SCHED.
        move: SCHED => /eqP SCHED.
        exists j_hp.
        have HP: higher_eq_priority j_hp j.
        { intros.
          have SOAS := scheduling_of_any_segment_starts_with_preemption_time _ _ SCHED.
          move: SOAS => [prt [/andP [_ LE] [PR SCH]]].
          case E:(t1 <= prt).
          - move: E => /eqP /eqP E; rewrite subn_eq0 in E.
            have EXISTS := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point prt.
            feed_n 2 EXISTS; try done.
            { by apply /andP; split; last by apply leq_ltn_trans with t. }
            move: EXISTS => [j_lp [_ [HEP SCHEDjhp]]].
            have EQ: j_hp = j_lp.
            { by apply (only_one_job_scheduled sched _ _ prt); first (apply SCH; apply/andP; split). }
              by subst j_hp. 
          - move: E => /eqP /neqP E; rewrite -lt0n subn_gt0 in E.
            apply negbNE; apply/negP; intros LP.
            rename j_hp into j_lp.
            have EXISTS := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point tp.
            feed_n 2 EXISTS; try done.
            { by apply /andP; split. }
            move: EXISTS => [j_hp [_ [HEP SCHEDjhp]]].
            have EQ: j_hp = j_lp.
            { apply (only_one_job_scheduled sched _ _ tp). 
                by done.
                apply SCH; apply/andP; split.
                apply leq_trans with t1. rewrite ltnW //. by done.
                  by done.
            }
              by subst j_hp; move: LP => /negP LP; apply: LP.
        } 
        repeat split; [| by done | by done].
        move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET EXj]]]. 
        move: (SCHED) => PENDING.
        eapply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING;
          [| by eauto | by done].
        apply/andP; split; 
          last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _].
        apply contraT; rewrite -ltnNge; intro LT; exfalso.
        feed (QUIET j_hp); first by eapply CONS, SCHED.
        specialize (QUIET HP LT).
        have COMP: job_completed_by j_hp t.
        { by apply completion_monotonic with (t0 := t1); [ apply leq_trans with tp | ]. }
        apply completed_implies_not_scheduled in COMP; last by done.
          by move: COMP => /negP COMP; apply COMP.
      Qed.

      (* Now, suppose there exists some constant K that bounds the distance to 
         a preemption time from the beginning of the busy interval. *)
      Variable K: time.
      Hypothesis H_preemption_time_exists:
        exists pr_t, preemption_time pr_t /\ t1 <= pr_t <= t1 + K.

      (* Then we prove that the processor is always busy with a job with 
         higher-or-equal priority after time instant [t1 + K]. *)
      Lemma not_quiet_implies_exists_scheduled_hp_job:
        forall t,
          t1 + K <= t < t2 ->
          exists j_hp,
            arrived_between job_arrival j_hp t1 t.+1 /\ 
            higher_eq_priority j_hp j /\
            job_scheduled_at j_hp t.
      Proof. 
        move => t /andP [GE LT].
        move: H_preemption_time_exists => [prt [PR /andP [GEprt LEprt]]].
        apply not_quiet_implies_exists_scheduled_hp_job_after_preemption_point with (tp := prt); eauto 2. 
        -  apply/andP; split; first by done.
           apply leq_ltn_trans with (t1 + K); first by done.
             by apply leq_ltn_trans with t.
        - apply/andP; split; last by done.
            by apply leq_trans with (t1 + K).
      Qed.
      
    End PreemptionTimeAndPriorityInversion.

    (* In this section we prove that the function max_length_of_priority_inversion 
       indeed upper bounds the priority inversion length. *)
    Section PreemprionTimeExists.

      (* First we prove that if a job with higher-or-equal priority is scheduled at 
         a quiet time t+1 then this is the first time when this job is scheduled. *)
      Lemma hp_job_not_scheduled_before_quiet_time:
        forall jhp t,
          quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t.+1 ->
          job_scheduled_at jhp t.+1 ->
          higher_eq_priority jhp j ->
          ~~ job_scheduled_at jhp t.
      Proof.
        intros jhp t QT SCHED1 HP.            
        apply/negP; intros SCHED2.
        specialize (QT jhp).
        feed_n 3 QT; try done.
        eapply H_jobs_come_from_arrival_sequence; eauto 1.
        rewrite /arrived_before ltnS.
        apply H_jobs_must_arrive_to_execute. by done.
        apply completed_implies_not_scheduled in QT; last by done.
          by move: QT => /negP NSCHED; apply: NSCHED.
      Qed.
      
      (* Also, we show that lower-priority jobs that are scheduled inside the
         busy-interval prefix [t1,t2) must have arrived before that interval. *)
      Lemma low_priority_job_arrives_before_busy_interval_prefix:
        forall jlp t,
          t1 <= t < t2 ->
          job_scheduled_at jlp t ->
          ~~ higher_eq_priority jlp j ->
          job_arrival jlp < t1.
      Proof.
        move => jlp t /andP [GE LT] SCHED LP.
        move: (H_busy_interval_prefix) => [NEM [QT [NQT HPJ]]].
        apply negbNE; apply/negP; intros ARR; rewrite -leqNgt in ARR.
        have SCH:= scheduling_of_any_segment_starts_with_preemption_time _ _ SCHED.
        move: SCH => [pt [/andP [NEQ1 NEQ2] [PT FA]]].
        have NEQ: t1 <= pt < t2.
        { apply/andP; split.
          apply leq_trans with (job_arrival jlp); by done.
          apply leq_ltn_trans with t; by done. }
        have LL:= not_quiet_implies_exists_scheduled_hp_job_at_preemption_point pt.
        feed_n 2 LL; try done.
        move: LL => [jhp [ARRjhp [HP SCHEDhp]]].
        feed (FA pt). apply/andP; split; by done.
        have OOJ:= only_one_job_scheduled _ _ _ _ FA SCHEDhp; subst jhp.
          by move: LP => /negP LP; apply: LP.
      Qed.

      (* Moreover, we show that lower-priority jobs that are scheduled inside the
         busy-interval prefix [t1,t2) must be scheduled before that interval. *)
      Lemma low_priority_job_scheduled_before_busy_interval_prefix:
        forall jlp t,
          t1 <= t < t2 ->
          job_scheduled_at jlp t ->
          ~~ higher_eq_priority jlp j ->
          exists t', t' < t1 /\ job_scheduled_at jlp t'.
      Proof.
        move => jlp t NEQ SCHED LP.
        have ARR := low_priority_job_arrives_before_busy_interval_prefix _ _ NEQ SCHED LP. 
        move: NEQ => /andP [GE LT].
        exists t1.-1.
        split.
        { rewrite prednK; first by done.
            by apply leq_ltn_trans with (job_arrival jlp).
        }
        { move: (H_busy_interval_prefix) => [NEM [QT [NQT HPJ]]].
          have SCHEDST := scheduling_of_any_segment_starts_with_preemption_time _ _ SCHED.
          move: SCHEDST => [pt [NEQpt [PT SCHEDc]]].
          have NEQ: pt < t1.
          { rewrite ltnNge; apply/negP; intros CONTR.
            have NQSCHED := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point pt.
            feed_n 2 NQSCHED; try done.
            { apply/andP; split; first by done.
                by apply leq_ltn_trans with t; move: NEQpt => /andP [_ T].
            }
            move: NQSCHED => [jhp [ARRhp [HPhp SCHEDhp]]].
            specialize (SCHEDc pt).
            feed SCHEDc.
            { by apply/andP; split; last move: NEQpt => /andP [_ T]. }
            have EQ:= only_one_job_scheduled sched jhp jlp pt.
            feed_n 2 EQ; try done.
            subst jhp.
              by move: LP => /negP LP; apply: LP.
          }
          apply SCHEDc; apply/andP; split.
          - rewrite -addn1 in NEQ.
            apply subh3 in NEQ.
              by rewrite subn1 in NEQ.
          - apply leq_trans with t1. by apply leq_pred. by done.
        }
        Qed.
      
      (* Thus, there must be a preemption time in the interval [t1, t1 + max_priority_inversion t1]. 
         That is, if a job with higher-or-equal priority is scheduled at time instant t1, then t1 is 
         a preemprion time. Otherwise, if a job with lower priority is scheduled at time t1, 
         then this jobs also should be scheduled before the beginning of the busy interval. So, the 
         next preemption time will be no more than [max_priority_inversion t1] time units later. *)
      Lemma preemption_time_exists: 
        exists pr_t,
          preemption_time pr_t /\
          t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
      Proof.
        set (service := service sched).
        move: (H_correct_preemption_model) => CORR.
        move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
        case SCHED: (sched t1) => [s | ]; move: SCHED => /eqP SCHED; last first. 
        { exists t1; split; last first.
          apply/andP; split; [by done | by rewrite leq_addr].
          move: SCHED => /eqP SCHED.
          rewrite /preemption_time /LimitedPreemptionPlatform.preemption_time.
            by rewrite SCHED.
        }
        { case PRIO: (higher_eq_priority s j).
          { exists t1; split; last first.
            apply/andP; split; [by done | by rewrite leq_addr].
            destruct t1.
            { eapply zero_is_pt; [eauto 2 | apply H_jobs_come_from_arrival_sequence]. }
            eapply hp_job_not_scheduled_before_quiet_time in QT1; eauto 2.
            eapply first_moment_is_pt with (j0 := s); eauto 2.
          } 
          { move: (SCHED) => ARRs; apply H_jobs_come_from_arrival_sequence in ARRs.
            move: (H_model_with_bounded_nonpreemptive_segments s ARRs) => [_ [_ [_ EXPP]]].
            move: (EXPP (service s t1)) => PP; clear EXPP.
            feed PP. by apply/andP; split; [done | apply H_completed_jobs_dont_execute].                
            have EX: exists pt,
                ((service s t1) <= pt <= (service s t1) + (job_max_nps s - 1))
                  && can_be_preempted s pt.
            { move: PP => [pt [NEQ PP]].
              exists pt; apply/andP; split; by done.
            } clear PP. 
            have MIN := ex_minnP EX.
            move: MIN => [sm_pt /andP [NEQ PP] MIN]; clear EX.
            have Fact: exists Δ, sm_pt = service s t1 + Δ.
            { exists (sm_pt - service s t1).
              apply/eqP; rewrite eq_sym; apply/eqP; rewrite subnKC //.
                by move: NEQ => /andP [T _]. }
            move: Fact => [Δ EQ]; subst sm_pt; rename Δ into sm_pt.
            exists (t1 + sm_pt); split.
            { have Fact1: 
                forall prog, service s t1 <= prog < service s t1 + sm_pt ->
                        ~~ can_be_preempted s prog. 
              { move => prog /andP [GE LT].
                apply/negP; intros PPJ.
                feed (MIN prog); first (apply/andP; split); try done.
                - apply/andP; split; first by done.
                  apply leq_trans with (service s t1 + sm_pt).
                  + by apply ltnW. 
                  + by move: NEQ => /andP [_ K].
                - by move: MIN; rewrite leqNgt; move => /negP NLT; apply: NLT.
              } 
              have Fact2: forall t', t1 <= t' < t1 + sm_pt -> job_scheduled_at s t'.
              { 
                move => t' /andP [GE LT]. 
                have Fact: exists Δ, t' = t1 + Δ.
                { by exists (t' - t1); apply/eqP; rewrite eq_sym; apply/eqP; rewrite subnKC.  }
                move: Fact => [Δ EQ]; subst t'.
                move: (Fact1 (service s (t1 + Δ)))(CORR s) => NPPJ T.
                feed T; first by done. move: T => [T _ ].
                apply: T; apply: NPPJ.
                apply/andP; split.
                { by apply Service.service_monotonic; rewrite leq_addr. }
                rewrite /service /UniprocessorSchedule.service (@Service.service_during_cat _ _ _ t1).
                { rewrite ltn_add2l; rewrite ltn_add2l in LT.
                  apply leq_ltn_trans with Δ; last by done.
                  rewrite -{2}(sum_of_ones t1 Δ).
                  rewrite leq_sum //; clear; intros t _.
                    by rewrite /service_at; destruct (scheduled_at sched s t). }
                { by apply/andP; split; [done | rewrite leq_addr]. } 
              }
              rewrite /preemption_time /LimitedPreemptionPlatform.preemption_time.
              case SCHEDspt: (sched (t1 + sm_pt)) => [s0 | ]; last by done.
              move: SCHEDspt => /eqP SCHEDspt.
              destruct (s == s0) eqn: EQ.
              { move: EQ => /eqP EQ; subst s0.
                rewrite /UniprocessorSchedule.service.
                rewrite (@Service.service_during_cat _ _ _ t1); last first.
                { by apply/andP; split; [ done | rewrite leq_addr]. }
                have ALSCHED: service_during sched s t1 (t1 + sm_pt) = sm_pt.
                { rewrite -{2}(sum_of_ones t1 sm_pt) /service_during.
                  apply/eqP; rewrite eqn_leq //; apply/andP; split.
                  { rewrite leq_sum //; clear; intros t _.
                      by unfold service_at; destruct (scheduled_at sched s t). }
                  { rewrite big_nat_cond [in X in _ <= X]big_nat_cond.
                    rewrite leq_sum //.
                    move => x /andP [HYP _].
                    rewrite lt0b. 
                      by apply Fact2.
                  } 
                } 
                  by rewrite ALSCHED.
              } 
              destruct sm_pt.
              { exfalso; move: EQ => /negP EQ; apply: EQ.
                move: SCHED SCHEDspt => /eqP SCHED /eqP SCHEDspt.
                rewrite addn0 in SCHEDspt; rewrite SCHEDspt in SCHED.
                  by inversion SCHED. }
              { rewrite addnS.
                move: (H_correct_preemption_model s0) => T.
                feed T; first by eauto 2. move: T => [_ T]; apply: T.
                apply /negP; intros CONTR.
                move: EQ => /negP EQ; apply: EQ.
                move: (Fact2 (t1 + sm_pt)) => SCHEDs0.
                feed SCHEDs0; first by apply/andP; split; [rewrite leq_addr | rewrite addnS].
                apply/eqP; eapply only_one_job_scheduled; eauto 2.
                  by rewrite -addnS.
              } 
            } 
            move: NEQ => /andP [GE LE].
            apply/andP; split; first by rewrite leq_addr.
            rewrite leq_add2l.
            unfold max_length_of_priority_inversion.
            rewrite (big_rem s) //=.
            { rewrite PRIO; simpl.
              apply leq_trans with (job_max_nps s - ε); last by rewrite leq_maxl.
                by rewrite leq_add2l in LE. }
            eapply arrived_between_implies_in_arrivals; eauto 2.
            apply/andP; split; first by done.
            eapply low_priority_job_arrives_before_busy_interval_prefix with t1; eauto 2.
              by rewrite PRIO.
          }
        }
      Qed.

    End PreemprionTimeExists.

  End PriorityInversionIsBounded. 
  
End PriorityInversionIsBounded.