Require Export prosa.model.task.preemption.parameters.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.definitions.busy_interval.
Require Export prosa.analysis.facts.model.ideal_schedule.
Require Export prosa.analysis.facts.busy_interval.busy_interval.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.

(** Throughout the file we assume for the classic Liu & Layland model
    of readiness without jitter and no self-suspensions, where
    pending jobs are always ready. *)
Require Import prosa.model.readiness.basic.

(** In preparation of the derivation of the priority inversion bound, we
    establish two basic facts on preemption times. *)
Section PreemptionTimes.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume the existence of a function mapping a
      task to its maximal non-preemptive segment ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and the existence of a function mapping a job and
      its progress to a boolean value saying whether this job is
      preemptable at its current point of execution. *)
  Context `{JobPreemptable Job}.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any ideal uniprocessor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** Consider a valid model with bounded nonpreemptive segments. *)
  Hypothesis H_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Then, we show that time 0 is a preemption time. *)
  Lemma zero_is_pt: preemption_time sched 0.
  Proof.
    unfold preemption_time.
    case SCHED: (sched 0) => [j | ]; last by done.
    move: (SCHED) => /eqP; rewrite -scheduled_at_def; move => ARR.
    apply H_jobs_come_from_arrival_sequence in ARR.
    rewrite /service /service_during big_geq; last by done.
    destruct H_model_with_bounded_nonpreemptive_segments as [T1 T2].
    by move: (T1 j ARR) => [PP _].
  Qed.

  (** Also, we show that the first instant of execution is a preemption time. *)
  Lemma first_moment_is_pt:
    forall j prt,
      arrives_in arr_seq j ->
      ~~ scheduled_at sched j prt ->
      scheduled_at sched j prt.+1 ->
      preemption_time sched prt.+1.
  Proof.
    intros s pt ARR NSCHED SCHED.
    unfold preemption_time.
    move: (SCHED); rewrite scheduled_at_def; move => /eqP SCHED2; rewrite SCHED2; clear SCHED2.
    destruct H_model_with_bounded_nonpreemptive_segments as [T1 T2].
    by move: (T1 s ARR) => [_ [_ [_ P]]]; apply P.
  Qed.

End PreemptionTimes.

(** * Priority inversion is bounded *)
(** In this module we prove that any priority inversion that occurs in the model with bounded 
    nonpreemptive segments defined in module prosa.model.schedule.uni.limited.platform.definitions 
    is bounded. *)
Section PriorityInversionIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** Consider any arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and any ideal uniprocessor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.
      
  (** Consider a JLFP policy that indicates a higher-or-equal priority relation,
      and assume that the relation is reflexive and transitive. *)
  Context `{JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive: reflexive_priorities.
  Hypothesis H_priority_is_transitive: transitive_priorities.

  (** In addition, we assume the existence of a function mapping a
      task to its maximal non-preemptive segment ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and the existence of a function mapping a job and its
      progress to a boolean value saying whether this job is
      preemptable at its current point of execution. *)
  Context `{JobPreemptable Job}.

  (** And assume that they define a valid preemption model with
     bounded nonpreemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  
  (** ... and the schedule respects the policy defined by the
       predicate [job_preemptable] (i.e., bounded nonpreemptive
       segments). *)
  Hypothesis H_respects_policy:
    respects_policy_at_preemption_point arr_seq sched.
  
  (** Let's define some local names for clarity. *)
  Let job_scheduled_at := scheduled_at sched.
  Let job_completed_by := completed_by sched.

  (** Finally, we introduce the notion of the maximal length of
       (potential) priority inversion at a time instant [t], which is
       defined as the maximum length of nonpreemptive segments among
       all jobs that arrived so far. Note that the value
       [job_max_nonpreemptive_segment j_lp] is at least [ε] for any job
       [j_lp], so the maximal length of priority inversion cannot be
       negative. *)
  Definition max_length_of_priority_inversion (j : Job) (t : instant) :=
    \max_(j_lp <- arrivals_before arr_seq t | ~~ hep_job j_lp j)
     (job_max_nonpreemptive_segment j_lp - ε).

  (** Next we prove that a priority inversion of a job is bounded by 
      function [max_length_of_priority_inversion]. *)

  (** Note that any bound on function
      [max_length_of_priority_inversion] will also be a bound on the
      maximal priority inversion. This bound may be different for
      different scheduler and/or task models. Thus, we don't define
      such a bound in this module. *)

  (** Consider any job [j] of [tsk] with positive job cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.
  
  (** Consider any busy interval prefix <<[t1, t2)>> of job j. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval_prefix:
    busy_interval_prefix arr_seq sched j t1 t2.

  (** * Processor Executes HEP jobs after Preemption Point *)
  (** In this section, we prove that at any time instant after any preemption point
     (inside the busy interval), the processor is always busy scheduling a 
     job with higher or equal priority. *)
  Section PreemptionTimeAndPriorityInversion. 

    (** First, we show that the processor at any preemptive point is always 
        busy scheduling a job with higher or equal priority. *)     
    Section ProcessorBusyWithHEPJobAtPreemptionPoints.

      (** Consider an arbitrary preemption time t ∈ <<[t1,t2)>>. *)
      Variable t : instant.
      Hypothesis H_t_in_busy_interval : t1 <= t < t2.
      Hypothesis H_t_preemption_time : preemption_time sched t.

      (** First note since [t] lies inside the busy interval, 
          the processor cannot be idle at time [t]. *)
      Lemma instant_t_is_not_idle:
        ~ is_idle sched t.
      Proof.
        intros Idle.
          by exfalso; eapply not_quiet_implies_not_idle with (t0 := t); eauto 2.
      Qed.
      
      (** Next we consider two cases: (1) when [t] is less than [t2 - 1] and (2) [t] is equal to [t2 - 1]. *)
      Lemma t_lt_t2_or_t_eq_t2:
        t < t2.-1 \/ t = t2.-1.
      Proof.
        have TEMP: t <= t2.-1.
        { move: (H_t_in_busy_interval) => /andP [GEt LEt]. 
            by rewrite -subn1 subh3 // addn1.
        }
        rewrite leq_eqVlt in TEMP; move: TEMP => /orP [/eqP EQUALt2m1 | LTt2m1].
        - right; auto.
        - left; auto.
      Qed.      

      (** In case when [t < t2 - 1], we use the fact that time instant
          [t+1] is not a quiet time. The later implies that there is a
          pending higher-or-equal priority job at time [t]. Thus, the
          assumption that the schedule respects priority policy at
          preemption points implies that the scheduled job must have a
          higher-or-equal priority. *)
      Lemma scheduled_at_preemption_time_implies_higher_or_equal_priority_lt:
        t < t2.-1 -> 
        forall jhp, 
          scheduled_at sched jhp t ->
          hep_job jhp j.
      Proof.
        intros LTt2m1 jhp Sched_jhp.
        move: (H_t_in_busy_interval) (H_busy_interval_prefix) => /andP [GEt LEt] [SL [QUIET [NOTQUIET INBI]]]. 
        apply contraT; move => /negP NOTHP; exfalso. 
        apply NOTQUIET with (t := t.+1).
        { apply/andP; split.
          - by apply leq_ltn_trans with t1.
          - rewrite -subn1 ltn_subRL addnC in LTt2m1.
              by rewrite -[t.+1]addn1.
        }
        intros j_hp' IN HP ARR.
        apply contraT; move => /negP NOTCOMP'; exfalso.
        have BACK: backlogged sched j_hp' t.
        { apply/andP; split; last first.
          { apply/negP; intro SCHED'.
            move: (ideal_proc_model_is_a_uniprocessor_model jhp j_hp' sched t Sched_jhp SCHED') => EQ; subst.
              by apply: NOTHP.
          } 
          apply/andP; split. unfold arrived_before, has_arrived in *. by done. 
          apply/negP; intro COMP; apply NOTCOMP'.
            by apply completion_monotonic with (t0 := t).
        }
        apply NOTHP, (H_priority_is_transitive t j_hp'); eauto 2.
      Qed.
      
      (** In case when [t = t2 - 1], we cannot use the same proof
          since [t+1 = t2], but [t2] is a quiet time. So we do a
          similar case analysis on the fact that [t1 = t ∨ t1 < t]. *)
      Lemma scheduled_at_preemption_time_implies_higher_or_equal_priority_eq:
        t = t2.-1 ->
        forall jhp, 
          scheduled_at sched jhp t ->
          hep_job jhp j.
      Proof.
        intros EQUALt2m1 jhp Sched_jhp.
        move: (H_t_in_busy_interval) (H_busy_interval_prefix) => /andP [GEt LEt] [SL [QUIET [NOTQUIET INBI]]]. 
        apply contraT; move => /negP NOTHP; exfalso. 
        rewrite leq_eqVlt in GEt; first move: GEt => /orP [/eqP EQUALt1 | LARGERt1].
        - subst t; clear LEt.
          rewrite -EQUALt1 in Sched_jhp; move: EQUALt1 => /eqP EQUALt1.
          destruct (job_scheduled_at j t1) eqn:SCHEDj.
          + apply NOTHP; erewrite (ideal_proc_model_is_a_uniprocessor_model j jhp); eauto.
              by apply (H_priority_is_reflexive 0).
          + eapply NOTHP, (H_respects_policy _ _ t2.-1); auto;
              last by rewrite -(eqbool_to_eqprop EQUALt1).
            apply/andP; split; last first.
            * by rewrite -(eqbool_to_eqprop EQUALt1); unfold job_scheduled_at in *; rewrite SCHEDj.
            * have EQ: t1 = job_arrival j.
              { rewrite -eqSS in EQUALt1.
                have EQ: t2 = t1.+1.
                { rewrite prednK in EQUALt1; first by apply/eqP; rewrite eq_sym.
                  apply negbNE; rewrite -eqn0Ngt; apply/neqP; intros EQ0.
                  move: INBI; rewrite EQ0; move => /andP [_ CONTR].
                    by rewrite ltn0 in CONTR.
                } clear EQUALt1.
                  by move: INBI; rewrite EQ ltnS -eqn_leq; move => /eqP INBI.
              }
                by rewrite -(eqbool_to_eqprop EQUALt1) EQ; eapply job_pending_at_arrival; eauto 2.                  
        - feed (NOTQUIET t); first by apply/andP; split.
          apply NOTQUIET; intros j_hp' IN HP ARR.
          apply contraT; move => /negP NOTCOMP'; exfalso.
          have BACK: backlogged sched j_hp' t.
          { apply/andP; split.
            - apply/andP; split. unfold arrived_before, has_arrived in *. by rewrite ltnW. 
              apply/negP; intro COMP; apply NOTCOMP'.
                by apply completion_monotonic with (t0 := t).
            - apply/negP; intro SCHED'.
              move: (ideal_proc_model_is_a_uniprocessor_model jhp j_hp' sched t Sched_jhp SCHED') => EQ; subst.
                by apply: NOTHP.
          } 
          apply NOTHP, (H_priority_is_transitive t j_hp'); eauto 2.
      Qed.

      (** By combining the above facts we conclude that a job that is
          scheduled at time [t] has higher-or-equal priority. *)
      Corollary scheduled_at_preemption_time_implies_higher_or_equal_priority:
        forall jhp, 
          scheduled_at sched jhp t ->
          hep_job jhp j.
      Proof.
        move: (H_t_in_busy_interval) (H_busy_interval_prefix) => /andP [GEt LEt] [SL [QUIET [NOTQUIET INBI]]]. 
        destruct t_lt_t2_or_t_eq_t2.
        - by apply scheduled_at_preemption_time_implies_higher_or_equal_priority_lt. 
        - by apply scheduled_at_preemption_time_implies_higher_or_equal_priority_eq. 
      Qed.

      (** Since a job that is scheduled at time [t] has higher-or-equal priority, 
          by properties of a busy interval it cannot arrive before time instant [t1]. *)
      Lemma scheduled_at_preemption_time_implies_arrived_between_within_busy_interval:
        forall jhp, 
          scheduled_at sched jhp t ->
          arrived_between jhp t1 t2.
      Proof.
        intros jhp Sched_jhp.
        rename H_work_conserving into WORK, H_jobs_come_from_arrival_sequence into CONS.
        move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET INBI]]]. 
        move: (H_t_in_busy_interval) => /andP [GEt LEt].
        have HP := scheduled_at_preemption_time_implies_higher_or_equal_priority _ Sched_jhp.
        move: (Sched_jhp) => PENDING.
        eapply scheduled_implies_pending in PENDING; eauto 2 with basic_facts.
        apply/andP; split; last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _]. 
        apply contraT; rewrite -ltnNge; intro LT; exfalso.
        feed (QUIET jhp); first by eapply CONS, Sched_jhp.
        specialize (QUIET HP LT).
        have COMP: job_completed_by jhp t by apply completion_monotonic with (t0 := t1).
        apply completed_implies_not_scheduled in COMP; last by done.
          by move: COMP => /negP COMP; apply COMP.
      Qed.      

      (** From the above lemmas we prove that there is a job [jhp] that is (1) scheduled at time [t],
          (2) has higher-or-equal priority, and (3) arrived between [t1] and [t2].   *)
      Corollary not_quiet_implies_exists_scheduled_hp_job_at_preemption_point:
        exists j_hp,
          arrived_between j_hp t1 t2 /\
          hep_job j_hp j /\
          job_scheduled_at j_hp t.
      Proof.
        move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET INBI]]]. 
        move: (H_t_in_busy_interval) => /andP [GEt LEt].
        ideal_proc_model_sched_case_analysis sched t jhp.
        { by exfalso; apply instant_t_is_not_idle. }
        exists jhp.
        repeat split.
        - by apply scheduled_at_preemption_time_implies_arrived_between_within_busy_interval.
        - by apply scheduled_at_preemption_time_implies_higher_or_equal_priority.
        - by done.
      Qed.        

    End ProcessorBusyWithHEPJobAtPreemptionPoints.
    
    (** Next we prove that every nonpreemptive segment 
        always begins with a preemption time ... *)
    Lemma scheduling_of_any_segment_starts_with_preemption_time: 
      forall j t,
        job_scheduled_at j t ->
        exists pt,
          job_arrival j <= pt <= t /\
          preemption_time sched pt /\
          (forall t', pt <= t' <= t -> job_scheduled_at j t').
    Proof.
      intros s t SCHEDst.
      have EX: exists t', (t' <= t) && (job_scheduled_at s t')
                              && (all (fun t'' => job_scheduled_at s t'') (index_iota t' t.+1 )).
      { exists t. apply/andP; split; [ by apply/andP; split | ].
        apply/allP; intros t'.
          by rewrite mem_index_iota ltnS -eqn_leq; move => /eqP <-.  
      } 
      have MIN := ex_minnP EX. 
      move: MIN => [mpt /andP [/andP [LT1 SCHEDsmpt] /allP ALL] MIN]; clear EX.
      destruct mpt.
      - exists 0; repeat split.
        + by apply/andP; split; first apply H_jobs_must_arrive_to_execute in SCHEDsmpt.
        + by eapply zero_is_pt; eauto 2.
        + by intros; apply ALL; rewrite mem_iota subn0 add0n ltnS.
      - have NSCHED: ~~ job_scheduled_at s mpt.
        { apply/negP; intros SCHED.
          enough (F : mpt < mpt); first by rewrite ltnn in F.
          apply MIN.
          apply/andP; split; [by apply/andP; split; [ apply ltnW | ] | ].
          apply/allP; intros t'.
          rewrite mem_index_iota; move => /andP [GE LE].
          move: GE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LT].
          - by subst t'. 
          - by apply ALL; rewrite mem_index_iota; apply/andP; split. 
        }         
        have PP: preemption_time sched mpt.+1.
        { by eapply first_moment_is_pt with (j0 := s); eauto 2. }
        exists mpt.+1; repeat split; try done.
        + apply/andP; split; last by done.
            by apply H_jobs_must_arrive_to_execute in SCHEDsmpt.
        + move => t' /andP [GE LE].
            by apply ALL; rewrite mem_index_iota; apply/andP; split.
    Qed.

    (** ... and the fact that at any time instant after a preemption point the
       processor is always busy with a job with higher or equal priority. *) 
    Lemma not_quiet_implies_exists_scheduled_hp_job_after_preemption_point:
      forall tp t,
        preemption_time sched tp ->
        t1 <= tp < t2 ->
        tp <= t < t2 ->
        exists j_hp,
          arrived_between j_hp t1 t.+1 /\ 
          hep_job j_hp j /\
          job_scheduled_at j_hp t.
    Proof.
      move: (H_jobs_come_from_arrival_sequence) (H_work_conserving) => CONS WORK.
      move: (H_respects_policy) => PRIO.              
      move => tp t PRPOINT /andP [GEtp LTtp] /andP [LEtp LTt].
      ideal_proc_model_sched_case_analysis_eq sched t jhp.
      { exfalso; eapply not_quiet_implies_not_idle with (t0 := t); eauto 2.
          by apply/andP; split; first apply leq_trans with tp. }
      exists jhp.
      have HP: hep_job jhp j.
      { intros.
        have SOAS := scheduling_of_any_segment_starts_with_preemption_time _ _ Sched_jhp.
        move: SOAS => [prt [/andP [_ LE] [PR SCH]]].
        case E:(t1 <= prt).
        - move: E => /eqP /eqP E; rewrite subn_eq0 in E.
          edestruct not_quiet_implies_exists_scheduled_hp_job_at_preemption_point as [jlp [_ [HEP SCHEDjhp]]]; eauto 2.
          { by apply /andP; split; last by apply leq_ltn_trans with t. }
          enough (EQ : jhp = jlp); first by subst.
          eapply ideal_proc_model_is_a_uniprocessor_model with (t0 := prt); eauto;
            by apply SCH; apply/andP; split.
        - move: E => /eqP /neqP E; rewrite -lt0n subn_gt0 in E.
          apply negbNE; apply/negP; intros LP; rename jhp into jlp.
          edestruct not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
            as [jhp [_ [HEP SCHEDjhp]]]; [ | apply PRPOINT| ]; first by apply/andP; split.
          move: LP => /negP LP; apply: LP.
          enough (EQ : jhp = jlp); first by subst. 
          eapply ideal_proc_model_is_a_uniprocessor_model with (j1 := jhp) (t0 := tp); eauto. 
            by apply SCH; apply/andP; split; first apply leq_trans with t1; auto.
      } 
      repeat split; try done. 
      move: (H_busy_interval_prefix) => [SL [QUIET [NOTQUIET EXj]]]; move: (Sched_jhp) => PENDING.
      eapply scheduled_implies_pending in PENDING; eauto with basic_facts.
      apply/andP; split; last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _].
      apply contraT; rewrite -ltnNge; intro LT; exfalso.
      feed (QUIET jhp); first by eapply CONS, Sched_jhp.
      specialize (QUIET HP LT).
      have COMP: job_completed_by jhp t.
      { by apply completion_monotonic with (t0 := t1); [ apply leq_trans with tp | ]. }
      apply completed_implies_not_scheduled in COMP; last by done.
        by move: COMP => /negP COMP; apply COMP.
    Qed.

    (** Now, suppose there exists some constant K that bounds the distance to 
       a preemption time from the beginning of the busy interval. *)
    Variable K : duration.
    Hypothesis H_preemption_time_exists:
      exists pr_t, preemption_time sched pr_t /\ t1 <= pr_t <= t1 + K.

    (** Then we prove that the processor is always busy with a job with 
       higher-or-equal priority after time instant [t1 + K]. *)
    Lemma not_quiet_implies_exists_scheduled_hp_job:
      forall t,
        t1 + K <= t < t2 ->
        exists j_hp,
          arrived_between j_hp t1 t.+1 /\ 
          hep_job j_hp j /\
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

  (** * Preemption Time Exists *)
  (** In this section we prove that the function [max_length_of_priority_inversion] 
     indeed upper bounds the priority inversion length. *)
  Section PreemptionTimeExists.

    (** First we prove that if a job with higher-or-equal priority is scheduled at 
       a quiet time [t+1] then this is the first time when this job is scheduled. *)
    Lemma hp_job_not_scheduled_before_quiet_time:
      forall jhp t,
        quiet_time arr_seq sched j t.+1 ->
        job_scheduled_at jhp t.+1 ->
        hep_job jhp j ->
        ~~ job_scheduled_at jhp t.
    Proof.
      intros jhp t QT SCHED1 HP.            
      apply/negP; intros SCHED2.
      specialize (QT jhp).
      feed_n 3 QT; eauto.
      apply completed_implies_not_scheduled in QT; last by done.
        by move: QT => /negP NSCHED; apply: NSCHED.
    Qed.

    (** Also, we show that lower-priority jobs that are scheduled inside the
       busy-interval prefix <<[t1,t2)>> must arrive before that interval. *)
    Lemma low_priority_job_arrives_before_busy_interval_prefix:
      forall jlp t,
        t1 <= t < t2 ->
        job_scheduled_at jlp t ->
        ~~ hep_job jlp j ->
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
      feed (FA pt); first (by apply/andP; split). 
      move: LP => /negP LP; apply: LP.
        by have ->: jlp = jhp by eapply ideal_proc_model_is_a_uniprocessor_model; eauto.
    Qed.

    (** Moreover, we show that lower-priority jobs that are scheduled
        inside the busy-interval prefix <<[t1,t2)>> must be scheduled
        before that interval. *)
    Lemma low_priority_job_scheduled_before_busy_interval_prefix:
      forall jlp t,
        t1 <= t < t2 ->
        job_scheduled_at jlp t ->
        ~~ hep_job jlp j ->
        exists t', t' < t1 /\ job_scheduled_at jlp t'.
    Proof.
      move => jlp t NEQ SCHED LP; move: (NEQ) => /andP [GE LT].
      have ARR := low_priority_job_arrives_before_busy_interval_prefix _ _ NEQ SCHED LP. 
      exists t1.-1; split.
      { by rewrite prednK; last apply leq_ltn_trans with (job_arrival jlp). } 
      move: (H_busy_interval_prefix) => [NEM [QT [NQT HPJ]]].
      have SCHEDST := scheduling_of_any_segment_starts_with_preemption_time _ _ SCHED.
      move: SCHEDST => [pt [NEQpt [PT SCHEDc]]].
      have LT2: pt < t1.
      { rewrite ltnNge; apply/negP; intros CONTR.
        have NQSCHED := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point pt.
        feed_n 2 NQSCHED; try done.
        { apply/andP; split; first by done.
            by apply leq_ltn_trans with t; move: NEQpt => /andP [_ T].
        } move: NQSCHED => [jhp [ARRhp [HPhp SCHEDhp]]].
        specialize (SCHEDc pt).
        feed SCHEDc; first by apply/andP; split; last move: NEQpt => /andP [_ T]. 
        move: LP => /negP LP; apply: LP.
          by have ->: jlp = jhp by eapply ideal_proc_model_is_a_uniprocessor_model; eauto.
      }
      apply SCHEDc; apply/andP; split.
      - by rewrite -addn1 in LT2; apply subh3 in LT2; rewrite subn1 in LT2.
      - by apply leq_trans with t1; first apply leq_pred. 
    Qed.

    (** Thus, there must be a preemption time in the interval [t1, t1
        + max_priority_inversion t1]. That is, if a job with
        higher-or-equal priority is scheduled at time instant t1, then
        t1 is a preemption time. Otherwise, if a job with lower
        priority is scheduled at time t1, then this jobs also should
        be scheduled before the beginning of the busy interval. So,
        the next preemption time will be no more than
        [max_priority_inversion t1] time units later. *)

    (** We proceed by doing a case analysis. *)
    Section CaseAnalysis.

      (** (1) Case when the schedule is idle at time [t1]. *)
      Section Case1.

        (** Assume that the schedule is idle at time [t1]. *)
        Hypothesis H_is_idle : is_idle sched t1. 

        (** Then time instant [t1] is a preemption time. *)
        Lemma preemption_time_exists_case1: 
          exists pr_t,
            preemption_time sched pr_t /\
            t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
        Proof.
          set (service := service sched).
          move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
          move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
          exists t1; split.
          - by rewrite /preemption_time (eqbool_to_eqprop H_is_idle).
          - by apply/andP; split; last rewrite leq_addr. 
        Qed.
        
      End Case1.

      (** (2) Case when a job with higher-or-equal priority is scheduled at time [t1]. *)
      Section Case2.

        (** Assume that a job [jhp] with higher-or-equal priority is scheduled at time [t1]. *)
        Variable jhp : Job.
        Hypothesis H_jhp_is_scheduled : scheduled_at sched jhp t1. 
        Hypothesis H_jhp_hep_priority : hep_job jhp j.

        (** Then time instant [t1] is a preemption time. *)
        Lemma preemption_time_exists_case2: 
          exists pr_t,
            preemption_time sched pr_t /\
            t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
        Proof.
          set (service := service sched).
          move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
          move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
          exists t1; split; last first.
          apply/andP; split; [by done | by rewrite leq_addr].
          destruct t1.
          - eapply zero_is_pt; eauto 2. 
          - eapply hp_job_not_scheduled_before_quiet_time in QT1; eauto 2.
              by eapply first_moment_is_pt with (j0 := jhp); eauto 2.
        Qed.
          
      End Case2.

      (** (3) Case when a job with lower priority is scheduled at time [t1]. *)
      Section Case3.

        (** Assume that a job [jhp] with lower priority is scheduled at time [t1]. *)
        Variable jlp : Job.
        Hypothesis H_jlp_is_scheduled : scheduled_at sched jlp t1.
        Hypothesis H_jlp_low_priority : ~~ hep_job jlp j.

        (** To prove the lemma in this case we need a few auxiliary
            facts about the first preemption point of job [jlp]. *)
        Section FirstPreemptionPointOfjlp.

          (** Let's denote the progress of job [jlp] at time [t1] as [progr_t1]. *)
          Let progr_t1 := service sched jlp t1. 

          (** Consider the first preemption point of job [jlp] after [progr_t1]. *)
          Variable fpt : instant.
          Hypothesis H_fpt_is_preemptio_point : job_preemptable jlp (progr_t1 + fpt).
          Hypothesis H_fpt_is_first_preemption_point:
            forall ρ,
              progr_t1 <= ρ <= progr_t1 + (job_max_nonpreemptive_segment jlp - ε) -> 
              job_preemptable jlp ρ ->
              service sched jlp t1 + fpt <= ρ.

          (** For convenience we also assume the following inequality holds. *)
          Hypothesis H_progr_le_max_nonp_segment:
            progr_t1 <= progr_t1 + fpt <= progr_t1 + (job_max_nonpreemptive_segment jlp - ε).

          (** First we show that [fpt] is indeed the first preemption point after [progr_t1]. *)
          Lemma no_intermediate_preemption_point:
            forall ρ,
              progr_t1 <= ρ < progr_t1 + fpt ->
              ~~ job_preemptable jlp ρ. 
          Proof.
            move => prog /andP [GE LT].
            apply/negP; intros PPJ.
            move: H_fpt_is_first_preemption_point => K; specialize (K prog). 
            feed_n 2 K; first (apply/andP; split); try done.
            apply leq_trans with (service sched jlp t1 + fpt).
            + by apply ltnW. 
            + by move: H_progr_le_max_nonp_segment => /andP [_ LL].
                by move: K; rewrite leqNgt; move => /negP NLT; apply: NLT.
          Qed.

          (** Thanks to the fact that the scheduler respects the notion of preemption points
              we show that [jlp] is continuously scheduled in time interval <<[t1, t1 + fpt)>>. *)
          Lemma continuously_scheduled_between_preemption_points:
            forall t',
              t1 <= t' < t1 + fpt ->
              job_scheduled_at jlp t'.
          Proof.
             move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
             move: (H_jlp_is_scheduled) => ARRs; apply H_jobs_come_from_arrival_sequence in ARRs.             
            move => t' /andP [GE LT]. 
              have Fact: exists Δ, t' = t1 + Δ.
              { by exists (t' - t1); apply/eqP; rewrite eq_sym; apply/eqP; rewrite subnKC. }
              move: Fact => [Δ EQ]; subst t'.
              have NPPJ := @no_intermediate_preemption_point (@service _ _ _ sched jlp (t1 + Δ)).
              apply proj1 in CORR; specialize (CORR jlp ARRs).
              move: CORR => [_ [_ [T _] ]].
              apply T; apply: NPPJ; apply/andP; split.
              { by apply service_monotonic; rewrite leq_addr. }
              rewrite /service  -(service_during_cat _ _ _ t1).
              { rewrite ltn_add2l; rewrite ltn_add2l in LT.
                apply leq_ltn_trans with Δ; last by done.
                rewrite -{2}(sum_of_ones t1 Δ).
                rewrite leq_sum //; intros t _.
                apply service_at_most_one.
                  by apply ideal_proc_model_provides_unit_service.
              } 
              { by apply/andP; split; [done | rewrite leq_addr]. } 
          Qed.
          
          (** Thus, job [jlp] reaches its preemption point at time instant [t1 + fpt], 
              which implies that time instant [t1 + fpt] is a preemption time. *)
          Lemma first_preemption_time: 
            preemption_time sched (t1 + fpt).
          Proof.
            rewrite /preemption_time.
            move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
            ideal_proc_model_sched_case_analysis_eq sched (t1 + fpt) s'; try done.
            clear EqSched_s'; move: (Sched_s'); rewrite scheduled_at_def;
              move => /eqP EqSched_s'; rewrite EqSched_s'.
            destruct (jlp == s') eqn: EQ.
            - move: EQ => /eqP EQ; subst s'.
              rewrite /service -(service_during_cat _ _ _ t1); last first.
              { by apply/andP; split; last rewrite leq_addr. }              
              have ->: service_during sched jlp t1 (t1 + fpt) = fpt.
              { rewrite -{2}(sum_of_ones t1 fpt) /service_during.
                apply/eqP; rewrite eqn_leq //; apply/andP; split.
                + rewrite leq_sum //; intros t _.
                  apply service_at_most_one.
                    by apply ideal_proc_model_provides_unit_service.
                + rewrite big_nat_cond [in X in _ <= X]big_nat_cond.
                  rewrite leq_sum //.
                  move => x /andP [HYP _].
                    by rewrite lt0b -scheduled_at_def; apply continuously_scheduled_between_preemption_points.
              } by done.
            - case: (posnP fpt) => [ZERO|POS].
              { subst fpt.
                exfalso; move: EQ => /negP EQ; apply: EQ.
                move: H_jlp_is_scheduled; rewrite scheduled_at_def; move => /eqP SCHED2.
                rewrite addn0 in EqSched_s'; rewrite EqSched_s' in SCHED2.
                  by inversion SCHED2.
              }
              { have EX: exists sm, sm.+1 = fpt.
                { exists fpt.-1. ssromega. }
                destruct EX as [sm EQ2]. rewrite -EQ2.
                rewrite addnS.
                move: ((proj1 CORR) s' (H_jobs_come_from_arrival_sequence _ _ Sched_s')) => T.
                apply T; clear T. apply /negP; intros CONTR. 
                move: EQ => /negP EQ; apply: EQ.            
                move: (continuously_scheduled_between_preemption_points (t1 + sm)) => SCHEDs0.
                feed SCHEDs0; first by apply/andP; split; [rewrite leq_addr | rewrite -EQ2 addnS].
                apply/eqP; eapply ideal_proc_model_is_a_uniprocessor_model; eauto 2.
                  by rewrite -addnS EQ2. 
              }
          Qed.

          (** And since [fpt <= max_length_of_priority_inversion j t1], 
              [t1 <= t1 + fpt <= t1 + max_length_of_priority_inversion j t1]. *) 
          Lemma preemption_time_le_max_len_of_priority_inversion: 
            t1 <= t1 + fpt <= t1 + max_length_of_priority_inversion j t1.
          Proof.
            move: (H_jlp_is_scheduled) => ARRs; apply H_jobs_come_from_arrival_sequence in ARRs.
            move: H_progr_le_max_nonp_segment => /andP [GE LE].
            apply/andP; split; first by rewrite leq_addr.
            rewrite leq_add2l.
            unfold max_length_of_priority_inversion.
            rewrite (big_rem jlp) //=.
            { rewrite H_jlp_low_priority; simpl.
              apply leq_trans with (job_max_nonpreemptive_segment jlp - ε); last by rewrite leq_maxl.
                by rewrite leq_add2l in LE. }
            eapply arrived_between_implies_in_arrivals; eauto 2.
            apply/andP; split; first by done.
            eapply low_priority_job_arrives_before_busy_interval_prefix with t1; eauto 2.
              by move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]]; apply/andP; split.
          Qed.
          
        End FirstPreemptionPointOfjlp.

        (** Next we combine the facts above to conclude the lemma. *)
        Lemma preemption_time_exists_case3: 
          exists pr_t,
            preemption_time sched pr_t /\
            t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
        Proof.
          set (service := service sched).
          have EX: exists pt,
              ((service jlp t1) <= pt <= (service jlp t1) + (job_max_nonpreemptive_segment jlp - 1)) && job_preemptable jlp pt.
          { move: (H_jlp_is_scheduled) => ARRs; apply H_jobs_come_from_arrival_sequence in ARRs.
            move: (proj2 (H_valid_model_with_bounded_nonpreemptive_segments) jlp ARRs) =>[_ EXPP].
            specialize (EXPP (service jlp t1)).
            feed EXPP.
            { apply/andP; split; first by done.
              apply service_at_most_cost; first by done.
                by apply ideal_proc_model_provides_unit_service.
            }
            move: EXPP => [pt [NEQ PP]].
            exists pt; apply/andP; split; by done.
          }
          move: (ex_minnP EX) => [sm_pt /andP [NEQ PP] MIN]; clear EX.
          have Fact: exists Δ, sm_pt = service jlp t1 + Δ.
          { exists (sm_pt - service jlp t1).
            apply/eqP; rewrite eq_sym; apply/eqP; rewrite subnKC //.
              by move: NEQ => /andP [T _]. }
          move: Fact => [Δ EQ]; subst sm_pt; rename Δ into sm_pt.
          exists (t1 + sm_pt); split.
          - apply first_preemption_time.
            all: unfold service.service; try done.
            intros; apply MIN; apply/andP; split; by done.
          - apply preemption_time_le_max_len_of_priority_inversion.
            unfold service.service; try done.
        Qed.
        
      End Case3.
      
    End CaseAnalysis.

    (** By doing the case analysis, we show that indeed there is a
        preemption time in time interval [[t1, t1 +
        max_length_of_priority_inversion j t1]. *)
    Lemma preemption_time_exists: 
      exists pr_t,
        preemption_time sched pr_t /\
        t1 <= pr_t <= t1 + max_length_of_priority_inversion j t1.
    Proof.
      set (service := service sched).
      move: (H_valid_model_with_bounded_nonpreemptive_segments) => CORR.
      move: (H_busy_interval_prefix) => [NEM [QT1 [NQT HPJ]]].
      ideal_proc_model_sched_case_analysis sched t1 s.
      - by apply preemption_time_exists_case1.
      - destruct (hep_job s j) eqn:PRIO.
        + by eapply preemption_time_exists_case2; eauto.
        + eapply preemption_time_exists_case3 with s; eauto.
            by rewrite -eqbF_neg; apply /eqP.
    Qed.
    
  End PreemptionTimeExists.

End PriorityInversionIsBounded.
