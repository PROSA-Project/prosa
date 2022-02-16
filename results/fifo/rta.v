From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Import prosa.analysis.facts.priority.fifo. 
Require Import prosa.model.priority.fifo.
Require Import prosa.analysis.abstract.ideal_jlfp_rta.
Require Export prosa.analysis.facts.busy_interval.carry_in.

(** Throughout this file, we assume ideal uni-processor schedules ... *)
Require Import prosa.model.processor.ideal.

(** ... and the classic (i.e., Liu & Layland) model of readiness
    without jitter or self-suspensions, wherein pending jobs are
    always ready. *)
Require Import prosa.model.readiness.basic.

(** * Abstract RTA for FIFO-schedulers *)
(** In this module we instantiate the Abstract Response-Time analysis
    (aRTA) to FIFO schedulers for real-time tasks with arbitrary arrival models
     assuming an ideal uni-processor model. *)

(** Given the FIFO priority policy and an ideal uni-processor scheduler
    model, we can explicitly specify [interference],
    [interfering_workload], and [interference_bound_function]. In this
    settings, we can define natural notions of service, workload, busy
    interval, etc. *)

Section AbstractRTAforFIFOwithArrivalCurves.

  (** Consider any type of tasks, each characterized by a WCET, a relative
      deadline, and a run-to-completion threshold, ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks, where each
       each job has an arrival time, a cost, and a preemption-point predicate. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context {Arrival : JobArrival Job}.
  Context {Cost : JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** Next, consider any valid ideal uni-processor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Note that we differentiate between abstract and 
      classical notions of work-conserving schedules. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** We assume that the schedule is a work-conserving schedule 
      in the _classical_ sense, and later prove that the hypothesis 
      about abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** Assume that a job's cost cannot be larger than its task's WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : list Task.

  (** Next, we assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task [tsk] in [ts] 
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) a monotonic function 
     that equals 0 for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
      is, [task_rtct tsk] is (1) no larger than [tsk]'s cost, (2) for
      any job of task [tsk], [job_rtct] is bounded by [task_rtct]. *)
  Hypothesis H_valid_run_to_completion_threshold : valid_task_run_to_completion_threshold arr_seq tsk.

  (** We also assume that the schedule respects the policy defined by the preemption model. *)
  Hypothesis H_respects_policy_at_preemption_point : respects_policy_at_preemption_point arr_seq sched. 

  (** We introduce [rbf] as an abbreviation of the task request bound function,
      which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a given task [T]. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce [task_rbf] as an abbreviation 
      of the task request bound function of task [tsk]. *)
   Let task_rbf := rbf tsk. 

  (** For simplicity, let's define some local names. *)
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.
  Let number_of_task_arrivals := number_of_task_arrivals arr_seq.

  (** Let L be any positive fixed point of the busy interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_request_bound_function ts L.

  (** To reduce the time complexity of the analysis, we introduce the notion of search space for FIFO.
      Intuitively, this corresponds to all "interesting" arrival offsets that the job under
      analysis might have with regard to the beginning of its busy-window. *)
  
  (** In the case of FIFO, the final search space is the set of offsets less than [L] 
      such that there exists a task [tsko] from [ts] such that [rbf tsko (A) ≠ rbf tsko (A + ε)]. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && has (fun tsko => rbf tsko (A) != rbf tsko ( A + ε )) ts.

  (** Let [R] be a value that upper-bounds the solution of each
      response-time equation, i.e., for any relative arrival time [A]
      in the search space, there exists a corresponding solution [F]
      such that [R >= F]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum: 
    forall (A : duration),
      is_in_search_space A -> 
      exists (F : nat),
        A + F >= \sum_(tsko <- ts) rbf tsko (A + ε) /\
        F <= R.

  (** To use the theorem [uniprocessor_response_time_bound] from the Abstract RTA module, 
      we need to specify functions that concretely define the abstract concepts
      interference, interfering workload, and [IBF]. *)
  
  (** ** Instantiation of Interference *)
  (** We say that job [j] incurs interference at time [t] iff it cannot execute due to 
     a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. *)
  Let interference (j : Job) (t : instant) := ideal_jlfp_rta.interference sched j t.

  (** ** Instantiation of Interfering Workload *)
  (** The interfering workload, in turn, is defined as the sum of the priority inversion 
      function and interfering workload of jobs with higher or equal priority. *)
  Let interfering_workload (j : Job) (t : instant) := ideal_jlfp_rta.interfering_workload arr_seq sched j t.

  (** Finally, we define the interference bound function ([IBF]). [IBF] bounds the cumulative 
      interference incurred by a job. For FIFO, we define [IBF] as the sum of [RBF] for all tasks 
      in the interval [A + ε] minus the WCET of [tsk]. *)
  Let IBF tsk (A R : duration) := (\sum_(tsko <- ts) rbf tsko (A + ε)) - task_cost tsk.

  (** ** Filling Out Hypotheses Of Abstract RTA Theorem *)
  (** In this section we prove that all hypotheses necessary to use the abstract theorem are satisfied. *)
  Section FillingOutHypothesesOfAbstractRTATheorem.

    (** First, we prove that, in the instantiation of interference and interfering workload, 
        we really take into account everything that can interfere with [tsk]'s jobs, and thus, 
        the scheduler satisfies the abstract notion of a work conserving schedule. *)
    Lemma instantiated_i_and_w_are_coherent_with_schedule:
      work_conserving_ab tsk interference interfering_workload.
    Proof.
      intros j t1 t2 t ARR TSK POS BUSY NEQ.
      split; [move=>/negP |rewrite scheduled_at_def => /eqP HYP].
      { rewrite negb_or /is_priority_inversion /is_priority_inversion
                /is_interference_from_another_hep_job => /andP [HYP1 HYP2].
        ideal_proc_model_sched_case_analysis_eq sched t jo.
        { exfalso; clear HYP1 HYP2.
          destruct H_valid_schedule as [A B].
          eapply instantiated_busy_interval_equivalent_busy_interval in BUSY; try by eauto 2 with basic_facts.
          move: BUSY => [PREF _].
          by eapply not_quiet_implies_not_idle; eauto 2 with basic_facts. }
        { clear EqSched_jo; move: Sched_jo; rewrite scheduled_at_def; move => /eqP EqSched_jo.
          rewrite EqSched_jo in HYP1, HYP2. 
          move: HYP1 HYP2.
          rewrite Bool.negb_involutive negb_and.
          move => HYP1 /orP [/negP HYP2| /eqP HYP2] //.
          rewrite Bool.negb_involutive in HYP2.
          move: HYP2 => /eqP /eqP HYP2.
          by subst jo; rewrite scheduled_at_def EqSched_jo. } }
      { apply/negP;
        rewrite /interference /ideal_jlfp_rta.interference /is_priority_inversion
                /is_interference_from_another_hep_job HYP negb_or.
        apply/andP; split.
        - by rewrite Bool.negb_involutive /hep_job /fifo.FIFO.
        - by rewrite negb_and Bool.negb_involutive; apply/orP; right. }
    Qed.

    (** Recall that L is assumed to be a fixed point of the busy interval recurrence. Thanks to
        this fact, we can prove that every busy interval (according to the concrete definition) 
        is bounded. In addition, we know that the conventional concept of busy interval and the 
        one obtained from the abstract definition (with the interference and interfering 
        workload) coincide. Thus, it follows that any busy interval (in the abstract sense) 
        is bounded. *)
    Lemma instantiated_busy_intervals_are_bounded:
      busy_intervals_are_bounded_by arr_seq sched tsk interference interfering_workload L.
    Proof.
      intros j ARR TSK POS.
      destruct H_valid_schedule as [COME MUST ].
      edestruct exists_busy_interval_from_total_workload_bound
        with (Δ := L) as [t1 [t2 [T1 [T2 GGG]]]]; eauto 2 with basic_facts.
      { by intros; rewrite {2}H_fixed_point; apply total_workload_le_total_rbf. }
      { exists t1, t2; split; first by done.
        split; first by done.
        by eapply instantiated_busy_interval_equivalent_busy_interval; eauto 2 with basic_facts. }
    Qed.
    
    (** In this section, we prove that, under FIFO scheduling, the cumulative priority inversion experienced
        by a job [j] in any interval within its busy window is always [0]. We later use this fact to prove the bound on 
        the cumulative interference. *)
    Section PriorityInversion.

      (** Consider any job [j] of the task under consideration [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_task j = tsk.

      (** Assume that the job has a positive cost. *)
      Hypothesis H_job_cost_positive: job_cost_positive j.

      (** Assume the busy interval of the job is given by <<[t1,t2)>>. *)
      Variable t1 t2 : duration.
      Hypothesis H_busy_interval :
        definitions.busy_interval sched interference interfering_workload j t1 t2.

      (** Consider any interval <<[t1,t1 + Δ)>> in the busy interval of [j]. *)
      Variable Δ : duration.
      Hypothesis H_Δ_in_busy : t1 + Δ < t2.

      (** We prove that the cumulative priority inversion in the interval <<[t1, t1 + Δ)>> is [0]. *)
      Lemma cumulative_priority_inversion_is_bounded:
        cumulative_priority_inversion sched j t1 (t1 + Δ) = 0.
      Proof.
        apply big_nat_eq0 => t /andP [T1 T2].
        apply /eqP; rewrite eqb0; apply /negP.
        move: (ideal_proc_model_sched_case_analysis sched t) => [/eqP IDLE|[s INTER]];
                                                                 first by rewrite  /is_priority_inversion IDLE.
        destruct (leqP (job_arrival j) t).
        { destruct (completed_by sched j t) eqn : COMPL; last first.
          { apply /negP.
            eapply (FIFO_implies_no_priority_inversion arr_seq); eauto with basic_facts.
            by apply /andP; split; [| rewrite COMPL]. }
          { rewrite scheduled_at_def in INTER.
            rewrite /is_priority_inversion. 
            move: INTER => /eqP INTER; rewrite INTER.
            apply /negP; rewrite Bool.negb_involutive /hep_job /FIFO.
            move_neq_up CONTR.
             have QTIme' : quiet_time arr_seq sched j t.
            { move => j_hp ARRjhp HEP ARRbef.
              eapply (scheduled_implies_higher_priority_completed arr_seq _ _ _ _ s); try by done.
              - by move : INTER => /eqP INTER; rewrite -scheduled_at_def in INTER.
              - by rewrite -ltnNge; apply leq_ltn_trans with (job_arrival j). } 
            apply instantiated_busy_interval_equivalent_busy_interval in H_busy_interval;
              eauto 2 with basic_facts;last by done.
            move : H_busy_interval => [ [_ [_ [QUIET /andP [ARR _ ]]]] _].
            destruct (leqP t t1) as [LE | LT].
            { have EQ : t = job_arrival j by apply eq_trans with t1; ssrlia.
              rewrite EQ in COMPL; apply completed_on_arrival_implies_zero_cost in COMPL; eauto with basic_facts.
              by move: (H_job_cost_positive); rewrite /job_cost_positive COMPL. }
            { specialize (QUIET t); feed QUIET.
              - apply /andP; split; first by done.
                by apply leq_trans with (t1 +  Δ) ; [| apply ltnW].
              - by contradict QUIET. }
            by destruct H_valid_schedule as [COME MUST]. } }
        { destruct H_valid_schedule as [READY MUST].
          have HAS : has_arrived s t by eapply (jobs_must_arrive_to_be_ready  sched).
          rewrite scheduled_at_def in INTER.
          unfold is_priority_inversion.
          move: INTER => /eqP ->.
          apply /negP; rewrite Bool.negb_involutive.
          by apply leq_trans with t; [apply HAS | apply ltnW]. }
        Unshelve.
        all: try by done.
      Qed.
      
    End PriorityInversion.

    (** Using the above lemma, we prove that IBF is indeed an interference bound. *)
    Lemma instantiated_interference_is_bounded :
      job_interference_is_bounded_by arr_seq sched tsk interference interfering_workload  IBF.
    Proof.
      move => t1 t2 Δ j ARRj TSKj BUSY IN_BUSY NCOMPL.
      move: H_valid_schedule => [READY MUST ].
      rewrite /cumul_interference cumulative_interference_split.
      have JPOS: job_cost_positive j by rewrite -ltnNge in NCOMPL; unfold job_cost_positive; ssrlia.
      move: (BUSY) => [ [ /andP [LE GT] [QUIETt1 _ ] ] [QUIETt2 EQNs]].
      erewrite (cumulative_priority_inversion_is_bounded j ARRj JPOS t1 t2); rewrite //= add0n.
      rewrite (instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs arr_seq) //=; 
              try by (try rewrite instantiated_quiet_time_equivalent_quiet_time); eauto 2 with basic_facts.
      eapply leq_trans; first by apply service_of_jobs_le_workload; eauto 2 with basic_facts.
      rewrite (leqRW (workload_equal_subset _ _ _ _ _ _  _)); eauto 2 with basic_facts.
      specialize (workload_minus_job_cost j) => ->.
      { rewrite /workload_of_jobs /IBF (big_rem tsk) //= (addnC (rbf tsk (job_arrival j - t1 + ε))).
        rewrite -addnBA; last first.
        { apply leq_trans with (task_rbf ε).
          apply (task_rbf_1_ge_task_cost arr_seq) with (j0 := j) => //=; first by auto.
          by apply task_rbf_monotone; [apply H_valid_arrival_curve | ssrlia]. }
        { eapply leq_trans; last first.
          by erewrite leq_add2l; eapply task_rbf_excl_tsk_bounds_task_workload_excl_j; eauto 1.
          rewrite addnBA.
          { rewrite leq_sub2r //; eapply leq_trans.
            - apply sum_over_partitions_le => j' inJOBS.
              by apply H_all_jobs_from_taskset, (in_arrivals_implies_arrived _ _ _ _ inJOBS). 
            - rewrite (big_rem tsk) //= addnC leq_add //; last by rewrite subnKC.
              rewrite big_seq_cond [in X in _ <= X]big_seq_cond big_mkcond [in X in _ <= X]big_mkcond //=. 
              apply leq_sum => tsk' _; rewrite andbC //=.
              destruct (tsk' \in rem (T:=Task) tsk ts) eqn:IN; last by done.
              apply rem_in in IN.
              eapply leq_trans; last first.
              + by apply (task_workload_le_task_rbf _ _ _ IN H_valid_job_cost H_is_arrival_curve t1).
              + by rewrite addnBAC //= subnKC //= addn1; apply leqW. } 
          { rewrite /task_workload_between /task_workload /workload_of_jobs (big_rem j) //=.
            - by rewrite TSKj; apply leq_addr.
            - apply job_in_arrivals_between => //.
              by apply /andP; split; [| rewrite subnKC; [rewrite addn1 |]].  } } }
      apply: arrivals_uniq => //.
      apply: job_in_arrivals_between => //.
      by apply /andP; split; [ | rewrite addn1]. 
    Qed.

    (** Finally, we show that there exists a solution for the response-time equation. *)
    Section SolutionOfResponseTimeReccurenceExists.

      (** Consider any job j of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      Hypothesis H_positive_cost : 0 < task_cost tsk.
      
      (** Next, consider any [A] from the search space (in the abstract sense). *)
      Variable A : nat.
      Hypothesis H_A_is_in_abstract_search_space:
        search_space.is_in_search_space tsk L IBF A.

      (** We prove that [A] is also in the concrete search space. In other words, 
          we prove that the abstract search space is a subset of the concrete search space. *)
      Lemma A_is_in_concrete_search_space:
        is_in_search_space A.
      Proof.
        move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
        unfold is_in_search_space.
        { subst A. 
          apply/andP; split; [by done |].
          apply /hasP. exists tsk; first by done.
          rewrite neq_ltn;apply/orP; left.
          rewrite /task_rbf /rbf; erewrite task_rbf_0_zero; eauto 2.
          rewrite add0n /task_rbf; apply leq_trans with (task_cost tsk).
          - by eapply leq_trans; eauto 2.
          - by eapply task_rbf_1_ge_task_cost; eauto. }
        { apply /andP; split; first by done.
          apply /hasPn.
          move => EQ2. unfold IBF in INSP2.
          rewrite subnK in INSP2; try by done.
          apply INSP2; clear INSP2.
          have -> : \sum_(tsko <- ts) rbf tsko A = \sum_(tsko <- ts) rbf tsko (A + ε); last by done.
          apply eq_big_seq => //= task IN.
          by move: (EQ2 task IN) => /negPn /eqP. }
      Qed.

      
      (** Then, there exists a solution for the response-time recurrence (in the abstract sense). *)
      Corollary exists_solution_for_abstract_response_time_recurrence:
        exists (F : nat),
          A + F >= task_rtct tsk + IBF tsk A (A + F) /\
          F + (task_cost tsk - task_rtct tsk) <= R.
      Proof.
        move : H_R_is_maximum => ABC.
        move: (H_valid_arrival_curve _ H_tsk_in_ts) => VARR.
        move: (H_is_arrival_curve _ H_tsk_in_ts) => RESP.
        move : H_job_of_tsk => /eqP EQj. 
        specialize (ABC 0); feed ABC.
        { apply /andP; split;  [by done| apply /hasP; exists tsk; first by done].
          rewrite /task_rbf /rbf task_rbf_0_zero //= (add0n ε) neq_ltn.
          apply /orP; left.
          by apply (task_rbf_epsilon_gt_0 arr_seq H_arrival_times_are_consistent tsk RESP  j). }
        move : ABC => [F [LE1 LE2]].
        edestruct H_R_is_maximum as [F' [FIX NEQ]]; first by apply A_is_in_concrete_search_space.
        exists (R - (task_cost tsk - task_rtct tsk)); split.
        { unfold IBF.
          rewrite (leqRW FIX) addnC -subnA; first last.
          - rewrite -(leqRW FIX).
            apply (task_cost_le_sum_rbf _ H_arrival_times_are_consistent _ VARR RESP j) => //.
            by rewrite addn1.
          - destruct H_valid_run_to_completion_threshold as [TASKvalid JOBvalid].
            by apply TASKvalid. 
          - rewrite addnBA; first by rewrite leq_sub2r // leq_add2l.
            have GE: task_cost tsk <= R; last by ssrlia.
            rewrite !add0n in LE1.
            rewrite -(leqRW LE2) -(leqRW LE1).
            by eapply (task_cost_le_sum_rbf arr_seq); eauto with basic_facts. }
        { rewrite subnK; first by done.
          rewrite !add0n in LE1. apply leq_trans with F; last by done.
          apply leq_trans with (\sum_(tsko <- ts) rbf tsko ε); last by done.
          apply leq_trans with (task_cost tsk); first by ssrlia.
          eapply task_cost_le_sum_rbf; eauto with basic_facts. }
      Qed.
      
    End SolutionOfResponseTimeReccurenceExists.

  End FillingOutHypothesesOfAbstractRTATheorem.

  (** ** Final Theorem *)
  (** Based on the properties established above, we apply the abstract analysis 
      framework to infer that [R] is a response-time bound for [tsk]. *)
  Theorem uniprocessor_response_time_bound_FIFO:
    response_time_bounded_by tsk R.
  Proof.
    intros js ARRs TSKs.
    move: (posnP (@job_cost _ Cost js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }    
    eapply uniprocessor_response_time_bound with
      (interference0 := interference) (interfering_workload0 := interfering_workload)
      (interference_bound_function := fun tsk A R => IBF tsk A R) (L0 := L); eauto 2 with basic_facts.
    - by apply instantiated_i_and_w_are_coherent_with_schedule.
    - by apply instantiated_busy_intervals_are_bounded.
    - by apply instantiated_interference_is_bounded.
    - eapply (exists_solution_for_abstract_response_time_recurrence js) => //=.
      apply leq_trans with (job_cost js) => //.
      move: TSKs; rewrite /job_of_task => /eqP <-.
      by eapply H_valid_job_cost.
  Qed.
  
End AbstractRTAforFIFOwithArrivalCurves. 



