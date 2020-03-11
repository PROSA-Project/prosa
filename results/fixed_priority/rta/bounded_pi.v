Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.facts.busy_interval.busy_interval.
Require Import prosa.analysis.abstract.ideal_jlfp_rta.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.readiness.basic.

(** * Abstract RTA for FP-schedulers with Bounded Priority Inversion *)
(** In this module we instantiate the Abstract Response-Time analysis
    (aRTA) to FP-schedulers for ideal uni-processor model of
    real-time tasks with arbitrary arrival models. *)

(** Given FP priority policy and an ideal uni-processor scheduler
    model, we can explicitly specify [interference],
    [interfering_workload], and [interference_bound_function]. In this
    settings, we can define natural notions of service, workload, busy
    interval, etc. The important feature of this instantiation is that
    we can induce the meaningful notion of priority
    inversion. However, we do not specify the exact cause of priority
    inversion (as there may be different reasons for this, like
    execution of a non-preemptive segment or blocking due to resource
    locking). We only assume that that a priority inversion is
    bounded. *)
Section AbstractRTAforFPwithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.
  
  (** Next, consider any ideal uniprocessor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Note that we differentiate between abstract and 
     classical notions of work conserving schedule. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.
  
  (** We assume that the schedule is a work-conserving schedule 
     in the _classical_ sense, and later prove that the hypothesis 
     about abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** Assume we have sequential tasks, i.e, jobs from the 
     same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks sched.

  (** Assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.
  
  (** Consider an arbitrary task set ts. *)    
  Variable ts : list Task.

  (** Next, we assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.
 
  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task [tsk] in ts 
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) it is a monotonic function 
     that equals 0 for the empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.
    
  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That is, 
     [task_run_to_completion_threshold tsk] is (1) no bigger than [tsk]'s 
     cost, (2) for any job of task [tsk] job_run_to_completion_threshold 
     is bounded by task_run_to_completion_threshold. *)
  Hypothesis H_valid_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.
  
  (** Consider an FP policy that indicates a higher-or-equal priority relation,
     and assume that the relation is reflexive. Note that we do not relate 
     the FP policy with the scheduler. However, we define functions for 
     Interference and Interfering Workload that actively use the concept of 
     priorities. We require the FP policy to be reflexive, so a job cannot 
     cause lower-priority interference (i.e. priority inversion) to itself. *)
  Context `{FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.
  
  (** For clarity, let's define some local names. *)
  Let job_pending_at := pending sched.
  Let job_scheduled_at := scheduled_at sched.
  Let job_completed_by := completed_by sched.
  Let job_backlogged_at := backlogged sched.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.

  (** We introduce [task_rbf] as an abbreviation of the task request bound function,
     which is defined as [task_cost(tsk) × max_arrivals(tsk,Δ)]. *)
  Let task_rbf := task_request_bound_function tsk.

  (** Using the sum of individual request bound functions, we define the request bound 
     function of all tasks with higher-or-equal priority (with respect to [tsk]). *)
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.
 
  (** Similarly, we define the request bound function of all tasks other 
     than [tsk] with higher-or-equal priority (with respect to [tsk]). *)
  Let total_ohep_rbf :=
    total_ohep_request_bound_function_FP ts tsk.
  
  (** Assume that there exists a constant priority_inversion_bound that bounds 
     the length of any priority inversion experienced by any job of [tsk]. 
     Since we analyze only task [tsk], we ignore the lengths of priority 
     inversions incurred by any other tasks. *)
  Variable priority_inversion_bound : duration.
  Hypothesis H_priority_inversion_is_bounded:
    priority_inversion_is_bounded_by
      arr_seq sched tsk priority_inversion_bound.

  (** Let L be any positive fixed point of the busy interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = priority_inversion_bound + total_hep_rbf L.

  (** To reduce the time complexity of the analysis, recall the notion of search space.
     Intuitively, this corresponds to all "interesting" arrival offsets that the job under
     analysis might have with regard to the beginning of its busy-window. *)
  Definition is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).

  (** Let R be a value that upper-bounds the solution of each response-time recurrence, 
     i.e., for any relative arrival time A in the search space, there exists a corresponding 
     solution F such that [F + (task cost - task lock-in service) <= R]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum : 
    forall (A : duration),
      is_in_search_space A -> 
      exists (F : duration),
        A + F = priority_inversion_bound
                + (task_rbf (A + ε) - (task_cost tsk - task_run_to_completion_threshold tsk))
                + total_ohep_rbf (A + F) /\
        F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.

  (** Instantiation of Interference *)
  (** We say that job j incurs interference at time t iff it cannot execute due to 
     a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. *)
  Let interference (j : Job) (t : instant) :=
    ideal_jlfp_rta.interference sched j t.

  (** Instantiation of Interfering Workload *)
  (** The interfering workload, in turn, is defined as the sum of the
      priority inversion function and interfering workload of jobs
      with higher or equal priority. *)
  Let interfering_workload (j : Job) (t : instant) :=
    ideal_jlfp_rta.interfering_workload arr_seq sched j t.
  
  (** Finally, we define the interference bound function as the sum of the priority 
      interference bound and the higher-or-equal-priority workload. *)
  Let IBF (R : duration) := priority_inversion_bound + total_ohep_rbf R.

  (** ** Filling Out Hypotheses Of Abstract RTA Theorem *)
  (** In this section we prove that all preconditions necessary to use the abstract theorem are satisfied. *)
  Section FillingOutHypothesesOfAbstractRTATheorem.

    (** First, we prove that in the instantiation of interference and interfering workload, 
       we really take into account everything that can interfere with [tsk]'s jobs, and thus, 
       the scheduler satisfies the abstract notion of work conserving schedule. *) 
    Lemma instantiated_i_and_w_are_consistent_with_schedule:
      work_conserving_ab tsk interference interfering_workload.
    Proof.
      intros j t1 t2 t ARR TSK POS BUSY NEQ; split; intros HYP.
      - move: HYP => /negP.
        rewrite negb_or /is_priority_inversion /is_priority_inversion
                /is_interference_from_another_hep_job.
        move => /andP [HYP1 HYP2].
        case SCHED: (sched t) => [s | ].
        + rewrite SCHED in HYP1, HYP2.
          move: HYP1 HYP2. 
          rewrite !Bool.negb_involutive negb_and Bool.negb_involutive.
          move => HYP1 /orP [/negP HYP2| /eqP HYP2].
          * by exfalso.
          * by subst s; rewrite scheduled_at_def //; apply eqprop_to_eqbool.
        + exfalso; clear HYP1 HYP2.
          eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; eauto with basic_facts.
            by move: BUSY => [PREF _]; eapply not_quiet_implies_not_idle;
                              eauto 2 using eqprop_to_eqbool.
      - move: (HYP); rewrite scheduled_at_def; move => /eqP HYP2; apply/negP.
        rewrite /interference /ideal_jlfp_rta.interference /is_priority_inversion
                  /is_interference_from_another_hep_job HYP2 negb_or.
         apply/andP; split.
         + rewrite Bool.negb_involutive; eauto 2.
             by eapply H_priority_is_reflexive with (t := 0).
         + by rewrite negb_and Bool.negb_involutive; apply/orP; right.
    Qed.

    (** Next, we prove that the interference and interfering workload 
       functions are consistent with sequential tasks. *)
    Lemma instantiated_interference_and_workload_consistent_with_sequential_tasks: 
      interference_and_workload_consistent_with_sequential_tasks
        arr_seq sched tsk interference interfering_workload.
    Proof.
      intros j t1 t2 ARR TSK POS BUSY. 
      eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; eauto with basic_facts.
      eapply all_jobs_have_completed_equiv_workload_eq_service; eauto 2; intros s ARRs TSKs.
      move: (BUSY) => [[_ [QT _]] _].
      apply QT.
      - by apply in_arrivals_implies_arrived in ARRs.
      - move: TSKs => /eqP TSKs.
        rewrite /hep_job /FP_to_JLFP TSK -TSKs; eauto 2.
          by eapply (H_priority_is_reflexive 0); eauto.
      - by eapply in_arrivals_implies_arrived_before; eauto 2.
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
      edestruct (exists_busy_interval) with (delta := L) as [t1 [t2 [T1 [T2 GGG]]]]; eauto 2.
      { by intros; rewrite {2}H_fixed_point leq_add //; apply total_workload_le_total_rbf'. }
      exists t1, t2; split; first by done.
      split.
      - by done.
      - by eapply instantiated_busy_interval_equivalent_edf_busy_interval; eauto 2 with basic_facts.
    Qed.

    (** Next, we prove that IBF is indeed an interference bound.

       Recall that in module abstract_seq_RTA hypothesis task_interference_is_bounded_by expects 
       to receive a function that maps some task t, the relative arrival time of a job j of task t, 
       and the length of the interval to the maximum amount of interference (for more details see 
       files limited.abstract_RTA.definitions and limited.abstract_RTA.abstract_seq_rta).

       However, in this module we analyze only one task -- [tsk], therefore it is “hard-coded” 
       inside the interference bound function IBF. Moreover, in case of a model with fixed 
       priorities, interference that some job j incurs from higher-or-equal priority jobs does not
       depend on the relative arrival time of job j. Therefore, in order for the IBF signature to
       match the required signature in module abstract_seq_RTA, we wrap the IBF function in a 
       function that accepts, but simply ignores, the task and the relative arrival time. *)
    Lemma instantiated_task_interference_is_bounded:
      task_interference_is_bounded_by
        arr_seq sched tsk interference interfering_workload (fun t A R => IBF R).
    Proof.
      intros ? ? ? ? ARR TSK ? NCOMPL BUSY; simpl.
      move: (posnP (@job_cost _ H3 j)) => [ZERO|POS].
      { by exfalso; rewrite /completed_by ZERO in  NCOMPL. }
      eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; eauto 2 with basic_facts.
      rewrite /interference; erewrite cumulative_task_interference_split; eauto 2 with basic_facts; last first.
      { move: BUSY => [[_ [_ [_ /andP [GE LT]]]] _].
          by eapply arrived_between_implies_in_arrivals; eauto 2. }
      unfold IBF, interference.
      rewrite leq_add; try done. 
      { move: (H_priority_inversion_is_bounded j ARR TSK) => BOUND.
        apply leq_trans with (cumulative_priority_inversion sched j t1 (t1 + R0)); first by done.
        apply leq_trans with (cumulative_priority_inversion sched j t1 t2); last first.
        { by apply BOUND; move: BUSY => [PREF QT2]. }
        rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + R0)) //=.
        - by rewrite leq_addr.
        - by rewrite leq_addr.
        - by rewrite ltnW.
      }
      { erewrite instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks;
          eauto 2; last by unfold quiet_time; move: BUSY => [[_ [T1 T2]] _]. 
        apply leq_trans with
            (workload_of_jobs
               (fun jhp : Job => (FP_to_JLFP _ _) jhp j && (job_task jhp != job_task j))
               (arrivals_between arr_seq t1 (t1 + R0))
            ).
        { by apply service_of_jobs_le_workload; last apply ideal_proc_model_provides_unit_service.  }
        { rewrite  /workload_of_jobs /total_ohep_rbf /total_ohep_request_bound_function_FP.
            by rewrite -TSK; apply total_workload_le_total_rbf.
        }
      }
    Qed.

    (** Finally, we show that there exists a solution for the response-time recurrence. *)
    Section SolutionOfResponseTimeRecurrenceExists.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_task j = tsk.
      Hypothesis H_job_cost_positive: job_cost_positive j.

      (** Given any job j of task [tsk] that arrives exactly A units after the beginning of 
         the busy interval, the bound of the total interference incurred by j within an 
         interval of length Δ is equal to [task_rbf (A + ε) - task_cost tsk + IBF Δ]. *)
      Let total_interference_bound tsk A Δ :=
        task_rbf (A + ε) - task_cost tsk + IBF Δ.

      (** Next, consider any A from the search space (in the abstract sense). *)
      Variable A : duration.
      Hypothesis H_A_is_in_abstract_search_space :
        search_space.is_in_search_space tsk L total_interference_bound A. 
      
      (** We prove that A is also in the concrete search space. *)
      Lemma A_is_in_concrete_search_space:
        is_in_search_space A.
      Proof.
        move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
        - rewrite INSP.
          apply/andP; split; first by done.
          rewrite neq_ltn; apply/orP; left.
          rewrite {1}/task_rbf; erewrite task_rbf_0_zero; eauto 2; try done.
          rewrite add0n /task_rbf; apply leq_trans with (task_cost tsk).
          + by apply leq_trans with (job_cost j); rewrite -?H_job_of_tsk; eauto 2.
          + eapply task_rbf_1_ge_task_cost; eauto 2.
        - apply/andP; split; first by done.
          apply/negP; intros EQ; move: EQ => /eqP EQ.
          apply INSP2.
          unfold total_interference_bound in *.
          rewrite subn1 addn1 prednK; last by done.              
            by rewrite -EQ.
      Qed.

      (** Then, there exists a solution for the response-time recurrence (in the abstract sense). *)
      Corollary correct_search_space:
        exists (F : duration),
          A + F = task_rbf (A + ε) - (task_cost tsk - task_run_to_completion_threshold tsk) + IBF (A + F) /\
          F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.
      Proof.
        move: (H_R_is_maximum A) => FIX.
        feed FIX; first by apply A_is_in_concrete_search_space. 
        move: FIX => [F [FIX NEQ]].
        exists F; split; last by done.
        apply/eqP; rewrite {1}FIX.
          by rewrite addnA [_ + priority_inversion_bound]addnC -!addnA.
      Qed.

    End SolutionOfResponseTimeRecurrenceExists.

  End FillingOutHypothesesOfAbstractRTATheorem.

  (** ** Final Theorem *)
  (** Based on the properties established above, we apply the abstract analysis 
     framework to infer that [R] is a response-time bound for [tsk]. *) 
  Theorem uniprocessor_response_time_bound_fp:
    response_time_bounded_by tsk R.
  Proof.
    intros js ARRs TSKs.
    move: (posnP (@job_cost _ H3 js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }
    eapply uniprocessor_response_time_bound_seq; eauto 3.
    - by apply instantiated_i_and_w_are_consistent_with_schedule. 
    - by apply instantiated_interference_and_workload_consistent_with_sequential_tasks. 
    - by apply instantiated_busy_intervals_are_bounded.
    - by apply instantiated_task_interference_is_bounded.
    - by eapply correct_search_space; eauto 2. 
  Qed.
    
End AbstractRTAforFPwithArrivalCurves.
