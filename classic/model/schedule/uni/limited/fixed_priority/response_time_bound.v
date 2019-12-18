Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority. 
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.response_time
               prosa.classic.model.schedule.uni.schedule_of_task.
Require Import prosa.classic.model.schedule.uni.limited.platform.definitions
               prosa.classic.model.schedule.uni.limited.schedule
               prosa.classic.model.schedule.uni.limited.rbf
               prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions
               prosa.classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space
               prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta
               prosa.classic.model.schedule.uni.limited.jlfp_instantiation.
Require Import prosa.classic.model.arrival.curves.bounds.
Require Import prosa.classic.analysis.uni.arrival_curves.workload_bound.
Require Import prosa.classic.model.schedule.uni.limited.busy_interval.
 
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Abstract RTA for FP-schedulers *)
(** In this module we propose the abstract response-time analysis (RTA) for  
    FP uniprocessor scheduling of real-time tasks with arbitrary arrival models.  *)
Module AbstractRTAforFPwithArrivalCurves.
   
  Import Job ArrivalCurves TaskArrival Priority ScheduleOfTask
         UniprocessorSchedule Workload Service ResponseTime MaxArrivalsWorkloadBound
         LimitedPreemptionPlatform RBF BusyIntervalJLFP JLFPInstantiation.
  
  Section AbstractResponseTimeAnalysisForFP.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.    
     
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time. 
    Variable job_task: Job -> Task.
  
    (* Consider any arrival sequence with consistent, non-duplicate arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
        
    (* Next, assume that the schedule is a work-conserving schedule. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

    (* Assume we have sequential jobs, i.e, jobs from the 
       same task execute in the order of their arrival. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.

    (* Assume that a job cost cannot be larger than a task cost. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq.
 
    (* Consider an arbitrary task set ts. *)    
    Variable ts: list Task.

    (* Next, we assume that all jobs come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

   (* Let max_arrivals be a family of proper arrival curves, i.e., for any task tsk in ts 
      [max_arrival tsk] is (1) an arrival bound of tsk, and (2) it is a monotonic function 
      that equals 0 for the empty interval delta = 0. *)
    Variable max_arrivals: Task -> time -> nat.
    Hypothesis H_family_of_proper_arrival_curves:
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts.
        
    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.
    
    (* Consider proper job lock-in service and task lock-in functions, i.e... *)
    Variable job_lock_in_service: Job -> time.
    Variable task_lock_in_service: Task -> time.

    (* ...we assume that for all jobs with positive cost in the arrival sequence the 
       lock-in service is (1) positive, (2) no bigger than costs of the corresponding
       jobs, and (3) a job becomes nonpreemptive after it reaches its lock-in service... *)
    Hypothesis H_proper_job_lock_in_service:
      proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service.

    (* ...and that [task_lock_in_service tsk] is (1) no bigger than tsk's cost, (2) for any
       job of task tsk job_lock_in_service is bounded by task_lock_in_service. *)
    Hypothesis H_proper_task_lock_in_service:
      proper_task_lock_in_service
        task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk.

    (* Consider an FP policy that indicates a higher-or-equal priority relation,
       and assume that the relation is reflexive. Note that we do not relate 
       the FP policy with the scheduler. However, we define functions for 
       Interference and Interfering Workload that actively use the concept of 
       priorities. We require the FP policy to be reflexive, so a job cannot 
       cause lower-priority interference (i.e. priority inversion) to itself. *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.

    (* We also lift the FP priority relation to a corresponding JLFP priority relation. *)
     Let jlfp_higher_eq_priority j1 j2 := FP_to_JLFP job_task higher_eq_priority j1 j2. 
     
    (* For clarity, let's define some local names. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_backlogged_at := backlogged job_arrival job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    Let response_time_bounded_by := is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.    
    Let quiet_time := quiet_time job_arrival job_cost arr_seq sched jlfp_higher_eq_priority.
    Let busy_interval :=  busy_interval job_arrival job_cost arr_seq sched jlfp_higher_eq_priority.
    Let task_scheduled_at :=  task_scheduled_at job_task sched.
    Let cumulative_task_interference :=
      AbstractSeqRTA.cumul_task_interference job_task arr_seq sched.

    (* We introduce task_rbf as an abbreviation of the task request bound function,
       which is defined as [task_cost(tsk) × max_arrivals(tsk,Δ)]. *)
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.

    (* Using the sum of individual request bound functions, we define the request bound 
       function of all tasks with higher-or-equal priority (with respect to tsk). *)
    Let total_hep_rbf :=
      total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.

    (* Similarly, we define the request bound function of all tasks other 
       than tsk with higher-or-equal priority (with respect to tsk). *)
    Let total_ohep_rbf :=
      total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.
    
    (* Assume that there eixsts a constant priority_inversion_bound that bounds 
       the length of any priority inversion experienced by any job of tsk. 
       Sinse we analyze only task tsk, we ignore the lengths of priority 
       inversions incurred by any other tasks. *)
    Variable priority_inversion_bound: time.
    Hypothesis H_priority_inversion_is_bounded:
      priority_inversion_is_bounded_by
        job_arrival job_cost job_task arr_seq sched jlfp_higher_eq_priority tsk priority_inversion_bound.

    (* Let L be any positive fixed point of the busy interval recurrence. *)
    Variable L: time.
    Hypothesis H_L_positive: L > 0.
    Hypothesis H_fixed_point: L = priority_inversion_bound + total_hep_rbf L.

    (* To reduce the time complexity of the analysis, recall the notion of search space.
       Intuitively, this corresponds to all "interesting" arrival offsets that the job under
       analysis might have with regard to the beginning of its busy-window. *)
    Let is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).

    (* Let R be a value that upper-bounds the solution of each response-time recurrence, 
       i.e., for any relative arrival time A in the search space, there exists a corresponding 
       solution F such that [F + (task cost - task lock-in service) <= R]. *)
    Variable R: time.
    Hypothesis H_R_is_maximum: 
      forall A,
        is_in_search_space A -> 
        exists F,
          A + F = priority_inversion_bound
                  + (task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk))
                  + total_ohep_rbf (A + F) /\
          F + (task_cost tsk - task_lock_in_service tsk) <= R.

    
    (* Instantiation of Interference *)
    (* We say that job j incurs interference at time t iff it cannot execute due to 
       a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. 
       (for more details see file limited.jlfp_instantiation.v) *)
    Let interference (j: Job) (t: time) :=
      interference sched jlfp_higher_eq_priority j t.

    (* Instantiation of Interfering Workload *)
    (* The interfering workload, in turn, is defined as the sum of the priority inversion 
       function and interfering workload of jobs with higher or equal priority.
       (for more details see file limited.limited.jlfp_instantiation.v) *)
    Let interfering_workload (j: Job) (t: time) :=
      interfering_workload job_cost arr_seq sched jlfp_higher_eq_priority j t.

    (* Finally, we define the interference bound function as the sum of the priority 
       interference bound and the higher-or-equal-priority workload. *)
    Let IBF R := priority_inversion_bound + total_ohep_rbf R.

    (** ** Filling Out Hypotheses Of Abstract RTA Theorem *)
    (** In this section we prove that all preconditions necessary to use the abstract theorem are satisfied. *)
    Section FillingOutHypothesesOfAbstractRTATheorem.

      (* First, we prove that in the instantiation of interference and interfering workload, 
         we really take into account everything that can interfere with tsk's jobs, and thus, 
         the scheduler satisfies the abstract notion of work conserving schedule. *) 
      Lemma instantiated_i_and_w_are_consistent_with_schedule:
        AbstractRTADefinitions.work_conserving
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload.
      Proof.
        intros j t1 t2 t ARR TSK POS BUSY NEQ; split; intros HYP. 
        unfold AbstractRTADefinitions.busy_interval, AbstractRTADefinitions.busy_interval_prefix in *.
        { move: HYP => /negP.
          rewrite negb_or /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion
                  /is_interference_from_another_job_with_higher_eq_priority.
          move => /andP [HYP1 HYP2].
          case SCHED: (sched t) => [s | ].
          { rewrite SCHED in HYP1, HYP2.
            move: HYP1 HYP2. 
            rewrite !Bool.negb_involutive negb_and Bool.negb_involutive.
            move => HYP1 /orP [/negP HYP2| /eqP HYP2].
            - by exfalso.
            - by subst s; rewrite /scheduled_at SCHED.
          }
          { exfalso; clear HYP1 HYP2. 
            eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; try done; first last.
            { by intros x; apply H_priority_is_reflexive. }
            { by apply job_task. } 
            have EQ:= not_quiet_implies_not_idle
                        job_arrival job_cost arr_seq _
                        sched jlfp_higher_eq_priority j _ _ _ _ _ t1 t2 _ t.
            feed_n 8 EQ; try done.
            - by rewrite /jlfp_higher_eq_priority /JLFP_is_reflexive /FP_to_JLFP.
            - by move: BUSY => [PREF _].
            - by apply EQ; apply/eqP.
          }
        } 
        { move: HYP => /eqP HYP.
          apply/negP.
          rewrite /interference /JLFPInstantiation.interference /is_priority_inversion
                  /BusyIntervalJLFP.is_priority_inversion
                  /jlfp_higher_eq_priority /is_interference_from_another_job_with_higher_eq_priority HYP negb_or.
          apply/andP; split.
          - by rewrite Bool.negb_involutive /FP_to_JLFP.
          - by rewrite negb_and Bool.negb_involutive; apply/orP; right.
        }
      Qed.

      (* Next, we prove that the interference and interfering workload 
         functions are consistent with sequential jobs. *)
      Lemma instantiated_interference_and_workload_consistent_with_sequential_jobs: 
        AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload.
      Proof.
        intros j t1 t2 ARR TSK POS BUSY. 
        eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; first last; try by done.
        { by intros x; apply H_priority_is_reflexive. }
        { by apply job_task. }
        eapply all_jobs_have_completed_equiv_workload_eq_service; eauto 2; intros s ARRs TSKs.
        move: (BUSY) => [[_ [QT _]] _].
        apply QT.
        - by apply in_arrivals_implies_arrived in ARRs.
        - move: TSKs => /eqP TSKs.
            by rewrite /jlfp_higher_eq_priority /FP_to_JLFP TSK TSKs.
        - by eapply in_arrivals_implies_arrived_before; eauto 2.
      Qed. 

      (* Recall that L is assumed to be a fixed point of the busy interval recurrence. Thanks to
         this fact, we can prove that every busy interval (according to the concrete definition) 
         is bounded. In addition, we know that the conventional concept of busy interval and the 
         one obtained from the abstract definition (with the interference and interfering 
         workload) coincide. Thus, it follows that any busy interval (in the abstract sense) 
         is bounded. *)
      Lemma instantiated_busy_intervals_are_bounded:
        AbstractRTADefinitions.busy_intervals_are_bounded_by
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L.
      Proof.
        intros j ARR TSK POS.
        have EX := exists_busy_interval
                     job_arrival job_cost arr_seq _ sched _
                     jlfp_higher_eq_priority j _ _ _ _ _ _ priority_inversion_bound _ L.
        feed_n 12 EX; try eauto 2.
        { by rewrite /JLFP_is_reflexive /jlfp_higher_eq_priority /FP_to_JLFP. } 
        { intros. 
          rewrite {2}H_fixed_point leq_add //.  
          apply total_workload_le_total_rbf'; try done.
            by intros tsko INo;  move: (H_family_of_proper_arrival_curves tsko INo) => [ARRB _].
        } 
        move: EX => [t1 [t2 [H1 [H2 GGG]]]].
        exists t1, t2; split; first by done.
        split; first by done.
        eapply instantiated_busy_interval_equivalent_edf_busy_interval; eauto 2.
          by intros x; apply H_priority_is_reflexive.
      Qed.

      (* Next, we prove that IBF is indeed an interference bound.

         Recall that in module abstract_seq_RTA hypothesis task_interference_is_bounded_by expects 
         to receive a function that maps some task t, the relative arrival time of a job j of task t, 
         and the length of the interval to the maximum amount of interference (for more details see 
         files limited.abstract_RTA.definitions and limited.abstract_RTA.abstract_seq_rta).

         However, in this module we analyze only one task -- tsk, therefore it is “hardcoded” 
         inside the interference bound function IBF. Moreover, in case of a model with fixed 
         priorities, interference that some job j incurs from higher-or-equal priority jobs does not
         depend on the relative arrival time of job j. Therefore, in order for the IBF signature to
         match the required signature in module abstract_seq_RTA, we wrap the IBF function in a 
         function that accepts, but simply ignores, the task and the relative arrival time. *)
      Lemma instantiated_task_interference_is_bounded:
        AbstractSeqRTA.task_interference_is_bounded_by
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload
          (fun t A R => IBF R).
      Proof. 
        intros ? ? ? ? ARR TSK ? NCOMPL BUSY.
        move: (posnP (job_cost j)) => [ZERO|POS].
        { exfalso.
          move: NCOMPL => /negP COMPL; apply: COMPL.
            by rewrite /is_response_time_bound_of_job /completed_by ZERO.
        }    
        eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; first last; try done.
        { by intros x; apply H_priority_is_reflexive. }
        { by apply job_task. } 
        have T123 := cumulative_task_interference_split.
        rewrite /cumulative_task_interference in T123.
        rewrite (T123 _ _ job_arrival job_cost _ _ _ _ _ _ _ j); eauto 2; last first.
        { move: BUSY => [[_ [_ [_ /andP [GE LT]]]] _].
            by eapply arrived_between_implies_in_arrivals; eauto 2. }
        { by apply any_reflexive_FP_respects_sequential_jobs. } 
        unfold IBF, interference.
        rewrite leq_add; try done. 
        { unfold is_priority_inversion, FP_to_JLFP.
          unfold priority_inversion_is_bounded_by in *.
          move: (H_priority_inversion_is_bounded j ARR TSK) => BOUND.
          apply leq_trans with (cumulative_priority_inversion sched jlfp_higher_eq_priority j t1 (t1 + R0)).
          { by done. }
          { apply leq_trans with (cumulative_priority_inversion sched jlfp_higher_eq_priority j t1 t2).
            { rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + R0)) //=.
              - by rewrite leq_addr.
              - by rewrite leq_addr.
              - by rewrite ltnW.
            }
            { by apply BOUND; move: BUSY => [PREF QT2]. }
          }
        }
        { intros.
          rewrite
            (instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks
               job_arrival job_cost _ arr_seq); last first; try done.
          { by unfold quiet_time; move: BUSY => [[_ [H1 H2]] _]. }
          apply leq_trans with
              (workload_of_jobs
                 job_cost (arrivals_between t1 (t1 + R0))
                 (fun jhp : Job => jlfp_higher_eq_priority jhp j && (job_task jhp != job_task j))).
          { by apply service_of_jobs_le_workload. }
          { rewrite  /workload_of_jobs
                    /total_ohep_rbf /total_ohep_request_bound_function_FP.
            rewrite -TSK; apply total_workload_le_total_rbf; try done.
              by intros tsko INo;  move: (H_family_of_proper_arrival_curves tsko INo) => [ARRB _].
          }
        }
      Qed.

      (* Finally, we show that there exists a solution for the response-time recurrence. *)
      Section SolutionOfResponseTimeReccurenceExists.

        (* Consider any job j of tsk. *)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_tsk: job_task j = tsk.
        Hypothesis H_job_cost_positive: job_cost_positive job_cost j.

        (* Given any job j of task tsk that arrives exactly A units after the beginning of 
           the busy interval, the bound of the total interference incurred by j within an 
           interval of length Δ is equal to [task_rbf (A + ε) - task_cost tsk + IBF Δ]. *)
        Let total_interference_bound tsk A Δ :=
          task_rbf (A + ε) - task_cost tsk + IBF Δ.

        (* Next, consider any A from the search space (in the abstract sence). *)
        Variable A: time.
        Hypothesis H_A_is_in_abstract_search_space:
          AbstractRTAReduction.is_in_search_space tsk L total_interference_bound A.

        (* We prove that A is also in the concrete search space. *)
        Lemma A_is_in_concrete_search_space:
          is_in_search_space A.
        Proof.
          unfold total_interference_bound in *.
          move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
          - rewrite INSP.
            apply/andP; split; first by done.
            rewrite neq_ltn; apply/orP; left.
            rewrite {1}/task_rbf; erewrite rbf.RBF.task_rbf_0_zero; eauto 2; try done.
            rewrite add0n /task_rbf.  
            apply leq_trans with (task_cost tsk).
            + by apply leq_trans with (job_cost j); rewrite -?H_job_of_tsk; eauto 2.
            + by eapply rbf.RBF.task_rbf_1_ge_task_cost; eauto 2.
          - apply/andP; split; first by done.
            apply/negP; intros EQ; move: EQ => /eqP EQ.
            apply INSP2.
            rewrite subn1 addn1 prednK; last by done.              
              by rewrite -EQ.
        Qed.

        (* Then, there exists a solution for the response-time recurrence (in the abstract sense). *)
        Corollary correct_search_space:
          exists F,
            A + F = task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk) + IBF (A + F) /\
            F + (task_cost tsk - task_lock_in_service tsk) <= R.
        Proof.
          move: (H_R_is_maximum A) => FIX.
          feed FIX; first by apply A_is_in_concrete_search_space. 
          move: FIX => [F [FIX NEQ]].
          exists F; split; last by done.
          apply/eqP; rewrite {1}FIX.
            by rewrite addnA [_ + priority_inversion_bound]addnC -!addnA.
        Qed.

      End SolutionOfResponseTimeReccurenceExists.

    End FillingOutHypothesesOfAbstractRTATheorem.

    (** ** Final Theorem *)
    (* Based on the properties established above, we apply the abstract analysis 
       framework to infer that R is a response-time bound for tsk. *) 
    Theorem uniprocessor_response_time_bound_fp:
      response_time_bounded_by tsk R.
    Proof.
      intros js ARRs TSKs.
      move: (posnP (job_cost js)) => [ZERO|POS].
      { by rewrite /is_response_time_bound_of_job /completed_by ZERO. }
      move: H_proper_job_lock_in_service => [T1 [T2 T3]].
      move: H_proper_task_lock_in_service => [T4 T5]. 
      eapply AbstractSeqRTA.uniprocessor_response_time_bound_seq with
          (interference0 := interference) (interfering_workload0 := interfering_workload)
          (task_interference_bound_function := fun _ A R => IBF R) (L0 := L) (ts0 := ts); eauto 3.
      - by apply instantiated_i_and_w_are_consistent_with_schedule. 
      - by apply instantiated_interference_and_workload_consistent_with_sequential_jobs. 
      - by apply instantiated_busy_intervals_are_bounded.
      - by apply instantiated_task_interference_is_bounded.
      - by eapply correct_search_space; eauto 2. 
    Qed.
    
  End AbstractResponseTimeAnalysisForFP.  
         
End AbstractRTAforFPwithArrivalCurves.