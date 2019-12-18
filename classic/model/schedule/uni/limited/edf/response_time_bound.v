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
               prosa.classic.model.schedule.uni.limited.busy_interval
               prosa.classic.model.schedule.uni.limited.rbf
               prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions
               prosa.classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space
               prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta
               prosa.classic.model.schedule.uni.limited.jlfp_instantiation.
Require Import prosa.classic.model.arrival.curves.bounds. 
Require Import prosa.classic.analysis.uni.arrival_curves.workload_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Abstract RTA for EDF-schedulers *)
(** In this module we propose the abstract response-time analysis (RTA) for 
    EDF uniprocessor scheduling of real-time tasks with arbitrary arrival models.  *)
Module AbstractRTAforEDFwithArrivalCurves.
  
  Import Job ArrivalCurves TaskArrival ScheduleOfTask Priority
         UniprocessorSchedule Workload Service ResponseTime MaxArrivalsWorkloadBound
         BusyIntervalJLFP LimitedPreemptionPlatform RBF Service JLFPInstantiation.
 
  Section AbstractResponseTimeAnalysisForEDF.
     
    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_deadline: Task -> time.
    
    Context {Job: eqType}. 
    Variable job_arrival: Job -> time. 
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* For clarity, let's denote the relative deadline of a task as D. *)
    Let D tsk := task_deadline tsk.

    (* The relative deadline of a job is equal to the deadline of the corresponding task. *)
    Let job_relative_deadline j := D (job_task j).
    
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

    (* Consider the EDF policy that indicates a higher-or-equal priority relation.
       Note that we do not relate the EDF policy with the scheduler. However, we 
       define functions for Interference and Interfering Workload that actively use
       the concept of priorities. *)
    Let EDF: JLFP_policy Job := EDF job_arrival job_relative_deadline.

    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_backlogged_at := backlogged job_arrival job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    Let task_scheduled_at :=  task_scheduled_at job_task sched.
    Let quiet_time := quiet_time job_arrival job_cost arr_seq sched EDF.
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    Let cumulative_task_interference :=
      AbstractSeqRTA.cumul_task_interference job_task arr_seq sched.

    (* We introduce "rbf" as an abbreviation of the task request bound function,
       which is defined as [task_cost(T) × max_arrivals(T,Δ)] for some task T. *)
    Let rbf := task_request_bound_function task_cost max_arrivals.
    
    (* Next, we introduce task_rbf as an abbreviation 
       of the task request bound function of task tsk. *)
    Let task_rbf := rbf tsk.

    (* Using the sum of individual request bound functions, we define the request bound 
       function of all tasks (total request bound function). *)
    Let total_rbf := total_request_bound_function task_cost max_arrivals ts.

    (* Assume that there exists a constant priority_inversion_bound that bounds 
       the length of any priority inversion experienced by any job of tsk. 
       Sinse we analyze only task tsk, we ignore the lengths of priority 
       inversions incurred by any other tasks. *)
    Variable priority_inversion_bound: time.
    Hypothesis H_priority_inversion_is_bounded:
      priority_inversion_is_bounded_by
        job_arrival job_cost job_task arr_seq sched EDF tsk priority_inversion_bound.

    (* Let L be any positive fixed point of the busy interval recurrence. *)
    Variable L: time.
    Hypothesis H_L_positive: L > 0.
    Hypothesis H_fixed_point: L = total_rbf L.

    (* Next, we define an upper bound on interfering workload received from jobs 
       of other tasks with higher-than-or-equal priority. *)
    Let bound_on_total_hep_workload A Δ :=
      \sum_(tsk_o <- ts | tsk_o != tsk)
       rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

    (* To reduce the time complexity of the analysis, we introduce the notion of search space for EDF.
       Intuitively, this corresponds to all "interesting" arrival offsets that the job under
       analysis might have with regard to the beginning of its busy-window. *) 

    (* In case of search space for EDF we ask whether [task_rbf A ≠ task_rbf (A + ε)]... *)
    Definition task_rbf_changes_at A := task_rbf A != task_rbf (A + ε).

    (* ...or there exists a task tsko from ts such that [tsko ≠ tsk] and 
       [rbf(tsko, A + D tsk - D tsko) ≠ rbf(tsko, A + ε + D tsk - D tsko)].
       Note that we use a slightly uncommon notation [has (λ tsko ⇒ P tsko) ts] 
       which can be interpreted as follows: task-set ts contains a task tsko such 
       that a predicate P holds for tsko. *)
    Definition bound_on_total_hep_workload_changes_at A :=
       has (fun tsko =>
           (tsk != tsko)
             && (rbf tsko (A +     D tsk - D tsko    )
                     != rbf tsko ((A + ε) + D tsk - D tsko))) ts.
  
    (* The final search space for EDF is a set of offsets that are less than L 
       and where task_rbf or bound_on_total_hep_workload chages. *)
    Let is_in_search_space A :=
      (A < L) && (task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A).
    
    (* Let R be a value that upper-bounds the solution of each response-time recurrence, 
       i.e., for any relative arrival time A in the search space, there exists a corresponding 
       solution F such that [F + (task cost - task lock-in service) <= R]. *)
    Variable R: nat.
    Hypothesis H_R_is_maximum: 
      forall A,
        is_in_search_space A -> 
        exists F,
          A + F = priority_inversion_bound
                  + (task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk))
                  + bound_on_total_hep_workload  A (A + F) /\
          F + (task_cost tsk - task_lock_in_service tsk) <= R.

    
    (* To use the theorem uniprocessor_response_time_bound_seq from the Abstract RTA module, 
       we need to specify functions of interference, interfering workload and IBF.  *)

    (* Instantiation of Interference *)
    (* We say that job j incurs interference at time t iff it cannot execute due to 
       a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. 
       (for more details see file limited.limited.jlfp_instantiation.v) *)
    Let interference (j: Job) (t: time) :=
      interference sched EDF j t.

    (* Instantiation of Interfering Workload *)
    (* The interfering workload, in turn, is defined as the sum of the priority inversion 
       function and interfering workload of jobs with higher or equal priority. 
       (for more details see file limited.limited.jlfp_instantiation.v) *)
    Let interfering_workload (j: Job) (t: time) := interfering_workload job_cost arr_seq sched EDF j t.

    (* Finally, we define the interference bound function as the sum of the priority 
       interference bound and the higher-or-equal-priority workload. *)
    Let IBF A R := priority_inversion_bound + bound_on_total_hep_workload A R.

    (** ** Filling Out Hypothesis Of Abstract RTA Theorem *)
    (** In this section we prove that all hypotheses necessary to use the abstract theorem are satisfied. *)
    Section FillingOutHypothesesOfAbstractRTATheorem.

      (* First, we prove that in the instantiation of interference and interfering workload, 
         we really take into account everything that can interfere with tsk's jobs, and thus, 
         the scheduler satisfies the abstract notion of work conserving schedule. *)
      Lemma instantiated_i_and_w_are_coherent_with_schedule:
        AbstractRTADefinitions.work_conserving
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload.
      Proof.
        intros j t1 t2 t ARR TSK POS BUSY NEQ; split; intros HYP.
        { move: HYP => /negP.
          rewrite negb_or /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion
                  /is_interference_from_another_job_with_higher_eq_priority.
          move => /andP [HYP1 HYP2].
          case SCHED: (sched t) => [s | ].
          { rewrite SCHED in HYP1, HYP2. 
            move: HYP1 HYP2.
            rewrite Bool.negb_involutive negb_and.
            move => HYP1 /orP [/negP HYP2| /eqP HYP2].
            - by exfalso.
            - rewrite Bool.negb_involutive in HYP2.
              move: HYP2 => /eqP /eqP HYP2.
                by subst s; rewrite /scheduled_at SCHED.
          }
          { exfalso; clear HYP1 HYP2.
            eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; try done; first last.
            { by rewrite /JLFP_is_reflexive /reflexive /EDF /Priority.EDF. }
            { by apply job_task. } 
            have EQ:= not_quiet_implies_not_idle
                        job_arrival job_cost arr_seq
                        _ sched EDF j _ _ _ _ _ t1 t2 _ t.
            feed_n 8 EQ; try done.
            { by rewrite /JLFP_is_reflexive /reflexive /EDF /Priority.EDF. }
            { by move: BUSY => [PREF _]. }            
              by eapply EQ; apply/eqP.
          }
        }
        { move: HYP => /eqP HYP.
          apply/negP; rewrite /interference /JLFPInstantiation.interference /is_priority_inversion
                              /BusyIntervalJLFP.is_priority_inversion
                              /is_interference_from_another_job_with_higher_eq_priority
                              HYP negb_or; apply/andP; split.
          - by rewrite Bool.negb_involutive /EDF /Priority.EDF.
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
        eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; try done; first last.
        { by rewrite /JLFP_is_reflexive /reflexive /EDF /Priority.EDF. }
        { by apply job_task. }
        eapply all_jobs_have_completed_equiv_workload_eq_service; eauto 2.
        intros s INs TSKs.
        rewrite /arrivals_between in INs.
        move: (INs) => NEQ.
        eapply in_arrivals_implies_arrived_between in NEQ; eauto 2.
        move: NEQ => /andP [_ JAs].
        move: (BUSY) => [[ _ [QT [_ /andP [JAj _]]] _]].
        apply QT; try done.
        - eapply in_arrivals_implies_arrived; eauto 2.
        - unfold EDF, Priority.EDF.
          move: TSKs => /eqP TSKs.
          rewrite /job_relative_deadline TSK TSKs leq_add2r.
            by apply leq_trans with t1; [apply ltnW | ].
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
        have EX := exists_busy_interval_from_total_workload_bound
                     job_arrival job_cost arr_seq _ sched _
                     EDF _ _ _ _ _ L _ _ j ARR POS. 
        feed_n 9 EX; try eauto 2.
        { by unfold JLFP_is_reflexive, reflexive, EDF, Priority.EDF. }
        { intros. 
          rewrite {2}H_fixed_point.
          apply total_workload_le_total_rbf'' with job_task; try done.
            by intros tsk0 IN0;  move: (H_family_of_proper_arrival_curves tsk0 IN0) => [ARRB _].
        } 
        move: EX => [t1 [t2 [H1 [H2 GGG]]]].
        exists t1, t2; split; first by done.
        split; first by done.
        eapply instantiated_busy_interval_equivalent_edf_busy_interval; eauto 2.
          by unfold JLFP_is_reflexive, reflexive, EDF, Priority.EDF. 
      Qed.

      (* Next, we prove that IBF is indeed an interference bound.

         Recall that in module abstract_seq_RTA hypothesis task_interference_is_bounded_by expects 
         to receive a function that maps some task t, the relative arrival time of a job j of task t, 
         and the length of the interval to the maximum amount of interference (for more details see 
         files limited.abstract_RTA.definitions and limited.abstract_RTA.abstract_seq_rta).

         However, in this module we analyze only one task -- tsk, therefore it is “hardcoded” 
         inside the interference bound function IBF. Therefore, in order for the IBF signature to
         match the required signature in module abstract_seq_RTA, we wrap the IBF function in a 
         function that accepts, but simply ignores the task. *)
      Lemma instantiated_task_interference_is_bounded:
        AbstractSeqRTA.task_interference_is_bounded_by
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload
          (fun tsk A R => IBF A R).
      Proof. 
        clear H_R_is_maximum R.  
        intros j R t1 t2 ARR TSK N NCOMPL BUSY.
        move: (posnP (job_cost j)) => [ZERO|POS].
        { exfalso.
          move: NCOMPL => /negP COMPL; apply: COMPL.
            by rewrite /is_response_time_bound_of_job /completed_by ZERO.
        }
        move: (BUSY) => [[/andP [JINBI JINBI2] [QT _]] _]. 
        set (A := job_arrival j - t1) in *.
        have L2 := JLFPInstantiation.cumulative_task_interference_split
                     job_arrival job_cost job_task arr_seq sched _ EDF _ tsk
                     j.
        rewrite L2; first last; try done.
        { by eapply arrived_between_implies_in_arrivals; eauto. }
        { by unfold EDF, job_relative_deadline; eapply EDF_respects_sequential_jobs; eauto. }
        rewrite /I leq_add //.  
        { unfold priority_inversion_is_bounded_by in *.
          apply leq_trans with (cumulative_priority_inversion sched EDF j t1 t2).
          { rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1  + R)) //=.
            - by rewrite leq_addr.
            - by rewrite /is_priority_inversion leq_addr.
            - by rewrite ltnW.
          }
          { apply H_priority_inversion_is_bounded; try done.
            eapply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; try done.
            { by move: BUSY => [PREF _]. }
            { by apply job_task. }
            { by rewrite /JLFP_is_reflexive /reflexive /EDF /Priority.EDF. }
          }
        }
        { rewrite
            (instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks
               job_arrival job_cost _ arr_seq
            ); try done; first last.
          rewrite instantiated_quiet_time_equivalent_edf_quiet_time //.
          { by apply job_task. }
          { by rewrite /JLFP_is_reflexive /reflexive /EDF /Priority.EDF. }
          apply leq_trans with
              (workload_of_jobs job_cost (arrivals_between t1 (t1 + R))
                                (fun jhp : Job => EDF jhp j && (job_task jhp != job_task j))).
          { apply service_of_jobs_le_workload; try done. }
          { rewrite /bound_on_total_hep_workload /rbf /total_ohep_request_bound_function_FP
                    /task_request_bound_function
                    /workload_of_jobs /arrivals_between.
            set l := jobs_arrived_between arr_seq t1 (t1 + R). 
            apply leq_trans with
                (\sum_(tsk_o <- ts | tsk_o != tsk)
                  (\sum_(j0 <- l | EDF j0 j && (job_task j0 == tsk_o)) job_cost j0)).
            { intros.
              have EXCHANGE := exchange_big_dep (fun j0 => EDF j0 j && (job_task j0 != job_task j)).
              rewrite EXCHANGE /=; last first.
              { move => tsko jo /negP NEQ /andP [EQ1 /eqP EQ2].
                rewrite EQ1 Bool.andb_true_l; apply/negP; intros CONTR.
                apply: NEQ; clear EQ1.
                  by rewrite -TSK -EQ2.
              }
              rewrite /workload_of_jobs /l big_seq_cond [X in _ <= X]big_seq_cond.
              apply leq_sum; move => jo /andP [ARRo /andP [HEQ TSKo]].
              rewrite (big_rem (job_task jo)) //=.
              rewrite HEQ eq_refl -TSK TSKo andTb andTb leq_addr //.
              eapply H_all_jobs_from_taskset, in_arrivals_implies_arrived; eauto 2.
            }                        
            apply leq_sum_seq; intros tsko INtsko NEQT.
            case NEQ: (R <= job_arrival j - t1 + ε + task_deadline tsk - task_deadline tsko). 
            { move: (NEQ) => /minn_idPl => MIN.
              rewrite minnC in MIN; rewrite MIN; clear MIN. 
              apply leq_trans with (task_cost tsko * num_arrivals_of_task job_task arr_seq tsko t1 (t1 + R)).
              { apply leq_trans with (\sum_(j0 <- l | job_task j0 == tsko) job_cost j0).
                { rewrite big_mkcond [X in _ <= X]big_mkcond //= leq_sum //.
                    by intros s _; case (job_task s == tsko); case (EDF s j). }
                { rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
                  rewrite -/l /workload_of_jobs.
                  rewrite /is_job_of_task  muln1.
                  apply leq_sum_seq; move => j0 IN0 /eqP EQ.
                  rewrite -EQ.
                  apply H_job_cost_le_task_cost.
                    by apply in_arrivals_implies_arrived in IN0.
                }
              }
              { rewrite leq_mul2l; apply/orP; right.
                rewrite -{2}[R](addKn t1).
                move: (H_family_of_proper_arrival_curves tsko INtsko) => [ARRB _].
                  by apply ARRB; rewrite leq_addr.
              }
            }
            { apply negbT in NEQ; rewrite -ltnNge in NEQ; apply ltnW in NEQ.
              move: (NEQ) => /minn_idPr => MIN.
              rewrite minnC in MIN; rewrite MIN; clear MIN.
              set (V := job_arrival j - t1 + ε + task_deadline tsk - task_deadline tsko) in *.              
              apply leq_trans with (task_cost tsko * num_arrivals_of_task job_task arr_seq tsko t1 (t1 + V)).
              { unfold l.                
                apply leq_trans with
                    (\sum_(jo <- jobs_arrived_between arr_seq t1 (t1 + V) | EDF jo j && (job_task jo == tsko))
                      job_cost jo).
                { rewrite (job_arrived_between_cat _ _ (t1 + V)); [ |rewrite leq_addr //|rewrite leq_add2l //].
                  rewrite big_cat //=. 
                  rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
                  rewrite big_seq_cond.
                  apply/eqP; apply big_pred0.
                  intros jo; apply/negP; intros CONTR.
                  move: CONTR => /andP [ARRIN /andP [HEP /eqP TSKo]].
                  unfold EDF, Priority.EDF  in HEP.
                  eapply in_arrivals_implies_arrived_between in ARRIN; eauto 2.
                  move: ARRIN => /andP [ARRIN _]; unfold V in ARRIN.
                  have EQ1: job_relative_deadline jo = task_deadline tsko;
                    first by rewrite /job_relative_deadline TSKo.
                  rewrite EQ1 in HEP; clear EQ1.
                  have EQ2: job_relative_deadline j = task_deadline tsk;
                    first by rewrite /job_relative_deadline TSK.
                  rewrite EQ2 in HEP; clear EQ2. 
                  case NEQ2: (task_deadline tsko <= job_arrival j - t1 + ε + task_deadline tsk).
                  { move: ARRIN; rewrite leqNgt; move => /negP ARRIN; apply: ARRIN.
                    rewrite -(ltn_add2r (task_deadline tsko)).
                    apply leq_ltn_trans with (job_arrival j + task_deadline tsk); first by done.
                    rewrite addnBA; last by done.
                    rewrite addnA addnA. 
                    rewrite subnKC; last by done.
                    rewrite subnK.
                    - by rewrite ltn_add2r addn1.
                    - apply leq_trans with (job_arrival j - t1 + ε + task_deadline tsk); first by done.
                        by rewrite !leq_add2r leq_subr. 
                  } 
                  { apply negbT in NEQ2; rewrite -ltnNge in NEQ2.
                    move: HEP; rewrite leqNgt; move => /negP HEP; apply: HEP.                      
                    apply leq_ltn_trans with (job_arrival jo + (job_arrival j - t1 + task_deadline tsk)).
                    { rewrite subh1; last by done.
                      rewrite addnBA; last apply leq_trans with (job_arrival j); [ | by done | by rewrite leq_addr].
                      rewrite [in X in _ <= X]addnC.
                      rewrite -addnBA; first by rewrite leq_addr.
                        by apply leq_trans with (t1 + (job_arrival j - t1 + ε + task_deadline tsk - task_deadline tsko)); first rewrite leq_addr.
                    } 
                    { rewrite ltn_add2l.
                      apply leq_ltn_trans with (job_arrival j - t1 + ε + task_deadline tsk); last by done.
                        by rewrite leq_add2r leq_addr.
                    }
                  }
                }
                {
                  intros. 
                  apply leq_trans with
                      (\sum_(jo <- jobs_arrived_between arr_seq t1 (t1 + V) | job_task jo == tsko) job_cost jo).
                  { rewrite big_mkcond [X in _ <= X]big_mkcond //=.
                    rewrite leq_sum //; intros s _.
                      by case (EDF s j).
                  }
                  { rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
                    rewrite /is_job_of_task  muln1.
                    apply leq_sum_seq; move => j0 IN0 /eqP EQ.
                    rewrite -EQ.
                    apply H_job_cost_le_task_cost.
                      by apply in_arrivals_implies_arrived in IN0.
                  }                  
                }                
              }
              { rewrite leq_mul2l; apply/orP; right.
                rewrite -{2}[V](addKn t1).
                move: (H_family_of_proper_arrival_curves tsko INtsko) => [ARRB _].
                  by apply ARRB; rewrite leq_addr.
              }                    
            }
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
           interval of length Δ is equal to [task_rbf (A + ε) - task_cost tsk + IBF(A, Δ)]. *)
        Let total_interference_bound tsk A Δ :=
          task_rbf (A + ε) - task_cost tsk + IBF A Δ.
        
        (* Next, consider any A from the search space (in abstract sence). *)
        Variable A: time.
        Hypothesis H_A_is_in_abstract_search_space:
          AbstractRTAReduction.is_in_search_space tsk L total_interference_bound A.

        (* We prove that A is also in the concrete search space. *)
        Lemma A_is_in_concrete_search_space:
          is_in_search_space A.
        Proof.
          unfold total_interference_bound in *.
          unfold AbstractRTAReduction.is_in_search_space in H_A_is_in_abstract_search_space.
          unfold is_in_search_space in H_R_is_maximum. 
          move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
          { subst A.
            apply/andP; split; first by done.
            apply/orP; left.
            unfold task_rbf_changes_at. rewrite neq_ltn; apply/orP; left.
            rewrite /task_rbf /rbf. erewrite rbf.RBF.task_rbf_0_zero; eauto 2.
            rewrite add0n /task_rbf.
            apply leq_trans with (task_cost tsk).
            + apply leq_trans with (job_cost j); try eauto 2. 
                by rewrite -H_job_of_tsk; apply H_job_cost_le_task_cost. 
            + by eapply rbf.RBF.task_rbf_1_ge_task_cost; eauto 2.                    
          }
          { apply/andP; split; first by done.
            apply/negPn/negP; intros EQ; move: EQ => /eqP EQ.
            apply INSP2.
            move: EQ; rewrite negb_or eqb_id Bool.negb_involutive; move => /andP [/eqP EQ1 /hasPn EQ2].
            unfold task_rbf, rbf in EQ1.                  
            rewrite subn1 addn1 prednK; last by done.
            rewrite /task_rbf /rbf -EQ1.
            apply/eqP; rewrite eqn_add2l eqn_add2l.
            unfold bound_on_total_hep_workload .
            have Abs:
              forall (T: eqType) (xs: seq T) f1 f2 (P: _ -> bool),
                (forall x, x \in xs -> P x -> f1 x == f2 x) ->
                \sum_(x <- xs | P x) f1 x == \sum_(x <- xs | P x) f2 x.
            { clear.
              intros.
              rewrite big_seq_cond [X in _ == X]big_seq_cond.
              rewrite big_mkcond [X in _ == X]big_mkcond //=.
              rewrite eqn_leq; apply/andP; split; rewrite leq_sum //; intros i _.
              - case IN: (i \in xs); last by done.
                case Pi: (P i); simpl; last by done.
                apply H in IN; last by done.
                  by move: IN => /eqP IN; rewrite IN.
              - case IN: (i \in xs); last by done.
                case Pi: (P i); simpl; last by done.
                apply H in IN; last by done.
                  by move: IN => /eqP IN; rewrite IN.              
            }
            apply: Abs; intros tsk_o IN NEQ.
            rewrite addn1 prednK; last by done.
            move: (EQ2 tsk_o IN); clear EQ2.
            rewrite eq_sym NEQ Bool.andb_true_l Bool.negb_involutive; move => /eqP EQ2.
            case CASE: (A + ε + task_deadline tsk - task_deadline tsk_o <= x).
            { have F1: minn (A + task_deadline tsk - task_deadline tsk_o) x =
                       A + task_deadline tsk - task_deadline tsk_o.
              { rewrite minnE.
                have CASE2: A + task_deadline tsk - task_deadline tsk_o <= x.
                {  apply leq_trans with (A + ε + task_deadline tsk - task_deadline tsk_o).
                   - by apply leq_sub2r; rewrite leq_add2r leq_addr.
                   - by done.
                } 
                move: CASE2; rewrite -subn_eq0; move => /eqP CASE2; rewrite CASE2.
                  by rewrite subn0.
              } 
              have F2: minn (A + ε + task_deadline tsk - task_deadline tsk_o) x =
                       A + ε + task_deadline tsk - task_deadline tsk_o.
              { rewrite minnE.
                move: CASE; rewrite -subn_eq0; move => /eqP CASE; rewrite CASE.
                  by rewrite subn0.                
              }
                by apply/eqP; rewrite F1 F2.
            }
            { move: CASE => /negP /negP; rewrite -ltnNge; move => CASE.
              have F1: minn (A + task_deadline tsk - task_deadline tsk_o) x = x.
              { rewrite minnE; rewrite subKn //.
                rewrite -(leq_add2r 1) !addn1.
                rewrite -subSn.
                { rewrite -[in X in _ <= X]addn1.
                    by rewrite -addnA [_ + 1]addnC addnA.
                }
                { intros.
                  have POS := @leq_ltn_trans _ 0 _ _ CASE.
                  feed POS; first by done.
                    by rewrite subn_gt0 -addnA [1 + _]addnC addnA addn1 ltnS in POS.
                } 
              }
              have F2: minn (A + ε + task_deadline tsk - task_deadline tsk_o) x = x.
              { by rewrite minnE; rewrite subKn // ltnW. }
                by apply/eqP; rewrite F1 F2.
            }
          }
        Qed.

        (* Then, there exists solution for response-time recurrence (in the abstract sense). *)
        Corollary correct_search_space:
          exists F,
            A + F = task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk) + IBF A (A + F) /\
            F + (task_cost tsk - task_lock_in_service tsk) <= R.
        Proof.
          unfold total_interference_bound in *.
          unfold AbstractRTAReduction.is_in_search_space in H_A_is_in_abstract_search_space.
          unfold is_in_search_space in H_R_is_maximum.
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
    Theorem uniprocessor_response_time_bound_edf:
      response_time_bounded_by tsk R.
    Proof.
      intros js ARRs TSKs.
      move: (posnP (job_cost js)) => [ZERO|POS].
      { by rewrite /is_response_time_bound_of_job /completed_by ZERO. }    
      eapply AbstractSeqRTA.uniprocessor_response_time_bound_seq with
          (interference0 := interference) (interfering_workload0 := interfering_workload)
          (task_interference_bound_function := fun tsk A R => IBF A R) (L0 := L); eauto 3.
      - by apply instantiated_i_and_w_are_coherent_with_schedule.
      - by apply instantiated_interference_and_workload_consistent_with_sequential_jobs.
      - by apply instantiated_busy_intervals_are_bounded.
      - by apply instantiated_task_interference_is_bounded.
      - by eapply correct_search_space; eauto 2.
    Qed.
     
  End AbstractResponseTimeAnalysisForEDF. 
   
End AbstractRTAforEDFwithArrivalCurves. 