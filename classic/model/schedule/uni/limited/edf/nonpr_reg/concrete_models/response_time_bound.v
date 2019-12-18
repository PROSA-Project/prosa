Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.limited.schedule
               prosa.classic.model.schedule.uni.limited.edf.response_time_bound
               prosa.classic.model.schedule.uni.limited.edf.nonpr_reg.response_time_bound
               prosa.classic.model.schedule.uni.limited.rbf.
Require Import prosa.classic.model.arrival.curves.bounds
               prosa.classic.analysis.uni.arrival_curves.workload_bound.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule
               prosa.classic.model.schedule.uni.limited.platform.limited
               prosa.classic.model.schedule.uni.limited.platform.preemptive
               prosa.classic.model.schedule.uni.limited.platform.nonpreemptive.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * RTA for concrete models *)
(** In this module we prove the RTA theorems for (1) fully preemptive EDF model,
    (2) fully nonpreemptive EDF model, (3) EDF with fixed premption points, and 
    (4) EDF with floating nonpreemptive regions. *)
Module RTAforConcreteModels.

  Import Job ArrivalCurves TaskArrival Priority UniprocessorSchedule Workload Service
         ResponseTime MaxArrivalsWorkloadBound LimitedPreemptionPlatform ModelWithLimitedPreemptions
         RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves NonpreemptiveSchedule
         FullyNonPreemptivePlatform FullyPreemptivePlatform AbstractRTAforEDFwithArrivalCurves.
  
  Section Analysis.

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

    (* Consider the EDF policy that indicates a higher-or-equal priority relation. *)
    Let higher_eq_priority: JLFP_policy Job := EDF job_arrival job_relative_deadline.

    (* Consider any arrival sequence with consistent, non-duplicate arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* Consider an arbitrary task set ts. *)
    Variable ts: list Task.

    (* Assume that all jobs come from the task set... *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* ...and the cost of a job cannot be larger than the task cost. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq.

    (* Let max_arrivals be a family of proper arrival curves, i.e., for any task tsk in ts 
       [max_arrival tsk] is (1) an arrival bound of tsk, and (2) it is a monotonic function 
       that equals 0 for the empty interval delta = 0. *)
    Variable max_arrivals: Task -> time -> nat.
    Hypothesis H_family_of_proper_arrival_curves:
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts.

    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Next, consider any uniprocessor schedule... *)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Assume we have sequential jobs, i.e, jobs from the same 
       task execute in the order of their arrival. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.

    (* Next, we assume that the schedule is a work-conserving schedule. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

    (* Let's define some local names for clarity. *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    Let task_rbf_changes_at A := task_rbf_changes_at task_cost max_arrivals tsk A.
    Let bound_on_total_hep_workload_changes_at :=
      bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk.
    
    (* We introduce the abbreviation "rbf" for the task request bound function,
       which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a task T. *)
    Let rbf := task_request_bound_function task_cost max_arrivals.

    (* Next, we introduce task_rbf as an abbreviation
       for the task request bound function of task tsk. *)
    Let task_rbf := rbf tsk.

    (* Using the sum of individual request bound functions, we define the request bound 
       function of all tasks (total request bound function). *)
    Let total_rbf := total_request_bound_function task_cost max_arrivals ts.

    (* Next, we define an upper bound on interfering workload received from jobs 
       of other tasks with higher-than-or-equal priority. *)
    Let bound_on_total_hep_workload A Δ :=
      \sum_(tsk_o <- ts | tsk_o != tsk)
       rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

    (** * RTA for fully preemptive EDF model *)
    (** In this section we prove the RTA theorem for the fully preemptive EDF model *)
    Section RTAforFullyPreemptiveEDFModelwithArrivalCurves.
      
      (* First, we assume that the schedule respects the JLFP policy
         under a model with fixed preemption points. *)
      Hypothesis H_respects_policy:
        respects_JLFP_policy_at_preemption_point
          job_arrival job_cost arr_seq sched
          can_be_preempted_for_fully_preemptive_model higher_eq_priority.

      (* Let L be any positive fixed point of the busy interval recurrence. *)
      Variable L: time.
      Hypothesis H_L_positive: L > 0.
      Hypothesis H_fixed_point: L = total_rbf L.

      (* To reduce the time complexity of the analysis, recall the notion of search space. *)
      Let is_in_search_space A :=
        (A < L) && (task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A).
      
      (* Consider any value R, and assume that for any given arrival offset A in the search space,
         there is a solution of the response-time bound recurrence which is bounded by R. *)
      Variable R: nat.
      Hypothesis H_R_is_maximum:
        forall A,
          is_in_search_space A -> 
          exists F,
            A + F = task_rbf (A + ε) + bound_on_total_hep_workload A (A + F) /\
            F <= R.
          
      (* Now, we can leverage the results for the abstract model with bounded nonpreemptive segments
         to establish a response-time bound for the more concrete model of fully preemptive scheduling. *)
      Theorem uniprocessor_response_time_bound_fully_preemptive_edf:
        response_time_bounded_by tsk R.
      Proof.
        have BLOCK: RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
                      (fun _ => ε) D ts tsk = 0.
        { by rewrite /RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
                     subnn big1_eq. } 
        eapply uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments with
            (task_max_nps := fun _ => ε)
            (can_be_preempted := fun j prog => true)
            (task_lock_in_service := fun tsk => task_cost tsk)
            (job_lock_in_service := fun j => job_cost j)
            (job_max_nps := fun j => ε); eauto 2; try done.
        - by eapply fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions.
        - repeat split; try done.
          intros ? ? ? ARR; move => LE COMPL /negP NCOMPL.
          exfalso; apply: NCOMPL.
          apply completion_monotonic with t; try done.
        - repeat split; try done. 
          rewrite /task_lock_in_service_le_task_cost. by done.
          unfold task_lock_in_service_bounds_job_lock_in_service.
            by intros ? ARR TSK; rewrite -TSK; apply H_job_cost_le_task_cost. 
        - move => A /andP [LT NEQ].
          specialize (H_R_is_maximum A); feed H_R_is_maximum.
          { by apply/andP; split. }
          move: H_R_is_maximum => [F [FIX BOUND]].
          exists F; split.
          + by rewrite BLOCK add0n subnn subn0. 
          + by rewrite subnn addn0. 
      Qed.
      
    End RTAforFullyPreemptiveEDFModelwithArrivalCurves.
    
    (** * RTA for fully nonpreemptive EDF model *)
    (** In this section we prove the RTA theorem for the fully nonpreemptive EDF model. *)
    Section RTAforFullyNonPreemptiveEDFModelwithArrivalCurves.
      
      (* First, we assume that the schedule is nonpreemptive. *)
      Hypothesis H_nonpreemptive_sched: is_nonpreemptive_schedule job_cost sched.
      
      (* Next, we assume that the schedule respects the JLFP policy 
         under a model with fixed preemption points. *)
      Hypothesis H_respects_policy:
        respects_JLFP_policy_at_preemption_point
          job_arrival job_cost arr_seq sched
          (can_be_preempted_for_fully_nonpreemptive_model job_cost) higher_eq_priority.

      (* We also define a bound for the priority inversion caused by jobs with lower priority. *)
      Let blocking_bound :=
        \max_(tsk_other <- ts | (tsk_other != tsk) && (D tsk_other > D tsk))
         (task_cost tsk_other - ε).

      (* Let L be any positive fixed point of the busy interval recurrence. *)
      Variable L: time.
      Hypothesis H_L_positive: L > 0.
      Hypothesis H_fixed_point: L = total_rbf L.

      (* To reduce the time complexity of the analysis, recall the notion of search space. *)
      Let is_in_search_space A :=
        (A < L) && (task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A).
      
      (* Consider any value R, and assume that for any given arrival offset A in the search space,
         there is a solution of the response-time bound recurrence which is bounded by R. *)
      Variable R: nat.
      Hypothesis H_R_is_maximum:
        forall A,
          is_in_search_space A -> 
          exists F,
            A + F = blocking_bound + (task_rbf (A + ε) - (task_cost tsk - ε))
                    + bound_on_total_hep_workload A (A + F) /\
            F + (task_cost tsk - ε) <= R.

      (* Now, we can leverage the results for the abstract model with bounded nonpreemptive segments
         to establish a response-time bound for the more concrete model of fully nonpreemptive scheduling. *)
      Theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf:
        response_time_bounded_by tsk R.
      Proof.
        move: (posnP (task_cost tsk)) => [ZERO|POS].
        { intros j ARR TSK.
          have ZEROj: job_cost j = 0.
          { move: (H_job_cost_le_task_cost j ARR) => NEQ.
            rewrite /job_cost_le_task_cost TSK ZERO in NEQ.
              by apply/eqP; rewrite -leqn0.
          }
            by rewrite /is_response_time_bound_of_job /completed_by ZEROj.
        }
        eapply uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments with
            (job_max_nps := fun j => job_cost j)
            (task_max_nps := fun tsk => task_cost tsk)
            (job_lock_in_service := fun j => ε)
            (task_lock_in_service := fun tsk => ε)
            (L0 := L); eauto 2.
        - by eapply fully_nonpreemptive_model_is_correct; eauto 2.
        - eapply fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions; eauto 2.
        - repeat split; try done.
        - intros j t t' ARR LE SERV NCOMPL.
          rewrite /service in SERV; apply incremental_service_during in SERV.
          move: SERV => [t_first [/andP [_ H1] [H2 H3]]].
          apply H_nonpreemptive_sched with t_first; try done.
            by apply leq_trans with t; first apply ltnW.
        - repeat split; try done.
      Qed.
      
    End RTAforFullyNonPreemptiveEDFModelwithArrivalCurves.

    (** * RTA for EDF with fixed premption points *)
    (** In this module we prove a general RTA theorem for EDF-schedulers with fixed preemption points *)
    Section RTAforFixedPreemptionPointsModelwithArrivalCurves.
      
      (* First, let's assume we have the model with fixed preemption points. 
         I.e., each task is divided into a number of nonpreemptive segments 
         separated by statically predefined preemption points. *)
      Variable job_preemption_points: Job -> seq time.
      Variable task_preemption_points: Task -> seq time.
      Hypothesis H_model_with_fixed_preemption_points:
        fixed_preemption_points_model
          task_cost job_cost job_task arr_seq
          job_preemption_points task_preemption_points ts.

      (* Assume that the schedule is a uniprocessor schedule with limited preemptions... *)
      Hypothesis H_schedule_with_limited_preemptions:
        is_schedule_with_limited_preemptions arr_seq job_preemption_points sched.

      (* ... that respects the JLFP policy under a model with fixed preemption points. *)
      Hypothesis H_respects_policy:
        respects_JLFP_policy_at_preemption_point
          job_arrival job_cost arr_seq sched
          (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) higher_eq_priority.
      
      (* We also have a set of functions that map job or task 
         to its max or last nonpreemptive segment. *)
      Let job_max_nps := job_max_nps job_preemption_points.
      Let job_last_nps := job_last_nps job_preemption_points.
      Let task_max_nps := task_max_nps task_preemption_points.
      Let task_last_nps := task_last_nps task_preemption_points.   
      
      (* We define a bound for the priority inversion caused by jobs with lower priority. *)
      Let blocking_bound :=
        \max_(tsk_other <- ts | (tsk_other != tsk) && (D tsk_other > D tsk))
         (task_max_nps tsk_other - ε).
      
      (* Let L be any positive fixed point of the busy interval recurrence. *)
      Variable L: time.
      Hypothesis H_L_positive: L > 0.
      Hypothesis H_fixed_point: L = total_rbf L.

      (* To reduce the time complexity of the analysis, recall the notion of search space. *)
      Let is_in_search_space A :=
        (A < L) && (task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A). 
      
      (* Consider any value R, and assume that for any given arrival offset A in the search space,
         there is a solution of the response-time bound recurrence which is bounded by R. *)
      Variable R: nat.
      Hypothesis H_R_is_maximum:
        forall A,
          is_in_search_space A -> 
          exists F,
            A + F = blocking_bound
                    + (task_rbf (A + ε) - (task_last_nps tsk - ε)) 
                    + bound_on_total_hep_workload A (A + F) /\
            F + (task_last_nps tsk - ε) <= R.

      (* Now, we can leverage the results for the abstract model with bounded nonpreemptive segments
         to establish a response-time bound for the more concrete model of fixed preemption points.  *)
      Theorem uniprocessor_response_time_bound_edf_with_fixed_preemption_points:
        response_time_bounded_by tsk R.  
      Proof. 
        move: (H_model_with_fixed_preemption_points) => [MLP [BEG [END [INCR [HYP1 [HYP2 HYP3]]]]]].
        move: (MLP) => [EMPTj [LSMj [BEGj [ENDj HH]]]].
        move: (posnP (task_cost tsk)) => [ZERO|POSt].
        { intros j ARR TSK.
          move: (H_job_cost_le_task_cost _ ARR) => POSt.
          move: POSt; rewrite /job_cost_le_task_cost TSK ZERO leqn0; move => /eqP Z.
            by rewrite /is_response_time_bound_of_job /completed_by Z.
        } 
        have Fact2: 1 < size (task_preemption_points tsk).
        { have Fact2: 0 < size (task_preemption_points tsk).
          { apply/negPn/negP; rewrite -eqn0Ngt; intros CONTR; move: CONTR => /eqP CONTR.
            move: (END _ H_tsk_in_ts) => EQ.
            move: EQ; rewrite /last0 -nth_last nth_default; last by rewrite CONTR.
              by intros; rewrite -EQ in POSt.
          } 
          have EQ: 2 = size [::0; task_cost tsk]; first by done. 
          rewrite EQ; clear EQ.
          apply subseq_leq_size.
          rewrite !cons_uniq.
          { apply/andP; split.
            rewrite in_cons negb_or; apply/andP; split; last by done.
            rewrite neq_ltn; apply/orP; left; eauto 2.
            apply/andP; split; by done. } 
          intros t EQ; move: EQ; rewrite !in_cons.
          move => /orP [/eqP EQ| /orP [/eqP EQ|EQ]]; last by done.
          { rewrite EQ; clear EQ.
            move: (BEG _ H_tsk_in_ts) => EQ.
            rewrite -EQ; clear EQ.
            rewrite /first0 -nth0. 
            apply/(nthP 0).
            exists 0; by done.
          }
          { rewrite EQ; clear EQ.
            move: (END _ H_tsk_in_ts) => EQ.
            rewrite -EQ; clear EQ.
            rewrite /last0 -nth_last.
            apply/(nthP 0).
            exists ((size (task_preemption_points tsk)).-1); last by done. 
              by rewrite -(leq_add2r 1) !addn1 prednK //.
          }
        }
        eapply uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
          with (task_lock_in_service := fun tsk => (task_cost tsk - (task_last_nps tsk - ε))) 
               (job_lock_in_service := fun job => (job_cost job - (job_last_nps job - ε)))
               (L0 := L)(job_cost0 := job_cost) (task_max_nps0 := task_max_nps)
        ; eauto 2.
        { by apply model_with_fixed_preemption_points_is_correct. }
        { eapply model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions; eauto 2.
          intros j ARR. 
          unfold ModelWithLimitedPreemptions.job_max_nps, task_max_nps, lengths_of_segments.
          apply max_of_dominating_seq.
          intros. apply HYP2.
            by done.
        }
        { split; last split. 
          { intros j ARR POS.
            rewrite subn_gt0.
            rewrite subn1 -(leq_add2r 1) !addn1 prednK; last first.
            apply LSMj; try done. 
            rewrite /job_last_nps /ModelWithLimitedPreemptions.job_last_nps
                    ltnS /last0 -nth_last function_of_distances_is_correct.
            apply leq_trans with (job_max_nps j);
              first by apply distance_between_neighboring_elements_le_max_distance_in_seq. 
            rewrite -ENDj; last by done.
              by apply max_distance_in_seq_le_last_element_of_seq; eauto 2. 
          }  
          { by intros j ARR; rewrite leq_subLR leq_addl. }
          { intros ? ? ? ARR LE LS NCOMPL.
            rewrite subnBA in LS; last first.          
            apply LSMj; try done.
            { rewrite lt0n; apply/negP; intros Z; move: Z => /eqP Z.
                by move: NCOMPL; rewrite /completed_by -ltnNge Z ltn0; move => LT.
            }
            have EQ: exists Δ, t' = t + Δ.
            { exists (t' - t); rewrite subnKC; by done. }
            move: EQ => [Δ EQ]; subst t'; clear LE.
            rewrite -subh1 in LS.
            rewrite addn1 in LS.
            apply H_schedule_with_limited_preemptions; first by done.
            rewrite /can_be_preempted_for_model_with_limited_preemptions; apply/negP.
            intros CONTR.
            move: NCOMPL; rewrite /completed_by -ltnNge; move => SERV.
            have NEQ: job_cost j - job_last_nps j < service sched j (t + Δ).
            { apply leq_trans with (service sched j t); first by done.
              rewrite /service /service_during [in X in _ <= X](@big_cat_nat _ _ _ t) //=.
              rewrite leq_addr //. 
              rewrite leq_addr //.
            }
            clear LS.
            rewrite -ENDj in NEQ, SERV; last by done.
            rewrite last_seq_minus_last_distance_seq in NEQ; last by eauto 2.
            rewrite /last0 -nth_last in SERV. 
            have EQ := antidensity_of_nondecreasing_seq.
            specialize (EQ (job_preemption_points j) (service sched j (t + Δ)) (size (job_preemption_points j)).-2).
            rewrite CONTR in EQ.
            feed_n 2 EQ; first by eauto 2.
            {
              apply/andP; split; first by done.
              rewrite prednK; first by done.
              rewrite -(leq_add2r 1) !addn1 prednK.
              eapply number_of_preemption_points_at_least_two with (job_cost0 := job_cost); eauto 2.
              eapply list_of_preemption_point_is_not_empty with (job_cost0 := job_cost); eauto 2. 
            }
              by done.            
            rewrite -ENDj; last by done.
            apply leq_trans with (job_max_nps j).
            - by apply last_of_seq_le_max_of_seq.
            - by apply max_distance_in_seq_le_last_element_of_seq; eauto 2.
          }
        }
        {
          split.
          - by rewrite /task_lock_in_service_le_task_cost leq_subLR leq_addl.
          - intros j ARR TSK.
            move: (posnP (job_cost j)) => [ZERO | POS].
            { by rewrite ZERO. } 
            unfold task_last_nps.
            rewrite !subnBA; first last.
            apply LSMj; try done.
            rewrite /ModelWithLimitedPreemptions.task_last_nps /last0 -nth_last.
            apply HYP3.
              by done.
              rewrite -(ltn_add2r 1) !addn1 prednK //.
              move: (Fact2) => Fact3.
              rewrite size_of_seq_of_distances // addn1 ltnS // in Fact2. 
              rewrite -subh1 -?[in X in _ <= X]subh1; first last. 
              { apply leq_trans with (job_max_nps j).
                - by apply last_of_seq_le_max_of_seq. 
                - by rewrite -ENDj //; apply max_distance_in_seq_le_last_element_of_seq; eauto 2.
              } 
              { apply leq_trans with (task_max_nps tsk). 
                - by apply last_of_seq_le_max_of_seq. 
                - by rewrite -END //; apply max_distance_in_seq_le_last_element_of_seq; eauto 2.
              }
              rewrite -ENDj; last eauto 2.
              rewrite -END; last eauto 2.
              rewrite !last_seq_minus_last_distance_seq.
              have EQ: size (job_preemption_points j) = size (task_preemption_points tsk).
              { rewrite -TSK.
                  by apply HYP1.
              }
              rewrite EQ; clear EQ. 
              rewrite leq_add2r.
              apply domination_of_distances_implies_domination_of_seq; try done; eauto 2. 
              rewrite BEG // BEGj //.
              eapply number_of_preemption_points_at_least_two with (job_cost0 := job_cost); eauto 2.
              rewrite -TSK; apply HYP1; try done.
              intros.              rewrite -TSK; eauto 2.
              eauto 2.
              eauto 2.
        }
        { rewrite subKn; first by done.
          rewrite /task_last_nps  -(leq_add2r 1) subn1 !addn1 prednK; last first.
          { rewrite /ModelWithLimitedPreemptions.task_last_nps /last0 -nth_last.
            apply HYP3; try by done. 
            rewrite -(ltn_add2r 1) !addn1 prednK //.
            move: (Fact2) => Fact3.
              by rewrite size_of_seq_of_distances // addn1 ltnS // in Fact2.
          }        
          { apply leq_trans with (task_max_nps tsk).
            - by apply last_of_seq_le_max_of_seq. 
            - rewrite -END; last by done.
              apply ltnW; rewrite ltnS; try done.
                by apply max_distance_in_seq_le_last_element_of_seq; eauto 2. 
          }
        }
      Qed.
      
    End RTAforFixedPreemptionPointsModelwithArrivalCurves.
    
    (** * RTA for EDF with floating nonpreemptive regions *)
    (** In this module we prove a general RTA theorem for EDF-schedulers with floating nonpreemptive regions *)
    Section RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves.

      (* First, assume we have model with floating nonpreemptive regions. 
         I.e., for each task only the length of the maximal nonpreemptive 
         segment is known. *)
      Variable job_preemption_points: Job -> seq time.
      Variable task_max_nps: Task -> time.
      Hypothesis H_task_model_with_floating_nonpreemptive_regions:
        model_with_floating_nonpreemptive_regions
          job_cost job_task arr_seq job_preemption_points task_max_nps.

      (* Assume that the schedule is a uniprocessor schedule with limited preemptions... *)
      Hypothesis H_schedule_with_limited_preemptions:
        is_schedule_with_limited_preemptions arr_seq job_preemption_points sched.

      (* ... that respects the JLFP policy under a model with floating nonpreemptive regions. *)
      Hypothesis H_respects_policy:
        respects_JLFP_policy_at_preemption_point
          job_arrival job_cost arr_seq sched
          (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) higher_eq_priority.

      (* We also have two functions that map job to its max or last nonpreemptive segment. *)
      Let job_max_nps := job_max_nps job_preemption_points.
      Let job_last_nps := job_last_nps job_preemption_points.

      (* We define a bound for the priority inversion caused by jobs with lower priority. *)
      Definition blocking_bound :=
        \max_(tsk_other <- ts | (tsk_other != tsk) && (D tsk_other > D tsk))
         (task_max_nps tsk_other - ε).

      (* Let L be any positive fixed point of the busy interval recurrence. *)
      Variable L: time.
      Hypothesis H_L_positive: L > 0.
      Hypothesis H_fixed_point: L = total_rbf L.

      (* To reduce the time complexity of the analysis, recall the notion of search space. *)
      Let is_in_search_space A :=
        (A < L) && (task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A).
      
      (* Consider any value R, and assume that for any given arrival offset A in the search space,
         there is a solution of the response-time bound recurrence which is bounded by R. *)
      Variable R: nat.
      Hypothesis H_R_is_maximum:
        forall A,
          is_in_search_space A -> 
          exists F,
            A + F = blocking_bound + task_rbf (A + ε) + bound_on_total_hep_workload A (A + F) /\
            F <= R.

      (* Now, we can leverage the results for the abstract model with bounded nonpreemptive segments
         to establish a response-time bound for the more concrete model with floating nonpreemptive regions.  *)
      Theorem uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions:
        response_time_bounded_by tsk R.  
      Proof.
        move: (H_task_model_with_floating_nonpreemptive_regions) => [LIMJ JMLETM].
        move: (LIMJ) => [ZERO [LSMj [BEG [END HH]]]].
        eapply uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
          with (task_lock_in_service := fun tsk => task_cost tsk) 
               (job_lock_in_service := fun job => (job_cost job - (job_last_nps job - ε)))
               (L0 := L) (job_max_nps0 := job_max_nps)
               (job_cost0 := job_cost )
        ; eauto 2.
        { by apply model_with_fixed_preemption_points_is_correct. }
        { by eapply model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions; eauto 2. }
        { split; last split.
          { intros j ARR POS.
            rewrite subn_gt0.
            rewrite subn1 -(leq_add2r 1) !addn1 prednK; last first.
            apply LSMj; try done.
            rewrite /job_last_nps /ModelWithLimitedPreemptions.job_last_nps
                    ltnS /last0 -nth_last function_of_distances_is_correct.
            apply leq_trans with (job_max_nps j); first by apply distance_between_neighboring_elements_le_max_distance_in_seq.
            rewrite -END; last by done.
              by apply max_distance_in_seq_le_last_element_of_seq; eauto 2.
          }  
          { by intros j ARR; rewrite leq_subLR leq_addl. }
          { intros ? ? ? ARR LE LS NCOMPL.  
            rewrite subnBA in LS; last first.
            apply LSMj; try done.
            { rewrite lt0n; apply/negP; intros Z; move: Z => /eqP Z.
                by move: NCOMPL; rewrite /completed_by -ltnNge Z ltn0.
            }
            have EQ: exists Δ, t' = t + Δ.
            { exists (t' - t); rewrite subnKC; by done. }
            move: EQ => [Δ EQ]; subst t'; clear LE.
            rewrite -subh1 in LS.
            rewrite addn1 in LS.
            apply H_schedule_with_limited_preemptions; first by done.
            rewrite /can_be_preempted_for_model_with_limited_preemptions; apply/negP.
            intros CONTR.
            move: NCOMPL; rewrite /completed_by -ltnNge; move => SERV.
            have NEQ: job_cost j - (job_last_nps j) < service sched j (t + Δ).
            { apply leq_trans with (service sched j t); first by done.
              rewrite /service /service_during [in X in _ <= X](@big_cat_nat _ _ _ t) //=.
              rewrite leq_addr //.
              rewrite leq_addr //.
            }
            clear LS.
            rewrite -END in NEQ, SERV; last by done.
            rewrite last_seq_minus_last_distance_seq in NEQ.
            rewrite /last0 -nth_last in SERV. 
            have EQ := antidensity_of_nondecreasing_seq.
            specialize (EQ (job_preemption_points j) (service sched j (t + Δ)) (size (job_preemption_points j)).-2).
            rewrite CONTR in EQ.
            feed_n 2 EQ; first by eauto 2.
            {
              apply/andP; split; first by done.
              rewrite prednK; first by done.
              rewrite -(leq_add2r 1) !addn1 prednK.
              eapply number_of_preemption_points_at_least_two with (job_cost0 := job_cost); eauto 2. 
              eapply list_of_preemption_point_is_not_empty with (job_cost0 := job_cost); eauto 2. 
            }
              by done.
            eauto 2.
            rewrite -END; last by done.
            apply leq_trans with (job_max_nps j).
            - by apply last_of_seq_le_max_of_seq.
            - by apply max_distance_in_seq_le_last_element_of_seq; eauto 2.
          }
        }
        {
          split.
          - by rewrite /task_lock_in_service_le_task_cost. 
          - intros j ARR TSK.
            apply leq_trans with (job_cost j); first by rewrite leq_subr.
              by rewrite -TSK; eauto 2.
        }
        {
          rewrite subnn.
          intros.
          apply H_R_is_maximum in H.
          move: H => [F [EQ LE]].
          exists F.
            by rewrite subn0 addn0; split.
        }
      Qed.
      
    End RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves.
    
  End Analysis. 
  
End RTAforConcreteModels.