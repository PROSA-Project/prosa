Require Import rt.util.all.
Require Import rt.model.arrival.basic.job
               rt.model.arrival.basic.task_arrival
               rt.model.priority.
Require Import rt.model.schedule.uni.service
               rt.model.schedule.uni.workload
               rt.model.schedule.uni.schedule
               rt.model.schedule.uni.response_time.
Require Import rt.model.schedule.uni.limited.schedule
               rt.model.schedule.uni.limited.edf.nonpr_reg.response_time_bound
               rt.model.schedule.uni.limited.rbf.
Require Import rt.model.arrival.curves.bounds. 
Require Import rt.analysis.uni.arrival_curves.workload_bound.
Require Import rt.model.schedule.uni.limited.platform.limited.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.
 
(** * RTA for EDF-schedulers with fixed premption points *)
(** In this module we prove a general RTA theorem for EDF-schedulers with fixed preemption points *)
Module RTAforFixedPreemptionPointsModelwithArrivalCurves.

  Import Epsilon Job ArrivalCurves TaskArrival Priority UniprocessorSchedule Workload Service
         ResponseTime MaxArrivalsWorkloadBound LimitedPreemptionPlatform ModelWithLimitedPreemptions
         RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.
  
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

    (* The deadline of a job is equal to the deadline of the corresponding task. *)
    Let job_deadline j := D (job_task j).

    (* Consider the EDF policy that indicates a higher-or-equal priority relation. *)
    Let higher_eq_priority: JLFP_policy Job := EDF job_arrival job_deadline.

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

    (* Assume we have the model with fixed preemption points. I.e., each task is divided into 
       a number of nonpreemptive segments by inserting staticaly predefined preemption points. *)
    Variable job_preemption_points: Job -> seq time.
    Variable task_preemption_points: Task -> seq time.
    Hypothesis H_model_with_fixed_preemption_points:
      fixed_preemption_points_model
        task_cost job_cost job_task arr_seq
        job_preemption_points task_preemption_points ts.

    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Next, consider any uniprocessor schedule with limited preemptions... *)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.
    Hypothesis H_schedule_with_limited_preemptions:
      is_schedule_with_limited_preemptions arr_seq job_preemption_points sched.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Assume we have sequential jobs, i.e, jobs from the same 
       task execute in the order of their arrival. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.

    (* Next, we assume that the schedule is a work-conserving schedule which 
       respects the JLFP policy under a model with fixed preemption points. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_respects_policy:
      respects_JLFP_policy_at_preemption_point
        job_arrival job_cost arr_seq sched
        (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) higher_eq_priority.

    (* Let's define some local names for clarity. *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.

    (* We introduce a shortening "rbf" for the task request bound function,
       which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a task T. *)
    Let rbf := task_request_bound_function task_cost max_arrivals.

    (* Next, we introduce task_rbf as an abbreviation for the task request bound function of task tsk. *)
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.

    (* Using the sum of individual request bound functions, we define the request bound 
       function of all tasks (total request bound function). *)
    Let total_rbf := total_request_bound_function task_cost max_arrivals ts.

    (* Next, we define an upper bound on interfering workload received from jobs
       with higher-than-or-equal priority. *)
    Let W A Δ :=
      \sum_(tsk_o <- ts | tsk_o != tsk)
       rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

    (* We also have a set of functions that map job or task 
       to its max or last nonpreemptive segment. *)
    Let job_max_nps := job_max_nps job_preemption_points.
    Let job_last_nps := job_last_nps job_preemption_points.
    Let task_max_nps := task_max_nps task_preemption_points.
    Let task_last_nps := task_last_nps task_preemption_points.   
    
    (* We also define a bound for the priority inversion caused by jobs with lower priority. *)
    Definition blocking_bound :=
      \max_(tsk_other <- ts | (tsk_other != tsk) && (D tsk_other > D tsk))
       (task_max_nps tsk_other - ε).
    
    (* Let L be any positive fixed point of the busy interval recurrence, determined by 
       the sum of blocking and higher-or-equal-priority workload. *)
    Variable L: time.
    Hypothesis H_L_positive: L > 0.
    Hypothesis H_fixed_point: L = blocking_bound + total_rbf L.

    (* To reduce the time complexity of the analysis, recall the notion of search space. *)
    Let is_in_search_space A :=
      (A < L)
        && ((task_rbf A != task_rbf (A + ε))
            || has (fun tsko =>
                     (tsk != tsko)
                       && (rbf tsko (A + D tsk - D tsko)
                               != rbf tsko ((A + ε) + D tsk - D tsko))) ts).

    (* Next, consider any value R, and assume that for any given arrival A from search space
       there is a solution of the response-time bound recurrence which is bounded by R. *)
    Variable R: nat.
    Hypothesis H_R_is_maximum:
      forall A,
        is_in_search_space A -> 
        exists F,
          A + F = blocking_bound
                  + (task_rbf (A + ε) - (task_last_nps tsk - ε)) 
                  + W A (A + F) /\
          F + (task_last_nps tsk - ε) <= R.

    (* Now, we can reuse the results for the abstract model of bounded nonpreemptive segments 
       to establish a response time bound for the concrete model of fixed preemption points.  *)
    Theorem uniprocessor_response_time_bound_edf_with_fixed_preemption_points:
      response_time_bounded_by tsk R.  
    Proof. 
      move: (H_model_with_fixed_preemption_points) => [MLP [BEG [END [INCR [HYP1 [HYP2 HYP3]]]]]].
      move: (MLP) => [EMPTj [LSMj [BEGj [ENDj HH]]]].
      move: (posnP (task_cost tsk)) => [ZERO|POSt].
      { intros j ARR TSK.
        move: (H_job_cost_le_task_cost _ ARR) => POSt.
        move: POSt; rewrite /job_cost_le_task_cost TSK ZERO leqn0; move => /eqP Z.
        rewrite /is_response_time_bound_of_job /completed_by eqn_leq; apply/andP; split.
        - by eauto 2.
        - by rewrite Z.
      } 
      have Fact2: 1 < size (task_preemption_points tsk).
      { have Fact2: 0 < size (task_preemption_points tsk).
        { apply/negPn/negP; rewrite -eqn0Ngt; intros CONTR; move: CONTR => /eqP CONTR.
          move: (END _ H_tsk_in_ts) => EQ.
          move: EQ; rewrite /NondecreasingSequence.last -nth_last nth_default; last by rewrite CONTR.
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
          rewrite /NondecreasingSequence.first -nth0. 
          apply/(nthP 0).
          exists 0; by done.
        }
        { rewrite EQ; clear EQ.
          move: (END _ H_tsk_in_ts) => EQ.
          rewrite -EQ; clear EQ.
          rewrite /NondecreasingSequence.last -nth_last.
          apply/(nthP 0).
          exists ((size (task_preemption_points tsk)).-1); last by done. 
            by rewrite -(leq_add2r 1) !addn1 prednK //.
        }
      }
      eapply uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
        with (task_lock_in_service := fun tsk => (task_cost tsk - (task_last_nps tsk - ε))) 
             (job_lock_in_service := fun job => (job_cost job - (job_last_nps job - ε)))
             (L0 := L) (job_max_nps0 := job_max_nps)
             (job_cost0 := job_cost )
      ; eauto 2.
      { by apply model_with_fixed_preemption_points_is_correct. }
      { eapply model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions; eauto 2.
        intros j ARR. 
        unfold ModelWithLimitedPreemptions.job_max_nps, task_max_nps, lengths_of_segments.
        apply NondecreasingSequence.max_of_dominating_seq.
        intros. apply HYP2.
          by done.
      }
      { split; last split. 
        { intros j ARR POS.
          rewrite subn_gt0.
          rewrite subn1 -(leq_add2r 1) !addn1 prednK; last first.
          apply LSMj; try done. 
          rewrite /job_last_nps /ModelWithLimitedPreemptions.job_last_nps
                  ltnS /NondecreasingSequence.last -nth_last NondecreasingSequence.function_of_distances_is_correct.
          apply leq_trans with (job_max_nps j);
            first by apply NondecreasingSequence.distance_between_neighboring_elements_le_max_distance_in_seq. 
          rewrite -ENDj; last by done.
            by apply NondecreasingSequence.max_distance_in_seq_le_last_element_of_seq; eauto 2. 
        }  
        { by intros j ARR; rewrite leq_subLR leq_addl. }
        { intros ? ? ? ARR LE LS NCOMPL.
          rewrite subnBA in LS; last first.          
          apply LSMj; try done.
          { rewrite lt0n; apply/negP; intros Z; move: Z => /eqP Z.
            move: NCOMPL; rewrite /completed_by neq_ltn; move => /orP [LT|GT].
            { by rewrite Z ltn0 in LT. }
            { move: GT; rewrite ltnNge; move => /negP GT; apply: GT.
                by eapply H_completed_jobs_dont_execute.
            }
          }
          have EQ: exists Δ, t' = t + Δ.
          { exists (t' - t); rewrite subnKC; by done. }
          move: EQ => [Δ EQ]; subst t'; clear LE.
          rewrite -subh1 in LS.
          rewrite addn1 in LS.
          apply H_schedule_with_limited_preemptions; first by done.
          rewrite /can_be_preempted_for_model_with_limited_preemptions; apply/negP.
          intros CONTR.
          move: NCOMPL; rewrite /completed_by neq_ltn; move => /orP [SERV|SERV]; last first.
          { exfalso.
            move: (H_completed_jobs_dont_execute j (t + Δ)); rewrite leqNgt; move => /negP T.
              by apply: T.
          }
          { have NEQ: job_cost j - job_last_nps j < service sched j (t + Δ).
            { apply leq_trans with (service sched j t); first by done.
              rewrite /service /service_during [in X in _ <= X](@big_cat_nat _ _ _ t) //=.
              rewrite leq_addr //. 
              rewrite leq_addr //.
            }
            clear LS.
            rewrite -ENDj in NEQ, SERV; last by done.
            rewrite NondecreasingSequence.last_seq_minus_last_distance_seq in NEQ; last by eauto 2.
            rewrite /NondecreasingSequence.last -nth_last in SERV. 
            have EQ := NondecreasingSequence.antidensity_of_nondecreasing_seq.
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
          }
          rewrite -ENDj; last by done.
          apply leq_trans with (job_max_nps j).
          - by apply NondecreasingSequence.last_of_seq_le_max_of_seq.
          - by apply NondecreasingSequence.max_distance_in_seq_le_last_element_of_seq; eauto 2.
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
          rewrite /ModelWithLimitedPreemptions.task_last_nps /NondecreasingSequence.last -nth_last.
          apply HYP3.
            by done.
            rewrite -(ltn_add2r 1) !addn1 prednK //.
          move: (Fact2) => Fact3.
          rewrite NondecreasingSequence.size_of_seq_of_distances // addn1 ltnS // in Fact2. 
          rewrite -subh1 -?[in X in _ <= X]subh1; first last. 
          { apply leq_trans with (job_max_nps j).
            - by apply NondecreasingSequence.last_of_seq_le_max_of_seq. 
            - by rewrite -ENDj //; apply NondecreasingSequence.max_distance_in_seq_le_last_element_of_seq; eauto 2.
          } 
          { apply leq_trans with (task_max_nps tsk). 
            - by apply NondecreasingSequence.last_of_seq_le_max_of_seq. 
            - by rewrite -END //; apply NondecreasingSequence.max_distance_in_seq_le_last_element_of_seq; eauto 2.
          }
          rewrite -ENDj; last eauto 2.
          rewrite -END; last eauto 2.
          rewrite !NondecreasingSequence.last_seq_minus_last_distance_seq.
          have EQ: size (job_preemption_points j) = size (task_preemption_points tsk).
          { rewrite -TSK.
              by apply HYP1.
          }
          rewrite EQ; clear EQ. 
          rewrite leq_add2r.
          apply NondecreasingSequence.domination_of_distances_implies_domination_of_seq; try done; eauto 2. 
          rewrite BEG // BEGj //.
          eapply number_of_preemption_points_at_least_two with (job_cost0 := job_cost); eauto 2.
          rewrite -TSK; apply HYP1; try done.
                    intros.              rewrite -TSK; eauto 2.
                    eauto 2.
                    eauto 2.
      }
      { rewrite subKn; first by done.
        rewrite /task_last_nps  -(leq_add2r 1) subn1 !addn1 prednK; last first.
        { rewrite /ModelWithLimitedPreemptions.task_last_nps /NondecreasingSequence.last -nth_last.
          apply HYP3; try by done. 
          rewrite -(ltn_add2r 1) !addn1 prednK //.
          move: (Fact2) => Fact3.
            by rewrite NondecreasingSequence.size_of_seq_of_distances // addn1 ltnS // in Fact2.
        }        
        { apply leq_trans with (task_max_nps tsk).
          - by apply NondecreasingSequence.last_of_seq_le_max_of_seq. 
          - rewrite -END; last by done.
            apply ltnW; rewrite ltnS; try done.
              by apply NondecreasingSequence.max_distance_in_seq_le_last_element_of_seq; eauto 2. 
        }
      }
    Qed.
     
  End Analysis. 
   
End RTAforFixedPreemptionPointsModelwithArrivalCurves.