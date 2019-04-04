Require Import rt.util.all.
Require Import rt.model.arrival.basic.job
               rt.model.arrival.basic.task_arrival
               rt.model.priority.
Require Import rt.model.schedule.uni.service
               rt.model.schedule.uni.workload
               rt.model.schedule.uni.schedule
               rt.model.schedule.uni.response_time.
Require Import rt.model.schedule.uni.limited.schedule
               rt.model.schedule.uni.limited.fixed_priority.nonpr_reg.response_time_bound
               rt.model.schedule.uni.limited.rbf.
Require Import rt.model.arrival.curves.bounds. 
Require Import rt.analysis.uni.arrival_curves.workload_bound.
Require Import rt.model.schedule.uni.limited.platform.limited.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.
 
(** * RTA for FP-schedulers with floating nonpreemptive regions *)
(** In this module we prove a general RTA theorem for FP-schedulers with floating nonpreemptive regions *)
Module RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves.

  Import Epsilon Job ArrivalCurves TaskArrival Priority UniprocessorSchedule Workload Service
         ResponseTime MaxArrivalsWorkloadBound LimitedPreemptionPlatform ModelWithLimitedPreemptions
         RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.
  
  Section Analysis.

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

    (* Assume we have the model with floating nonpreemptive regions. I.e., for each
       task only the length of the maximal nonpreemptive segment is known. *)
    Variable job_preemption_points: Job -> seq time.
    Variable task_max_nps: Task -> time.
    Hypothesis H_task_model_with_floating_nonpreemptive_regions:
      model_with_floating_nonpreemptive_regions
        job_cost job_task arr_seq job_preemption_points task_max_nps.
    
    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.
    
    (* Next, consider any uniprocessor schedule with limited preemptions...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.
    Hypothesis H_schedule_with_limited_preemptions:
      is_schedule_with_limited_preemptions arr_seq job_preemption_points sched.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Assume we have sequential jobs. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.
    
    (* Consider an FP policy that indicates a higher-or-equal priority relation,
       and assume that the relation is reflexive and transitive. *) 
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.

    (* Next, we assume that the schedule is a work-conserving schedule which 
       respects the FP policy under a model with fixed preemption points. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_respects_policy:
      respects_FP_policy_at_preemption_point
        job_arrival job_cost job_task arr_seq sched
        (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) higher_eq_priority.
    
    (* Let's define some local names for clarity. *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.    
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.
    Let total_hep_rbf :=
      total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.
    Let total_ohep_rbf :=
      total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.
    Let job_max_nps := job_max_nps job_preemption_points.
    Let job_last_nps := job_last_nps job_preemption_points.
    
    (* Next, we define a bound for the priority inversion caused by tasks of lower priority. *)
    Definition blocking :=
      \max_(tsk_other <- ts | ~~ higher_eq_priority tsk_other tsk) (task_max_nps tsk_other - ε).
    
    (* Let L be any positive fixed point of the busy interval recurrence, determined by 
       the sum of blocking and higher-or-equal-priority workload. *)
    Variable L: time.
    Hypothesis H_L_positive: L > 0.
    Hypothesis H_fixed_point: L = blocking + total_hep_rbf L.

    (* To reduce the time complexity of the analysis, recall the notion of search space. *)
    Let is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).
    
    (* Next, consider any value R, and assume that for any given arrival A from search space
       there is a solution of the response-time bound recurrence which is bounded by R. *)    
    Variable R: nat.
    Hypothesis H_R_is_maximum:
      forall A,
        is_in_search_space A ->
        exists  F,
          A + F = blocking + task_rbf (A + ε) + total_ohep_rbf (A + F) /\
          F <= R.

    (* Now, we can reuse the results for the abstract model of bounded nonpreemptive segments 
       to establish a response time bound for the concrete model with floating nonpreemptive regions.  *)
    Theorem uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions:
      response_time_bounded_by tsk R.  
    Proof.
      move: (H_task_model_with_floating_nonpreemptive_regions) => [LIMJ JMLETM].
      move: (LIMJ) => [ZERO [LSMj [BEG [END HH]]]].
      eapply uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments
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
                  ltnS /NondecreasingSequence.last -nth_last NondecreasingSequence.function_of_distances_is_correct.
          apply leq_trans with (job_max_nps j); first by apply NondecreasingSequence.distance_between_neighboring_elements_le_max_distance_in_seq.
          rewrite -END; last by done.
            by apply NondecreasingSequence.max_distance_in_seq_le_last_element_of_seq; eauto 2.
        }  
        { by intros j ARR; rewrite leq_subLR leq_addl. }
        { intros ? ? ? ARR LE LS NCOMPL.  
          rewrite subnBA in LS; last first.
          apply LSMj; try done.
          { rewrite lt0n; apply/negP; intros Z; move: Z => /eqP Z.
            move: NCOMPL. rewrite /completed_by neq_ltn. move => /orP [LT|GT].
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
          { have NEQ: job_cost j - (job_last_nps j) < service sched j (t + Δ).
            { apply leq_trans with (service sched j t); first by done.
              rewrite /service /service_during [in X in _ <= X](@big_cat_nat _ _ _ t) //=.
              rewrite leq_addr //.
              rewrite leq_addr //.
            }
            clear LS.
            rewrite -END in NEQ, SERV; last by done.
            rewrite NondecreasingSequence.last_seq_minus_last_distance_seq in NEQ.
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
            eauto 2.
          }
          rewrite -END; last by done.
          apply leq_trans with (job_max_nps j).
          - by apply NondecreasingSequence.last_of_seq_le_max_of_seq.
          - by apply NondecreasingSequence.max_distance_in_seq_le_last_element_of_seq; eauto 2.
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
     
  End Analysis.
    
End RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves.