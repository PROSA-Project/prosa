Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task_arrival rt.model.priority.
Require Import rt.model.schedule.uni.service
               rt.model.schedule.uni.workload
               rt.model.schedule.uni.schedule
               rt.model.schedule.uni.response_time.
Require Import rt.model.schedule.uni.limited.platform.preemptive
               rt.model.schedule.uni.limited.schedule
               rt.model.schedule.uni.limited.fixed_priority.nonpr_reg.response_time_bound.
Require Import rt.model.arrival.curves.bounds.
Require Import rt.analysis.uni.arrival_curves.workload_bound.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * RTA for fully preemptive FP model *)
(* In this module we prove the RTA theorem for fully preemptive FP model *)
Module RTAforFullyPreemptiveFPModelwithArrivalCurves. 
               
  Import Epsilon Job ArrivalCurves TaskArrival Priority UniprocessorSchedule Workload Service
         ResponseTime MaxArrivalsWorkloadBound FullyPreemptivePlatform LimitedPreemptionPlatform
         RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.

  (* In this section we prove that the maximum among the solutions of the response-time bound 
     recurrence for some set of parameters is a response time bound for tsk. *)
  Section Analysis.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.    
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
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

    (* Let tsk be any task in ts. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.
    
    (* Next, consider any uniprocessor schedule of the arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

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
       respects the FP policy under a fully preemptive model. *) 
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_respects_policy:
      respects_FP_policy_at_preemption_point
        job_arrival job_cost job_task arr_seq sched
        (can_be_preempted_for_fully_preemptive_model) higher_eq_priority. 

    (* Let's define some local names for clarity. *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.    
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.
    Let total_hep_rbf :=
      total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.
    Let total_ohep_rbf :=
      total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.

    (* Let L be any positive fixed point of the busy interval recurrence, determined by 
       the sum of blocking and higher-or-equal-priority workload. *)
    Variable L: time.
    Hypothesis H_L_positive: L > 0.
    Hypothesis H_fixed_point: L = total_hep_rbf L.

    (* To reduce the time complexity of the analysis, recall the notion of search space. *)
    Let is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).
    
    (* Next, consider any value R, and assume that for any given arrival A from search space
       there is a solution of the response-time bound recurrence which is bounded by R. *)
    Variable R: nat.
    Hypothesis H_R_is_maximum:
      forall A,
        is_in_search_space A -> 
        exists F,
          A + F = task_rbf (A + ε) + total_ohep_rbf (A + F) /\
          F <= R.

    (* Now, we can reuse the results for the abstract model with fixed preemption 
       points to establish a response-time bound for the more concrete model 
       of fully-preemptive scheduling. *)
    Theorem uniprocessor_response_time_bound_fully_preemptive_fp:
      response_time_bounded_by tsk R.
    Proof.
      have BLOCK: RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound (fun _ => ε) higher_eq_priority ts tsk = 0.
      { by rewrite /RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound subnn big1_eq. } 
      eapply uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments with
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
        rewrite /completed_by eqn_leq; apply/andP; split; try done.
      - repeat split; try done. 
        rewrite /task_lock_in_service_le_task_cost. by done.
        unfold task_lock_in_service_bounds_job_lock_in_service.
          by intros ? ARR TSK; rewrite -TSK; apply H_job_cost_le_task_cost. 
      - by rewrite BLOCK add0n.
      - move => A /andP [LT NEQ].
        specialize (H_R_is_maximum A); feed H_R_is_maximum.
        { by apply/andP; split. }
        move: H_R_is_maximum => [F [FIX BOUND]].
        exists F; split.
        + by rewrite BLOCK add0n subnn subn0. 
        + by rewrite subnn addn0. 
    Qed.
    
  End Analysis.
  
End RTAforFullyPreemptiveFPModelwithArrivalCurves. 