Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task_arrival rt.model.priority.
Require Import rt.model.schedule.uni.service
               rt.model.schedule.uni.workload
               rt.model.schedule.uni.schedule 
               rt.model.schedule.uni.response_time.
Require Import rt.model.schedule.uni.nonpreemptive.schedule.
Require Import rt.model.schedule.uni.limited.schedule
               rt.model.schedule.uni.limited.edf.nonpr_reg.response_time_bound.
Require Import rt.model.arrival.curves.bounds.
Require Import rt.analysis.uni.arrival_curves.workload_bound.

Require Import rt.model.schedule.uni.limited.platform.nonpreemptive.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * RTA for fully nonpreemptive EDF model *)
(** In this module we prove the RTA theorem for the fully nonpreemptive EDF model. *)
Module RTAforFullyNonPreemptiveEDFModelwithArrivalCurves.

  Import Epsilon Job ArrivalCurves TaskArrival Priority UniprocessorSchedule
         NonpreemptiveSchedule Workload Service FullyNonPreemptivePlatform
         ResponseTime MaxArrivalsWorkloadBound LimitedPreemptionPlatform
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

    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Next, consider any uniprocessor nonpreemptive schedule...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.
    Hypothesis H_nonpreemptive_sched: is_nonpreemptive_schedule job_cost sched.

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
        (can_be_preempted_for_fully_nonpreemptive_model job_cost) higher_eq_priority.

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

    (* We also define a bound for the priority inversion caused by jobs with lower priority. *)
    Definition blocking_bound :=
      \max_(tsk_other <- ts | (tsk_other != tsk) && (D tsk_other > D tsk))
       (task_cost tsk_other - ε).

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
          A + F = blocking_bound + (task_rbf (A + ε) - (task_cost tsk - ε)) + W A (A + F) /\
          F + (task_cost tsk - ε) <= R.

    (* Now, we can reuse the results for the abstract model with fixed preemption points to 
       establish a response-time bound for the more concrete model of fully nonpreemptive scheduling. *)
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
        rewrite /is_response_time_bound_of_job /completed_by eqn_leq; apply/andP; split.
        - by apply H_completed_jobs_dont_execute.
        - by rewrite ZEROj.
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
    
  End Analysis.
   
End RTAforFullyNonPreemptiveEDFModelwithArrivalCurves. 