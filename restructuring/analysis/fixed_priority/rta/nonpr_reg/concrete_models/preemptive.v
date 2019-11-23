Require Export rt.restructuring.analysis.fixed_priority.rta.nonpr_reg.response_time_bound.
Require Export rt.restructuring.analysis.basic_facts.preemption.task.preemptive.
Require Export rt.restructuring.analysis.basic_facts.preemption.rtc_threshold.preemptive.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require Import rt.restructuring.model.processor.ideal.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import rt.restructuring.model.readiness.basic.

(** Throughout this file, we assume the fully preemptive task model. *)
Require Import rt.restructuring.model.task.preemption.fully_preemptive.

(** * RTA for Fully Preemptive FP Model *)
(** In this module we prove the RTA theorem for fully preemptive FP model. *)
Section RTAforFullyPreemptiveFPModelwithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** Consider an arbitrary task set ts, ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.
  
  (** ... and the cost of a job cannot be larger than the task cost. *)
  Hypothesis H_job_cost_le_task_cost:
    cost_of_jobs_from_arrival_sequence_le_task_cost arr_seq.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
      any task tsk in ts [max_arrival tsk] is (1) an arrival bound of
      tsk, and (2) it is a monotonic function that equals 0 for the
      empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let tsk be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Next, consider any ideal uniprocessor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider an FP policy that indicates a higher-or-equal priority relation,
     and assume that the relation is reflexive and transitive. *)
  Variable higher_eq_priority : FP_policy Task.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.
  Hypothesis H_priority_is_transitive : transitive_priorities.

  (** Assume we have sequential tasks, i.e, tasks from the 
     same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks sched.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  
  (** ... and the schedule respects the policy defined by thejob_preemptable 
     function (i.e., jobs have bounded nonpreemptive segments). *)
  Hypothesis H_respects_policy : respects_policy_at_preemption_point arr_seq sched.  

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let total_hep_rbf := total_hep_request_bound_function_FP _ ts tsk.
  Let total_ohep_rbf := total_ohep_request_bound_function_FP _ ts tsk.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.
  
  (** Let L be any positive fixed point of the busy interval recurrence, determined by 
      the sum of blocking and higher-or-equal-priority workload. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_hep_rbf L.

  (** To reduce the time complexity of the analysis, recall the notion of search space. *)
  Let is_in_search_space (A : duration) := (A < L) && (task_rbf A != task_rbf (A + ε)).
  
  (** Next, consider any value R, and assume that for any given arrival A from search space
       there is a solution of the response-time bound recurrence which is bounded by R. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum:
    forall (A : duration),
      is_in_search_space A -> 
      exists (F : duration),
        A + F = task_rbf (A + ε) + total_ohep_rbf (A + F) /\
        F <= R.

  (** Now, we can leverage the results for the abstract model with bounded nonpreemptive segments
       to establish a response-time bound for the more concrete model of fully preemptive scheduling. *)
  Theorem uniprocessor_response_time_bound_fully_preemptive_fp:
    response_time_bounded_by tsk R.
  Proof.
    have BLOCK: blocking_bound  higher_eq_priority ts tsk = 0.
    { by rewrite /blocking_bound /parameters.task_max_nonpreemptive_segment
               /fully_preemptive.fully_preemptive_model subnn big1_eq. } 
    eapply uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments.      
    all: eauto 2 with basic_facts.
    - by rewrite BLOCK add0n.
    - move => A /andP [LT NEQ].
      edestruct H_R_is_maximum as [F [FIX BOUND]].
      { by apply/andP; split; eauto 2. }
      exists F; split.
      + by rewrite BLOCK add0n subnn subn0.
      + by rewrite subnn addn0.
  Qed.
  
End RTAforFullyPreemptiveFPModelwithArrivalCurves. 
