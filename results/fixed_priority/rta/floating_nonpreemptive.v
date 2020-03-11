Require Export prosa.results.fixed_priority.rta.bounded_nps.
Require Export prosa.analysis.facts.preemption.rtc_threshold.floating.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.


(** * RTA for Model with Floating Non-Preemptive Regions *)
(** In this module we prove the RTA theorem for floating non-preemptive regions FP model. *)

(** Throughout this file, we assume the FP priority policy, ideal uni-processor 
    schedules, and the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.processor.ideal.
Require Import prosa.model.readiness.basic.

(** Furthermore, we assume the task model with floating non-preemptive regions. *)
Require Import prosa.model.preemption.limited_preemptive.
Require Import prosa.model.task.preemption.floating_nonpreemptive.

(** ** Setup and Assumptions *)

Section RTAforFloatingModelwithArrivalCurves.

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

  (** Assume we have the model with floating non-preemptive regions. 
      I.e., for each task only the length of the maximal non-preemptive 
      segment is known _and_ each job level is divided into a number of
      non-preemptive segments by inserting preemption points. *)
  Context `{JobPreemptionPoints Job}
          `{TaskMaxNonpreemptiveSegment Task}.
  Hypothesis H_valid_task_model_with_floating_nonpreemptive_regions:
    valid_model_with_floating_nonpreemptive_regions arr_seq.

  (** Consider an arbitrary task set ts, ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.
  
  (** ... and the cost of a job cannot be larger than the task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task [tsk] in ts 
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) it is a monotonic function 
     that equals [0] for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Next, consider any ideal uni-processor schedule with limited preemptions of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_schedule_with_limited_preemptions:
    schedule_respects_preemption_model arr_seq sched.
  
  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider an FP policy that indicates a higher-or-equal priority relation,
      and assume that the relation is reflexive and transitive. *)
  Context `{FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.
  Hypothesis H_priority_is_transitive : transitive_priorities.

  (** Assume we have sequential tasks, i.e, jobs from the 
      same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks sched.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  
  (** ... and the schedule respects the policy defined by the [job_preemptable] 
     function (i.e., jobs have bounded non-preemptive segments). *)
  Hypothesis H_respects_policy : respects_policy_at_preemption_point arr_seq sched.

  (** ** Total Workload and Length of Busy Interval *)

  (** We introduce the abbreviation [rbf] for the task request bound function,
       which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a task T. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce [task_rbf] as an abbreviation
      for the task request bound function of task [tsk]. *)
  Let task_rbf := rbf tsk.

  (** Using the sum of individual request bound functions, we define
      the request bound function of all tasks with higher priority
      ... *)
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.

  (** ... and the request bound function of all tasks with higher
      priority other than task [tsk]. *)
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.

  (** Next, we define a bound for the priority inversion caused by tasks of lower priority. *)
  Let blocking_bound :=
    \max_(tsk_other <- ts | ~~ hep_task tsk_other tsk)
     (task_max_nonpreemptive_segment tsk_other - ε).
  
  (** Let L be any positive fixed point of the busy interval recurrence, determined by 
      the sum of blocking and higher-or-equal-priority workload. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = blocking_bound + total_hep_rbf L.

  (** ** Response-Time Bound *)

  (** To reduce the time complexity of the analysis, recall the notion of search space. *)
  Let is_in_search_space := is_in_search_space tsk L.
  
  (** Next, consider any value R, and assume that for any given
      arrival A from search space there is a solution of the
      response-time bound recurrence which is bounded by R. *)    
  Variable R : duration.
  Hypothesis H_R_is_maximum:
    forall (A : duration),
      is_in_search_space A ->
      exists  (F : duration),
        A + F = blocking_bound + task_rbf (A + ε) + total_ohep_rbf (A + F) /\
        F <= R.
  
  (** Now, we can reuse the results for the abstract model with
      bounded nonpreemptive segments to establish a response-time
      bound for the more concrete model with floating nonpreemptive
      regions.  *)

  Let response_time_bounded_by := task_response_time_bound arr_seq sched.

  Theorem uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions:
    response_time_bounded_by tsk R.  
  Proof.
    move: (H_valid_task_model_with_floating_nonpreemptive_regions) => [LIMJ JMLETM].
    move: (LIMJ) => [BEG [END _]].
    eapply uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments.
    all: eauto 2 with basic_facts.
    intros A SP.
    rewrite subnn subn0.
    destruct (H_R_is_maximum _ SP) as [F [EQ LE]].
      by exists F; rewrite addn0; split.
  Qed.

End RTAforFloatingModelwithArrivalCurves.
