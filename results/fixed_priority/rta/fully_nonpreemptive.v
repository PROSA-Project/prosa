Require Export rt.results.fixed_priority.rta.bounded_nps.
Require Export rt.analysis.facts.preemption.task.nonpreemptive.
Require Export rt.analysis.facts.preemption.rtc_threshold.nonpreemptive.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import rt.model.processor.ideal.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import rt.model.readiness.basic.

(** Throughout this file, we assume the fully non-preemptive task model. *)
Require Import rt.model.task.preemption.fully_nonpreemptive.

(** * RTA for Fully Non-Preemptive FP Model *)
(** In this module we prove the RTA theorem for the fully non-preemptive FP model. *)
Section RTAforFullyNonPreemptiveFPModelwithArrivalCurves.

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
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
      any task [tsk] in ts [max_arrival tsk] is (1) an arrival bound of
      [tsk], and (2) it is a monotonic function that equals [0] for the
      empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Next, consider any ideal non-preemptive uniprocessor schedule of
      this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule  sched.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider an FP policy that indicates a higher-or-equal priority relation,
     and assume that the relation is reflexive and transitive. *)
  Context `{FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.
  Hypothesis H_priority_is_transitive : transitive_priorities.

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.  

  (** Assume we have sequential tasks, i.e, tasks from the same task
      execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks sched.

  (** Next, we assume that the schedule is a work-conserving schedule ... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.
  
  (** ... and the schedule respects the policy defined by the
     [job_preemptable] function (i.e., jobs have bounded nonpreemptive
     segments). *)
  Hypothesis H_respects_policy : respects_policy_at_preemption_point arr_seq sched.    

  (** Next, we define a bound for the priority inversion caused by tasks of lower priority. *)
  Let blocking_bound :=
    \max_(tsk_other <- ts | ~~ hep_task tsk_other tsk) (task_cost tsk_other - ε).
  
  (** Let L be any positive fixed point of the busy interval recurrence, determined by 
      the sum of blocking and higher-or-equal-priority workload. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = blocking_bound + total_hep_rbf L.

  (** To reduce the time complexity of the analysis, recall the notion of search space. *)
  Let is_in_search_space (A : duration) := (A < L) && (task_rbf A != task_rbf (A + ε)).
  
  (** Next, consider any value R, and assume that for any given arrival A from search space
      there is a solution of the response-time bound recurrence which is bounded by R. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum:
    forall (A : duration),
      is_in_search_space A -> 
      exists (F : duration),
        A + F = blocking_bound
                + (task_rbf (A + ε) - (task_cost tsk - ε))
                + total_ohep_rbf (A + F) /\
        F + (task_cost tsk - ε) <= R.
  
  (** Now, we can leverage the results for the abstract model with
      bounded nonpreemptive segments to establish a response-time
      bound for the more concrete model of fully nonpreemptive
      scheduling. *)
  Theorem uniprocessor_response_time_bound_fully_nonpreemptive_fp:
    response_time_bounded_by tsk R.
  Proof.
    move: (posnP (@task_cost _ H tsk)) => [ZERO|POS].
    { intros j ARR TSK.
      have ZEROj: job_cost j = 0.
      { move: (H_valid_job_cost j ARR) => NEQ.
        rewrite /valid_job_cost TSK ZERO in NEQ.
          by apply/eqP; rewrite -leqn0.
      }
        by rewrite /job_response_time_bound /completed_by ZEROj.
    }
    eapply uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments with
        (L0 := L).
    all: eauto 2 with basic_facts. 
  Qed.

End RTAforFullyNonPreemptiveFPModelwithArrivalCurves.