Require Import prosa.model.readiness.basic.
Require Export prosa.results.edf.rta.bounded_nps.
Require Export prosa.analysis.facts.preemption.task.nonpreemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.model.task.preemption.fully_nonpreemptive.
Require Import prosa.model.priority.edf.

(** * RTA for Fully Non-Preemptive EDF *)
(** In this module we prove the RTA theorem for the fully non-preemptive EDF model. *)

(** ** Setup and Assumptions *)

Section RTAforFullyNonPreemptiveEDFModelwithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** We assume that jobs and tasks are fully nonpreemptive. *)
  #[local] Existing Instance fully_nonpreemptive_job_model.
  #[local] Existing Instance fully_nonpreemptive_task_model.
  #[local] Existing Instance fully_nonpreemptive_rtc_threshold.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Consider an arbitrary task set ts, ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from this task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and the cost of a job cannot be larger than the task cost. *)
  Hypothesis H_valid_job_cost :
    arrivals_have_valid_job_costs arr_seq.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
     any task [tsk] in ts [max_arrival tsk] is (1) an arrival bound of
     [tsk], and (2) it is a monotonic function that equals 0 for the
     empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Next, consider any valid ideal non-preemptive uniprocessor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule sched.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and the schedule respects the scheduling policy. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).

  (** ** Total Workload and Length of Busy Interval *)

  (** We introduce the abbreviation [rbf] for the task request bound function,
      which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a task T. *)
  Let rbf := task_request_bound_function.

  (** Next, we introduce [task_rbf] as an abbreviation
      for the task request bound function of task [tsk]. *)
  Let task_rbf := rbf tsk.

  (** Using the sum of individual request bound functions, we define the request bound
     function of all tasks (total request bound function). *)
  Let total_rbf := total_request_bound_function ts.

  (** We also define a bound for the priority inversion caused by jobs with lower priority. *)
  Let blocking_bound A :=
    \max_(tsk_o <- ts | (blocking_relevant tsk_o)
                         && (task_deadline tsk_o > task_deadline tsk + A))
     (task_cost tsk_o - ε).

  (** Let L be any positive fixed point of the busy interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_rbf L.

  (** ** Response-Time Bound *)

  (** To reduce the time complexity of the analysis, recall the notion of search space. *)
  Let is_in_search_space := bounded_nps.is_in_search_space ts tsk L.

  (** Consider any value [R], and assume that for any given arrival
      offset [A] in the search space, there is a solution of the
      response-time bound recurrence which is bounded by [R]. *)
  Variable R : nat.
  Hypothesis H_R_is_maximum :
    forall A,
      is_in_search_space A ->
      exists F,
        A + F >= blocking_bound A + (task_rbf (A + ε) - (task_cost tsk - ε))
                + bound_on_athep_workload ts tsk A (A + F)
        /\ R >= F + (task_cost tsk - ε).

  (** Now, we can leverage the results for the abstract model with bounded nonpreemptive segments
      to establish a response-time bound for the more concrete model of fully nonpreemptive scheduling. *)

  Theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    case: (posnP (task_cost tsk)) => [ZERO|POS].
    { intros j ARR TSK.
      have ZEROj: job_cost j = 0.
      { move: (H_valid_job_cost j ARR) => NEQ.
        rewrite /valid_job_cost in NEQ.
        move: TSK => /eqP -> in NEQ.
        rewrite ZERO in NEQ.
        by apply/eqP; rewrite -leqn0.
      }
      by rewrite /job_response_time_bound /completed_by ZEROj.
    }
    by eapply uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments with (L := L).
  Qed.

End RTAforFullyNonPreemptiveEDFModelwithArrivalCurves.
