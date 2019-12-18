Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.jitter.job
               prosa.classic.model.arrival.jitter.task_arrival
               prosa.classic.model.arrival.jitter.arrival_bounds.
Require Import prosa.classic.model.schedule.uni.workload.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

(* In this file, we define the workload bound for jitter-aware FP scheduling. *)
Module WorkloadBoundFP.

  Import JobWithJitter SporadicTaskset UniprocessorScheduleWithJitter Priority Workload
         TaskArrivalWithJitter ArrivalBounds.

  (* First, we define a bound for the workload of a single task. *)
  Section SingleTask.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_period: Task -> time.
    Variable task_jitter: Task -> time.

    (* Consider any task tsk to be scheduled in a given interval of length delta. *)
    Variable tsk: Task.
    Variable delta: time.
    
    (* Based on the maximum number of jobs of tsk that can execute in the interval, ... *)
    Definition max_jobs := div_ceil (delta + task_jitter tsk) (task_period tsk).

    (* ... we define the following workload bound for the task. *)
    Definition task_workload_bound_FP := max_jobs * task_cost tsk. 

  End SingleTask.

  (* In this section, we define a bound for the workload all tasks with
     higher or equal priority. *)
  Section AllTasks.
    
    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_period: Task -> time.
    Variable task_jitter: Task -> time.

    (* Assume any FP policy. *)
    Variable higher_eq_priority: FP_policy Task.
    
    (* Consider a task set ts... *)
    Variable ts: list Task.
    
    (* ...and let tsk be the task to be analyzed. *)
    Variable tsk: Task.
    
    (* Let delta be the length of the interval of interest. *)
    Variable delta: time.

    (* Recall the definition of higher-or-equal-priority task and
       the per-task workload bound for FP scheduling (defined above). *)
    Let is_hep_task tsk_other := higher_eq_priority tsk_other tsk.
    Let W tsk_other :=
      task_workload_bound_FP task_cost task_period task_jitter tsk_other delta.

    (* Using the sum of individual workload bounds, we define the following bound
       for the total workload of tasks of higher-or-equal priority (with respect
       to tsk) in any interval of length delta. *)
    Definition total_workload_bound_fp :=
      \sum_(tsk_other <- ts | is_hep_task tsk_other) W tsk_other.
      
  End AllTasks.

  (* In this section, we prove some basic lemmas about the workload bound. *)
  Section BasicLemmas.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    Variable task_jitter: Task -> time.

    (* Assume any FP policy. *)
    Variable higher_eq_priority: FP_policy Task.
      
    (* Consider a task set ts... *)
    Variable ts: list Task.
    
    (* ...and let tsk be any task in ts. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Recall the workload bound for uniprocessor FP scheduling. *)
    Let workload_bound :=
      total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk.

    (* In this section we prove that the workload bound in a time window of
       length (task_cost tsk) is as large as (task_cost tsk) time units.
       (This is an important initial condition for the fixed-point iteration.) *)
    Section NoSmallerThanCost.

      (* Assume that the priority order is reflexive... *)
      Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.

      (* ...and that the cost and period of task tsk are positive. *)
      Hypothesis H_cost_positive: task_cost tsk > 0.
      Hypothesis H_period_positive: task_period tsk > 0.

      (* Then, we prove that the workload bound in an interval of length (task_cost tsk)
         cannot be smaller than (task_cost tsk). *)
      Lemma total_workload_bound_fp_ge_cost:
        workload_bound (task_cost tsk) >= task_cost tsk.
      Proof.
        rename H_priority_is_reflexive into REFL.
        unfold workload_bound, total_workload_bound_fp.
        rewrite big_mkcond (big_rem tsk) /=; last by done.
        rewrite REFL /task_workload_bound_FP.
        apply leq_trans with (n := max_jobs task_period task_jitter
                                            tsk (task_cost tsk) * task_cost tsk);
          last by apply leq_addr.
        rewrite -{1}[task_cost tsk]mul1n leq_mul2r; apply/orP; right.
        apply ceil_neq0; last by done.
        by apply leq_trans with (n := task_cost tsk); last by apply leq_addr.
      Qed.

    End NoSmallerThanCost.

    (* In this section, we prove that the workload bound is monotonically non-decreasing. *)
    Section NonDecreasing.

      (* Assume that the period of every task in the task set is positive. *)
      Hypothesis H_period_positive:
        forall tsk,
          tsk \in ts ->
          task_period tsk > 0.

      (* Then, the workload bound is a monotonically non-decreasing function.
         (This is an important property for the fixed-point iteration.) *)
      Lemma total_workload_bound_fp_non_decreasing:
        forall delta1 delta2,
          delta1 <= delta2 ->
          workload_bound delta1 <= workload_bound delta2.
      Proof.
        unfold workload_bound, total_workload_bound_fp; intros d1 d2 LE.
        apply leq_sum_seq; intros tsk' IN HP.
        rewrite leq_mul2r; apply/orP; right.
        by apply leq_divceil2r; [by apply H_period_positive | by rewrite leq_add2r].
      Qed.
      
    End NonDecreasing.

  End BasicLemmas.
  
  (* In this section, we prove that any fixed point R = workload_bound R
     is indeed a workload bound for any interval of length R. *)
  Section ProofWorkloadBound.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_period: Task -> time.
    Variable task_jitter: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> Task.

    (* Let ts be any task set... *)
    Variable ts: seq Task.

    (* ...with positive task periods. *)
    Hypothesis H_positive_periods:
      forall tsk, tsk \in ts -> task_period tsk > 0.
    
    (* Consider any job arrival sequence with consistent, duplicate-free arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.    
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* First, let's define some local names for clarity. *)
    Let actual_arrivals := actual_arrivals_between job_arrival job_jitter arr_seq.

    (* Next, assume that all jobs come from the task set, ...*)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* ...the cost of each job is bounded by the cost of its task, ... *)
    Hypothesis H_job_cost_le_task_cost:
      forall j,
        arrives_in arr_seq j ->
        job_cost j <= task_cost (job_task j).

    (* ...and the jitter of each job is bounded by the jitter of its task. *)
    Hypothesis H_job_jitter_le_task_jitter:
      forall j,
        arrives_in arr_seq j ->
        job_jitter j <= task_jitter (job_task j).

    (* Assume that jobs arrived sporadically. *)
    Hypothesis H_sporadic_arrivals:
      sporadic_task_model task_period job_arrival job_task arr_seq.

    (* Then, let tsk be any task in ts. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* For a given fixed-priority policy, ... *)
    Variable higher_eq_priority: FP_policy Task.
    
    (* ...we recall the definitions of higher-or-equal-priority workload and the workload bound. *)
    Let actual_hp_workload t1 t2 :=
      workload_of_higher_or_equal_priority_tasks job_cost job_task (actual_arrivals t1 t2)
                                                 higher_eq_priority tsk.
    Let workload_bound :=
      total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk.

    (* Next, consider any R that is a fixed point of the following equation,
       i.e., the claimed workload bound is equal to the interval length. *)
    Variable R: time.
    Hypothesis H_fixed_point: R = workload_bound R.

    (* Then, we prove that R bounds the workload of jobs of higher-or-equal-priority tasks
       with actual arrival time (including jitter) in [t, t + R). *)
    Lemma fp_workload_bound_holds:
      forall t,
        actual_hp_workload t (t + R) <= R.
    Proof.
      rename H_fixed_point into FIX, H_all_jobs_from_taskset into FROMTS,
             H_arrival_times_are_consistent into CONS, H_arrival_sequence_is_a_set into SET.
      unfold actual_hp_workload, workload_of_higher_or_equal_priority_tasks,
             valid_sporadic_job_with_jitter, valid_sporadic_job, valid_realtime_job,
             valid_sporadic_taskset, is_valid_sporadic_task in *.
      have BOUND := sporadic_task_with_jitter_arrival_bound task_period task_jitter job_arrival
                    job_jitter job_task arr_seq CONS SET.
      feed_n 2 BOUND; (try by done).
      intro t.
      rewrite {2}FIX /workload_bound /total_workload_bound_fp.
      set l := actual_arrivals_between job_arrival job_jitter arr_seq t (t + R).
      set hep := higher_eq_priority.
      apply leq_trans with (n := \sum_(tsk' <- ts | hep tsk' tsk)
                                  (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
      {
        have EXCHANGE := exchange_big_dep (fun x => hep (job_task x) tsk).
        rewrite EXCHANGE /=; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
        rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
        apply leq_sum; move => j0 /andP [IN0 HP0].
        rewrite big_mkcond (big_rem (job_task j0)) /=;
          first by rewrite HP0 andTb eq_refl; apply leq_addr.
        rewrite mem_filter in IN0; move: IN0 => /andP [_ ARR0].
        by apply in_arrivals_implies_arrived in ARR0; apply FROMTS.
      }
      apply leq_sum_seq; intros tsk0 IN0 HP0.
      apply leq_trans with (n := num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq
                                                             tsk0 t (t + R) * task_cost tsk0).
      {
        rewrite /num_actual_arrivals_of_task -sum1_size big_distrl /= big_filter.
        apply leq_sum_seq; move => j1 IN1 /eqP EQ.
        rewrite -EQ mul1n; apply H_job_cost_le_task_cost.
        rewrite mem_filter in IN1; move: IN1 => /andP [_ ARR1].
        by apply in_arrivals_implies_arrived in ARR1.
      }
      rewrite /task_workload_bound_FP leq_mul2r; apply/orP; right.
      feed (BOUND t (t + R) tsk0); first by apply H_positive_periods.
      by rewrite -addnA addKn in BOUND.
    Qed.

  End ProofWorkloadBound.
  
End WorkloadBoundFP.