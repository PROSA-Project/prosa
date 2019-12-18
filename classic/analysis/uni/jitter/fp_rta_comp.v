Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.jitter.job prosa.classic.model.arrival.jitter.arrival_sequence
               prosa.classic.model.arrival.jitter.task_arrival.
Require Import prosa.classic.model.schedule.uni.schedulability
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.jitter.schedule prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.analysis.uni.jitter.workload_bound_fp prosa.classic.analysis.uni.jitter.fp_rta_theory.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path ssrfun.

Module ResponseTimeIterationFP.

  Import JobWithJitter UniprocessorScheduleWithJitter TaskArrivalWithJitter
         SporadicTaskset WorkloadBoundFP Priority ResponseTime
         ResponseTime Schedulability Platform ResponseTimeAnalysisFP.

  (* In this section, we define the response-time analysis for
     jitter-aware uniprocessor FP scheduling. *)
  Section Analysis.
    
    Context {SporadicTask: eqType}.
    Variable task_cost: SporadicTask -> time.
    Variable task_period: SporadicTask -> time.
    Variable task_deadline: SporadicTask -> time.
    Variable task_jitter: SporadicTask -> time.

    (* In the algorithm, we consider pairs of tasks and computed response-time bounds. *)
    Let task_with_response_time := (SporadicTask * time)%type.
    
    (* Assume a fixed-priority policy. *)
    Variable higher_eq_priority: FP_policy SporadicTask.

    (* We begin by defining the fixed-point iteration for computing the
       response-time bound of each task. *)

    (* First, to ensure that the algorithm converges, we will run the iteration
       on each task for at most (task_deadline tsk - task_cost tsk + 1) steps,
       i.e., the worst-case time complexity of the procedure. *)
    Definition max_steps (tsk: SporadicTask) :=
      task_deadline tsk - task_cost tsk + 1.

    (* Next, based on the jitter-aware workload bound for uniprocessor FP scheduling, ... *)
    Let workload_bound :=
      total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority.

    (* ...we compute the response-time bound R of a single task as follows:

           R (step) =  task_cost tsk                          if step = 0,
                       workload_bound (ts, tsk, R (step-1))   otherwise.       *)
    Definition per_task_rta ts tsk :=
      iter_fixpoint (workload_bound ts tsk) (max_steps tsk) (task_cost tsk).

    (* Next, we validate the computed response-time bound by checking
       (a) if the iteration returned some value and
       (b) if the corresponding response-time bound plus the jitter of the task is no
           larger than its deadline.
       If the validation succeeds, we return the pair (tsk, R), without the task jitter. *)
    Let is_valid_bound tsk_R :=
      if tsk_R is (tsk, Some R) then
          if task_jitter tsk + R <= task_deadline tsk then
            Some (tsk, R)
          else None
      else None.

    (* At the end, the response-time bounds for the entire taskset is computed
       using the fixed-point iteration on each task.
       If each response-time bound is no larger than the corresponding deadline,
       we return the pairs of tasks and response-time bounds, else we return None. *)
    Definition fp_claimed_bounds ts: option (seq task_with_response_time) :=
      let possible_bounds := [seq (tsk, per_task_rta ts tsk) | tsk <- ts] in
        if all is_valid_bound possible_bounds then
          Some (pmap is_valid_bound possible_bounds)
        else None.
    
    (* The schedulability test simply checks if we got a list of
       response-time bounds (i.e., if the computation did not fail). *)
    Definition fp_schedulable (ts: seq SporadicTask) :=
      fp_claimed_bounds ts != None.

    (* In this section, we prove some properties about the computed
       list of response-time bounds. *)
    Section Lemmas.

      (* Let ts be any taskset to be analyzed. *)
      Variable ts: seq SporadicTask.

      (* Assume that the response-time analysis does not fail.*)
      Variable rt_bounds: seq task_with_response_time.
      Hypothesis H_analysis_succeeds:
        fp_claimed_bounds ts = Some rt_bounds.

      (* First, we prove that a response-time bound exists for each task. *)
      Section BoundExists.
        
        (* Let tsk be any task in ts. *)
        Variable tsk: SporadicTask.
        Hypothesis H_tsk_in_ts: tsk \in ts.

        (* Since the analysis succeeded, there must be a corresponding
           response-time bound R for this task. *)
        Lemma fp_claimed_bounds_for_every_task:
          exists R, (tsk, R) \in rt_bounds.
        Proof.
          rename H_analysis_succeeds into SOME.
          move: SOME; rewrite /fp_claimed_bounds.
          case ALL: all; [case => SOME | by done].
          move: ALL => /allP ALL.
          have IN: (tsk, per_task_rta ts tsk) \in
                   [seq (tsk, per_task_rta ts tsk) | tsk <- ts];
            first by apply/mapP; exists tsk.
          specialize (ALL _ IN); move: ALL.
          rewrite /is_valid_bound; case RTA: per_task_rta => [R|] //.
          case DL: (_ <= _); last by done.
          move => _; exists R; rewrite -SOME.
          rewrite mem_pmap; apply/mapP.
          exists (tsk, Some R); first by rewrite -RTA.
          by rewrite /is_valid_bound DL.
        Qed.

      End BoundExists.
      
      (* Next, assuming that a bound exists, we prove some of its properties. *)
      Section PropertiesOfBound.

        (* Let tsk and R be any pair of task and response-time bound
           returned by the analysis. *)
        Variable tsk: SporadicTask.
        Variable R: time.
        Hypothesis H_tsk_R_computed: (tsk, R) \in rt_bounds.

        (* First, we show that tsk comes from task set ts. *)
        Lemma fp_claimed_bounds_from_taskset:
          tsk \in ts.
        Proof.
          rename H_analysis_succeeds into SOME, H_tsk_R_computed into IN.
          move: SOME; rewrite /fp_claimed_bounds.
          case: all; [case => SOME | by done].
          move: IN; rewrite -SOME mem_pmap.
          move => /mapP [[tsk' someR]].
          rewrite /is_valid_bound; case: someR; last by done.
          move => R'; case: (_ <= _); last by done.
          move => IN; case => EQ1 EQ2; subst.
          move: IN => /mapP [tsk'' IN].
          by case; move => EQ1; subst tsk'.
        Qed.

        (* Then, we prove that R is computed using the per-task fixed-point iteration, ... *)
        Lemma fp_claimed_bounds_computes_iteration:
          per_task_rta ts tsk = Some R.
        Proof.
          rename H_analysis_succeeds into SOME, H_tsk_R_computed into IN.
          move: SOME; rewrite /fp_claimed_bounds.
          case: all; [case => SOME | by done].
          move: IN; rewrite -SOME mem_pmap.
          move => /mapP [[tsk' someR]].
          rewrite /is_valid_bound; case: someR; last by done.
          move => R'; case: (_ <= _); last by done.
          move => IN; case => EQ1 EQ2; subst.
          move: IN => /mapP [tsk'' IN]; case => EQ1; subst; move => <-.
          by f_equal; rewrite addKn.
        Qed. 

        (* ...which implies that the computed bound is a fixed point
           of the response-time recurrence. *)
        Lemma fp_claimed_bounds_yields_fixed_point :
          R = workload_bound ts tsk R.
        Proof.
          have ITER := fp_claimed_bounds_computes_iteration.
          rewrite /per_task_rta in ITER.
          set f := workload_bound _ _ in ITER.
          set s := max_steps _ in ITER.
          set x0 := _ tsk in ITER.
          destruct (iter_fixpoint_cases f s x0) as [NONE | [R' [SOME EQ]]];
            first by rewrite NONE in ITER.
          by rewrite SOME in ITER; case: ITER => SAME; subst.
        Qed.

        (* Since the analysis validates the computed values, it follows that
           the jitter of the task plus R is no larger than its deadline. *)
        Lemma fp_claimed_bounds_le_deadline:
          task_jitter tsk + R <= task_deadline tsk.
        Proof.
          rename H_analysis_succeeds into SOME, H_tsk_R_computed into IN.
          move: SOME; rewrite /fp_claimed_bounds.
          case: all; [case => SOME | by done].
          move: IN; rewrite -SOME mem_pmap.
          move => /mapP [[tsk' someR]].
          rewrite /is_valid_bound; case: someR; last by done.
          move => R'; case LE: (_ <= _); last by done.
          by move => IN; case => EQ1 EQ2; subst.
        Qed.

        (* Using the monotonicity of the workload bound, we prove some properties
           of the results of the iteration. *)
        Section FixedPoint.

          (* Assume that the priority relation is reflexive. *)
          Hypothesis H_priority_is_reflexive:
            FP_is_reflexive higher_eq_priority.

          (* Assume that tasks have positive costs and periods. *)
          Hypothesis H_cost_positive: task_cost tsk > 0.
          Hypothesis H_period_positive:
            forall tsk, tsk \in ts -> task_period tsk > 0.

          (* Then, we can show that the computed response-time bound is as large
             as the cost of the task, ... *)
          Lemma fp_claimed_bounds_ge_cost:
            R >= task_cost tsk.
          Proof.
            have ITER := fp_claimed_bounds_computes_iteration.
            rewrite /per_task_rta in ITER.
            set f := workload_bound _ _ in ITER.
            set s := max_steps _ in ITER.
            set x0 := _ tsk in ITER.
            have REFL: reflexive leq by rewrite /reflexive; apply leqnn.
            have TRANS: transitive leq by rewrite /transitive;apply leq_trans.
            have MON: monotone f leq.
              by intros x1 x2 LE; apply total_workload_bound_fp_non_decreasing.
            have GE: task_cost tsk <= f (task_cost tsk).
            {
              apply total_workload_bound_fp_ge_cost; try (by done).
              - by apply fp_claimed_bounds_from_taskset.
              - by apply H_period_positive, fp_claimed_bounds_from_taskset.
            }
            by apply (iter_fixpoint_ge_bottom f leq REFL TRANS MON s x0 _ ITER GE).
          Qed.

          (* ...which implies that the response-time bound is positive. *)
          Corollary fp_claimed_bounds_gt_zero: R > 0.
          Proof.
            apply leq_trans with (n := task_cost tsk); first by done.
            by apply fp_claimed_bounds_ge_cost.
          Qed.

        End FixedPoint.

      End PropertiesOfBound.
      
    End Lemmas.
    
  End Analysis.

  (* In this section, using the main theorem from fp_rta_theory.v, we prove
     the correctness of the jitter-aware response-time analysis. *)
  Section ProvingCorrectness.

    Context {SporadicTask: eqType}.
    Variable task_cost: SporadicTask -> time.
    Variable task_period: SporadicTask -> time.
    Variable task_deadline: SporadicTask -> time.
    Variable task_jitter: SporadicTask -> time.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> SporadicTask.
    
    (* Consider a task set ts... *)
    Variable ts: seq SporadicTask.

    (* ...with positive task costs and periods. *)
    Hypothesis H_positive_costs: forall tsk, tsk \in ts -> task_cost tsk > 0.
    Hypothesis H_positive_periods: forall tsk, tsk \in ts -> task_period tsk > 0.

    (* Next, consider any job arrival sequence with consistent, duplicate-free arrivals, ... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.

   (* ...where all jobs come from task set ts, ...*)
    Hypothesis H_all_jobs_from_taskset:
      forall j,
        arrives_in arr_seq j ->
        job_task j \in ts.
 
    (* ... and satisfy the sporadic task model.*)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.

    (* Assume that the cost of each job is bounded by the cost of its task,... *)
    Hypothesis H_job_cost_le_task_cost:
      forall j,
        arrives_in arr_seq j ->
        job_cost j <= task_cost (job_task j).

    (* ...the jitter of each job is bounded by the jitter of its task,... *)
    Hypothesis H_job_jitter_le_task_jitter:
      forall j,
        arrives_in arr_seq j ->
        job_jitter j <= task_jitter (job_task j).

    (* ...and that job deadlines equal task deadlines. *)
    Hypothesis H_job_deadline_eq_task_deadline:
      forall j,
        arrives_in arr_seq j ->
        job_deadline j = task_deadline (job_task j).
    
    (* Assume any fixed-priority policy... *)
    Variable higher_eq_priority: FP_policy SporadicTask.
    
    (* ...that is reflexive and transitive, i.e., indicating higher-or-equal priority. *)
    Hypothesis H_priority_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_transitive: FP_is_transitive higher_eq_priority.

    (* Next, consider any jitter-aware uniprocessor schedule of these jobs... *)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.

    (* ...where jobs do not execute before the jitter has passed nor after completion. *)
    Hypothesis H_jobs_execute_after_jitter: jobs_execute_after_jitter job_arrival job_jitter sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Also assume that the scheduler is jitter-aware work-conserving and respects the FP policy. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost job_jitter arr_seq sched.
    Hypothesis H_respects_FP_policy:
      respects_FP_policy job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority.

    (* For simplicity, let's define some local names. *)
    Let no_deadline_missed_by_task :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.
    Let no_deadline_missed_by_job :=
      job_misses_no_deadline job_arrival job_cost job_deadline sched.
    Let response_time_bounded_by:=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.

    (* Recall the response-time analysis and the corresponding schedulability test. *)
    Let RTA_claimed_bounds :=
      fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts.
    Let claimed_to_be_schedulable :=
      fp_schedulable task_cost task_period task_deadline task_jitter higher_eq_priority ts.

    (* First, we prove that the RTA yields valid response-time bounds. *)
    Theorem fp_analysis_yields_response_time_bounds :
      forall tsk R,
        (tsk, R) \In RTA_claimed_bounds ->
        response_time_bounded_by tsk (task_jitter tsk + R).
    Proof.
      unfold valid_sporadic_job, valid_realtime_job,
             valid_sporadic_taskset, is_valid_sporadic_task in *.
      unfold RTA_claimed_bounds; intros tsk R.
      case SOME: fp_claimed_bounds => [rt_bounds|] IN; last by done.
      apply uniprocessor_response_time_bound_fp with
            (task_cost0 := task_cost) (task_period0 := task_period)
            (ts0 := ts) (job_jitter0 := job_jitter)
            (higher_eq_priority0 := higher_eq_priority); try (by done).
      {
        apply fp_claimed_bounds_gt_zero with (task_cost0 := task_cost)
          (task_period0 := task_period) (task_deadline0 := task_deadline)
          (higher_eq_priority0 := higher_eq_priority) (ts0 := ts) (task_jitter0 := task_jitter)
          (rt_bounds0 := rt_bounds) (tsk0 := tsk); try (by done).
        apply H_positive_costs.
        by eapply fp_claimed_bounds_from_taskset; eauto 1.
      }
      by apply fp_claimed_bounds_yields_fixed_point with
        (task_deadline0 := task_deadline) (rt_bounds0 := rt_bounds). 
    Qed.

    (* Next, we show that the RTA is a sufficient schedulability analysis. *)
    Section AnalysisIsSufficient.
      
      (* If the schedulability test suceeds, ...*)
      Hypothesis H_test_succeeds: claimed_to_be_schedulable.

      (* ...then no task misses its deadline. *)
      Theorem taskset_schedulable_by_fp_rta :
        forall tsk, tsk \in ts -> no_deadline_missed_by_task tsk.
      Proof.
        unfold claimed_to_be_schedulable, fp_schedulable in *.
        have RESP := fp_claimed_bounds_for_every_task task_cost task_period task_deadline
                                                      task_jitter higher_eq_priority ts.
        have DL := fp_claimed_bounds_le_deadline task_cost task_period task_deadline
                                                 task_jitter higher_eq_priority ts.
        have BOUND := fp_analysis_yields_response_time_bounds.
        rename H_test_succeeds into TEST.
        move:TEST; case TEST:(fp_claimed_bounds _ _ _ _ _) => [rt_bounds|] _//.
        intros tsk IN.
        move: (RESP rt_bounds TEST tsk IN) => [R INbounds].
        specialize (DL rt_bounds TEST tsk R INbounds).
        apply task_completes_before_deadline with
                (task_deadline0 := task_deadline) (R0 := task_jitter tsk + R); try (by done).
        by apply BOUND; rewrite /RTA_claimed_bounds TEST.
      Qed.

      (* Since all jobs of the arrival sequence are spawned by the task set,
         we also conclude that no job in the schedule misses its deadline. *)
      Theorem jobs_schedulable_by_fp_rta :
        forall j,
          arrives_in arr_seq j ->
          no_deadline_missed_by_job j.
      Proof.
        intros j ARRj.
        have SCHED := taskset_schedulable_by_fp_rta.
        unfold no_deadline_missed_by_task, task_misses_no_deadline in *.
        apply SCHED with (tsk := job_task j); try (by done).
        by apply H_all_jobs_from_taskset.
      Qed.

    End AnalysisIsSufficient.
    
  End ProvingCorrectness.
  
End ResponseTimeIterationFP.