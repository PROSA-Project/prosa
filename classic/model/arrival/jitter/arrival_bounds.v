Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.jitter.job
               prosa.classic.model.arrival.jitter.arrival_sequence
               prosa.classic.model.arrival.jitter.task_arrival.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path div.

(* In this file, we prove bounds on the number of actual task arrivals, i.e,
   taking release jitter into account. *)
Module ArrivalBounds.

  Import JobWithJitter ArrivalSequenceWithJitter SporadicTaskset Priority
         TaskArrivalWithJitter.
  
  Section BoundingActualArrivals.

    Context {Task: eqType}.
    Variable task_period: Task -> time.
    Variable task_jitter: Task -> time.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence with consistent, duplicate-free arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.    
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* ...where the jitter of each job is bounded by the jitter of its task. *)
    Hypothesis H_job_jitter_bounded:
      forall j,
        arrives_in arr_seq j ->
        job_jitter_leq_task_jitter task_jitter job_jitter job_task j.
    
    (* For simplicity, let's define some local names. *)
    Let actual_job_arrival := actual_arrival job_arrival job_jitter.

    (* In this section, we prove an upper bound on the number of jobs with actual arrival time
       in a given interval. *)
    Section UpperBoundOn.

      (* Assume that jobs are sporadic. *)
      Hypothesis H_sporadic_tasks: sporadic_task_model task_period job_arrival job_task arr_seq.
      
      (* Consider any time interval [t1, t2)... *)
      Variable t1 t2: time.

      (* ...and let tsk be any task with period > 0. *)
      Variable tsk: Task.
      Hypothesis H_period_gt_zero: task_period tsk > 0.

      (* Recall the jobs of tsk with actual arrival time in [t1, t2), along with the corresponding
         number of arrivals. *)
      Let actual_arrivals := actual_arrivals_of_task_between job_arrival job_jitter
                                                             job_task arr_seq tsk t1 t2.
      Let num_actual_arrivals := num_actual_arrivals_of_task job_arrival job_jitter job_task
                                                             arr_seq tsk t1 t2.
      
      (* We will establish an upper bound on the number of actual arrivals of tsk.
         The proof follows by case analysis. *)
      
      (* Case 1: Assume that there are no jobs of tsk with actual arrival time in the interval. *)
      Section NoJobs.

        (* If there are no actual arrivals in [t1, t2), ...*)
        Hypothesis H_no_jobs: num_actual_arrivals = 0.

        (* ...then the arrival bound trivially holds. *)
        Lemma sporadic_arrival_bound_no_jobs:
          num_actual_arrivals <= div_ceil (t2 + task_jitter tsk - t1) (task_period tsk).
        Proof.
          by rewrite H_no_jobs.
        Qed.
        
      End NoJobs.

      (* Case 2: Assume that a single job of tsk has actual arrival time in the interval. *)
      Section OneJob.

        (* First, note that since the interval is open at time t2,
           t2 must be larger than t1. *)
        Lemma sporadic_arrival_bound_more_than_one_point:
          num_actual_arrivals > 0 ->
          t1 < t2.
        Proof.
          unfold num_actual_arrivals, num_actual_arrivals_of_task in *; intros ONE.
          rewrite -/actual_arrivals in ONE *.
          destruct actual_arrivals as [| j l] eqn:EQ; first by done.
          have IN: j \in actual_arrivals by rewrite EQ in_cons eq_refl orTb.
          rewrite mem_filter in IN; move: IN => /andP [_ ARR].
          rewrite mem_filter in ARR; move: ARR => /andP [GE ARR].
          by move: GE => /andP [GE LE]; apply: (leq_ltn_trans GE).
        Qed.
        
        (* Therefore, if there is one job of tsk with actual arrival time in [t1, t2), ... *)
        Hypothesis H_no_jobs: num_actual_arrivals = 1.

        (* ...then (t2 - t1) > 0 and the arrival bound also holds. *)
        Lemma sporadic_arrival_bound_one_job:
          num_actual_arrivals <= div_ceil (t2 + task_jitter tsk - t1) (task_period tsk).
        Proof.
          rewrite H_no_jobs.
          rewrite ceil_neq0 // ltn_subRL addn0.
          apply leq_trans with (n := t2); last by apply leq_addr.
          apply sporadic_arrival_bound_more_than_one_point.
          by rewrite H_no_jobs.
        Qed.
        
      End OneJob.

      (* Case 3: There are at least two actual job arrivals. *)
      Section AtLeastTwoJobs.

        (* Assume that there are at least two jobs of tsk with actual arrival in [t1,t2). *)
        Hypothesis H_at_least_two_jobs: num_actual_arrivals >= 2.

        (* We prove the arrival bound by contradiction. *)
        Section DerivingContradiction.
          
          (* Suppose that the number of arrivals is larger than the bound. *)
          Hypothesis H_many_arrivals:
            div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) < num_actual_arrivals.

          (* Consider the list of jobs ordered by arrival times. *)
          Let by_arrival_time j j' := job_arrival j <= job_arrival j'. 
          Let sorted_jobs := sort by_arrival_time actual_arrivals.

          (* Based on the notation for the n-th job in the sorted list of arrivals, ... *)
          Variable elem: Job.
          Let nth_job := nth elem sorted_jobs.

          (* ...we identify the first and last jobs and their respective arrival times. *)
          Let j_first := nth_job 0.
          Let j_last := nth_job (num_actual_arrivals.-1).
          Let a_first := job_arrival j_first.
          Let a_last := job_arrival j_last.

          (* Next, we recall from task_arrival.v the properties of the n-th job in
             the sequence... *)
          Corollary sporadic_arrival_bound_properties_of_nth:
            forall idx,
              idx < num_actual_arrivals ->
              t1 <= actual_job_arrival (nth_job idx) < t2 /\
              job_task (nth_job idx) = tsk /\
              arrives_in arr_seq (nth_job idx).
          Proof.
            by intros idx LTidx; apply sorted_arrivals_properties_of_nth.
          Qed.

          (* ...and that the first and last jobs are separated by at least
             (num_actual_arrivals - 1) periods. *)
          Corollary sporadic_arrival_bound_distance_between_first_and_last:
            a_last >= a_first + (num_actual_arrivals - 1) * task_period tsk.
          Proof.
            rename H_at_least_two_jobs into TWO.
            apply sorted_arrivals_distance_between_first_and_last; try (by done).
            by apply leq_ltn_trans with (n := 1).
          Qed.

          (* Next, because the number of actual arrivals is larger than the ceiling term,
             it follows that the first and last jobs are separated by at least the
             length of the interval plus the jitter of the task, ... *)
          Lemma sporadic_arrival_bound_last_job_too_far:
            a_first + t2 + task_jitter tsk - t1 <= a_last.
          Proof.
            have DIST := sporadic_arrival_bound_distance_between_first_and_last.
            have MORE := sporadic_arrival_bound_more_than_one_point.
            rename H_many_arrivals into MANY, H_at_least_two_jobs into TWO.
            destruct num_actual_arrivals; first by rewrite ltn0 in TWO.
            destruct n; first by rewrite ltnn in TWO.
            rewrite subn1 /= in DIST.
            apply leq_trans with (n := a_first + n.+1*task_period tsk); last by done.
            rewrite -addnA -addnBA;
              last by apply leq_trans with (n := t2); [by apply ltnW, MORE | by apply leq_addr].
            rewrite leq_add2l.
            unfold div_ceil in MANY.
            destruct (task_period tsk %| t2 + task_jitter tsk - t1) eqn:DIV;
              first by rewrite ltnS leq_divLR in MANY.
            by rewrite ltnS ltn_divLR // in MANY; apply ltnW.
          Qed.
          
          (* ...which implies that the last job arrives after the interval. *)
          Lemma sporadic_arrival_bound_last_arrives_too_late:
            a_last >= t2.
          Proof.
            have NTH := sporadic_arrival_bound_properties_of_nth.
            have TOOFAR := sporadic_arrival_bound_last_job_too_far.            
            apply leq_trans with (n := a_first + t2 + task_jitter tsk - t1); last by done.
            apply leq_trans with (n := t1 + t2 - t1); first by rewrite addKn.
            rewrite leq_sub2r // -addnA [t2 + _]addnC addnA leq_add2r.
            feed (NTH 0); [ by apply leq_ltn_trans with (n := 1) | des].
            apply leq_trans with (n := a_first + job_jitter j_first); first by done.
            by rewrite leq_add2l -NTH0; apply H_job_jitter_bounded.
          Qed.

          (* However, the actual arrival time of the last job must lie within [t1, t2).
             Contradiction! *)
          Lemma sporadic_arrival_bound_case_3_contradiction: False.
          Proof.
            have LATE := sporadic_arrival_bound_last_arrives_too_late.
            have NTH := sporadic_arrival_bound_properties_of_nth.
            rename H_at_least_two_jobs into TWO.
            feed (NTH num_actual_arrivals.-1);
              first by destruct num_actual_arrivals; first by rewrite ltn0 in TWO.
            move: NTH => [/andP [_ BUG] _].
            rewrite ltnNge in BUG; move: BUG => /negP BUG; apply: BUG.
            by apply leq_trans with (n := a_last); last by apply leq_addr.
          Qed.
          
        End DerivingContradiction.

        (* From the contradiction above, we prove that the arrival bound
           is correct for case 3 (i.e., at least two actual arrivals). *)
        Lemma sporadic_task_arrival_bound_at_least_two_jobs:
          num_actual_arrivals <= div_ceil (t2 + task_jitter tsk - t1) (task_period tsk).
        Proof.
          have CONTRA := sporadic_arrival_bound_case_3_contradiction.
          unfold num_actual_arrivals, num_actual_arrivals_of_task in *.
          rename H_at_least_two_jobs into TWO.
          set l := actual_arrivals_of_task_between _ _ _ _ _ _; fold l in TWO.
          apply contraT; rewrite -ltnNge; intro MANY; exfalso.
          have DUMMY: exists (j: Job), True.
          {
            destruct l eqn:EQ; first by rewrite /= ltn0 in TWO.
            by exists s.
          } destruct DUMMY as [elem _].
          by apply CONTRA; last by apply elem.
        Qed.
        
      End AtLeastTwoJobs.
      
      (* Using the case analysis above, we prove that the number of actual arrivals of tsk
         can be upper-bounded using the length of the interval as follows. *)
      Theorem sporadic_task_with_jitter_arrival_bound:
        num_actual_arrivals <= div_ceil (t2 + task_jitter tsk - t1) (task_period tsk).
      Proof.
        destruct num_actual_arrivals as [|n] eqn:CEIL;
          first by rewrite -CEIL; apply sporadic_arrival_bound_no_jobs.
        destruct n as [|num_arr]; rewrite -CEIL; first by apply sporadic_arrival_bound_one_job.
        by apply sporadic_task_arrival_bound_at_least_two_jobs; rewrite CEIL.
      Qed.

    End UpperBoundOn.

  End BoundingActualArrivals.

End ArrivalBounds.