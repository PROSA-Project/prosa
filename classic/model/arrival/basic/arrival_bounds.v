Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.arrival_sequence prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path div.

(* Properties of job arrival. *)
Module ArrivalBounds.

  Import ArrivalSequence SporadicTaskset TaskArrival Priority.
  
  Section Lemmas.

    Context {Task: eqType}.
    Variable task_period: Task -> time.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence with consistent, duplicate-free arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.    
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* In this section, we upper bound the number of jobs that can arrive in any interval. *)
    Section BoundOnSporadicArrivals.

      (* Assume that jobs are sporadic. *)
      Hypothesis H_sporadic_tasks: sporadic_task_model task_period job_arrival job_task arr_seq.
      
      (* Consider any time interval [t1, t2)... *)
      Variable t1 t2: time.

      (* ...and let tsk be any task with period > 0. *)
      Variable tsk: Task.
      Hypothesis H_period_gt_zero: task_period tsk > 0.

      (* Recall the jobs of tsk during [t1, t2), along with the number of arrivals. *)
      Let arriving_jobs := arrivals_of_task_between job_task arr_seq tsk t1 t2.
      Let num_arrivals := num_arrivals_of_task job_task arr_seq tsk t1 t2.
      
      (* We will establish an upper bound on the number of arriving jobs of tsk.
         The proof follows by case analysis. *)

      
      (* Case 1: Assume that no jobs of tsk arrive in the interval. *)
      Section NoJobs.

        (* If there are no arriving jobs in [t1, t2), ...*)
        Hypothesis H_no_jobs: num_arrivals = 0.

        (* ...then the arrival bound trivially holds. *)
        Lemma sporadic_arrival_bound_no_jobs:
          num_arrivals <= div_ceil (t2 - t1) (task_period tsk).
        Proof.
          by rewrite H_no_jobs.
        Qed.
        
      End NoJobs.

      (* Case 2: Assume that a single job of tsk arrives in the interval. *)
      Section OneJob.

        (* First, note that since the interval is open at time t2,
           t2 must be larger than t1. *)
        Lemma sporadic_arrival_bound_more_than_one_point:
          num_arrivals > 0 ->
          t1 < t2.
        Proof.
          unfold num_arrivals, num_arrivals_of_task in *; intros ONE.
          rewrite -/arriving_jobs in ONE *.
          destruct arriving_jobs as [| j l] eqn:EQ; first by done.
          have IN: j \in arriving_jobs by rewrite EQ in_cons eq_refl orTb.
          rewrite mem_filter in IN; move: IN => /andP [_ ARR].
          apply in_arrivals_implies_arrived_between with (job_arrival0 := job_arrival) in ARR;
            last by done.
          move: ARR => /andP [GE LT].
          by apply: (leq_ltn_trans GE).
        Qed.
        
        (* Therefore, if there is one job of tsk arriving during [t1, t2), ... *)
        Hypothesis H_no_jobs: num_arrivals = 1.

        (* ...then (t2 - t1) > 0 and the arrival bound also holds. *)
        Lemma sporadic_arrival_bound_one_job:
          num_arrivals <= div_ceil (t2 - t1) (task_period tsk).
        Proof.
          rewrite H_no_jobs.
          rewrite ceil_neq0 // ltn_subRL addn0.
          apply sporadic_arrival_bound_more_than_one_point.
          by rewrite H_no_jobs.
        Qed.
        
      End OneJob.

      (* Case 3: There are at least two arriving jobs. *)
      Section AtLeastTwoJobs.

        (* Assume that there are at least two jobs of tsk arriving in [t1,t2). *)
        Hypothesis H_at_least_two_jobs: num_arrivals >= 2.

        (* We prove the arrival bound by contradiction. *)
        Section DerivingContradiction.
          
          (* Suppose that the number of arrivals is larger than the bound. *)
          Hypothesis H_many_arrivals: div_ceil (t2 - t1) (task_period tsk) < num_arrivals.

          (* Consider the list of jobs ordered by arrival times. *)
          Let by_arrival_time j j' := job_arrival j <= job_arrival j'. 
          Let sorted_jobs := sort by_arrival_time arriving_jobs.

          (* Based on the notation for the n-th job in the sorted list of arrivals, ... *)
          Variable elem: Job.
          Let nth_job := nth elem sorted_jobs.

          (* ...we identify the first and last jobs and their respective arrival times. *)
          Let j_first := nth_job 0.
          Let j_last := nth_job (num_arrivals.-1).
          Let a_first := job_arrival j_first.
          Let a_last := job_arrival j_last.

          (* Recall from task_arrival.v the properties of the n-th job ...*)
          Corollary sporadic_arrival_bound_properties_of_nth:
            forall idx,
              idx < num_arrivals ->
              t1 <= job_arrival (nth_job idx) < t2 /\
              job_task (nth_job idx) = tsk /\
              arrives_in arr_seq (nth_job idx).
          Proof.
            intros idx LTidx.
            by apply sorted_arrivals_properties_of_nth.
          Qed.

          (* ...and the distance between the first and last jobs. *)
          Corollary sporadic_arrival_bound_distance_between_first_and_last:
            a_last >= a_first + (num_arrivals-1) * task_period tsk.
          Proof.
            apply sorted_arrivals_distance_between_first_and_last; try (by done).
            by apply leq_ltn_trans with (n := 1).
          Qed.

          (* Because the number of arrivals is larger than the ceiling term,
             it follows that the first and last jobs are separated by at
             least the length of the interval, ... *)
          Lemma sporadic_arrival_bound_last_job_too_far:
            a_first + t2 - t1 <= a_last.
          Proof.
            have DIST := sporadic_arrival_bound_distance_between_first_and_last.
            have MORE := sporadic_arrival_bound_more_than_one_point.
            rename H_many_arrivals into MANY, H_at_least_two_jobs into TWO.
            destruct num_arrivals; first by rewrite ltn0 in TWO.
            destruct n; first by rewrite ltnn in TWO.
            rewrite subn1 /= in DIST.
            apply leq_trans with (n := a_first + n.+1*task_period tsk); last by done.
            rewrite -addnBA; last by apply ltnW, MORE.
            rewrite leq_add2l.
            {
              unfold div_ceil in MANY.
                destruct (task_period tsk %| t2 - t1) eqn:DIV;
                  first by rewrite ltnS leq_divLR in MANY.
                by rewrite ltnS ltn_divLR // in MANY; apply ltnW.
            }
          Qed.
          
          (* ...which implies that the last job arrives after the interval. *)
          Lemma sporadic_arrival_bound_last_arrives_too_late:
            a_last >= t2.
          Proof.
            have NTH := sporadic_arrival_bound_properties_of_nth.
            have TOOFAR := sporadic_arrival_bound_last_job_too_far.            
            apply leq_trans with (n := a_first + t2 - t1); last by done.
            apply leq_trans with (n := t1 + t2 - t1); first by rewrite addKn.
            rewrite leq_sub2r // leq_add2r.
            by feed (NTH 0); [ by apply leq_ltn_trans with (n := 1) | des].
          Qed.

          (* However, the last job must lie within [t1, t2). Contradiction! *)
          Lemma sporadic_arrival_bound_case_3_contradiction: False.
          Proof.
            have LATE := sporadic_arrival_bound_last_arrives_too_late.
            have NTH := sporadic_arrival_bound_properties_of_nth.
            rename H_at_least_two_jobs into TWO.
            feed (NTH num_arrivals.-1); first by destruct num_arrivals; first by rewrite ltn0 in TWO.
            move: NTH => [/andP [_ BUG] _].
            by rewrite ltnNge LATE in BUG.
          Qed.            
          
        End DerivingContradiction.

        (* From the contradiction above, we prove that the arrival bound
           is correct for case 3 (i.e., at least two arriving jobs). *)
        Lemma sporadic_task_arrival_bound_at_least_two_jobs:
          num_arrivals <= div_ceil (t2 - t1) (task_period tsk).
        Proof.
          have CONTRA := sporadic_arrival_bound_case_3_contradiction.
          unfold num_arrivals, num_arrivals_of_task in *.
          rename H_at_least_two_jobs into TWO.
          set l := arrivals_of_task_between job_task arr_seq tsk t1 t2; fold l in TWO.
          apply contraT; rewrite -ltnNge; intro MANY; exfalso.
          have DUMMY: exists (j: Job), True.
          {
            destruct l eqn:EQ; first by rewrite /= ltn0 in TWO.
            by exists s.
          } destruct DUMMY as [elem _].
          by apply CONTRA; last by apply elem.
        Qed.
        
      End AtLeastTwoJobs.
      
      (* Using the case analysis, we prove that the number of job arrivals of tsk
         can be upper-bounded using the length of the interval as follows. *)
      Theorem sporadic_task_arrival_bound:
        num_arrivals <= div_ceil (t2 - t1) (task_period tsk).
      Proof.
        destruct num_arrivals as [|n] eqn:CEIL;
          first by rewrite -CEIL; apply sporadic_arrival_bound_no_jobs.
        destruct n as [|num_arr]; rewrite -CEIL; first by apply sporadic_arrival_bound_one_job.
        by apply sporadic_task_arrival_bound_at_least_two_jobs; rewrite CEIL.
      Qed.

    End BoundOnSporadicArrivals.
    
  End Lemmas.
  
End ArrivalBounds.