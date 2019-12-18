Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.jitter.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path.

(* In this file, we provide definitions and lemmas about task arrivals
   in jitter-aware schedules. *)
Module TaskArrivalWithJitter.

  Import ArrivalSequenceWithJitter SporadicTaskset.
  Export TaskArrival.

  (* First, we identify the arrivals of a particular task. *)
  Section NumberOfArrivals.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence ...*)
    Variable arr_seq: arrival_sequence Job.

    (* ...and recall the list of jobs with actual arrival time in a given interval. *)
    Let arrivals_between := actual_arrivals_between job_arrival job_jitter arr_seq.

    (* Next, let tsk be any task. *)
    Variable tsk: Task.

    (* By checking the jobs spawned by tsk... *)
    Definition is_job_of_tsk := is_job_of_task job_task tsk.

    (* ...we identify the jobs of tsk that arrived in any interval [t1, t2) ... *)
    Definition actual_arrivals_of_task_between (t1 t2: time) :=
      [seq j <- arrivals_between t1 t2 | is_job_of_tsk j].
  
    (* ...and also count the number of such job arrivals. *)
    Definition num_actual_arrivals_of_task (t1 t2: time) :=
      size (actual_arrivals_of_task_between t1 t2).

  End NumberOfArrivals.

  (* Next, we prove properties about lists of actual arrivals
     that are sorted by arrival time. *)
  Section DistanceBetweenSporadicJobs.

    Context {Task: eqType}.
    Variable task_period: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any arrival sequence with consistent, duplicate-free arrivals, ... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_consistent_arrivals: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_no_duplicate_arrivals: arrival_sequence_is_a_set arr_seq.

    (* ...where jobs are sporadic. *)
    Hypothesis H_sporadic_jobs:
      sporadic_task_model task_period job_arrival job_task arr_seq.

    (* For simplicity, let's define some local names. *)
    Let actual_job_arrival := actual_arrival job_arrival job_jitter.
    
    (* Next, let tsk be any task to be scheduled. *)
    Variable tsk: Task.

    (* Consider any time interval [t1, t2)... *)
    Variable t1 t2: time.

    (* ...and the associated actual arrivals of task tsk. *)
    Let arriving_jobs := actual_arrivals_of_task_between job_arrival job_jitter
                                                         job_task arr_seq tsk t1 t2.
    Let num_arrivals := num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2.

    (* Then, consider the sequence of such jobs ordered by arrival times... *)
    Let by_arrival_time j j' := job_arrival j <= job_arrival j'. 
    Let sorted_jobs := sort by_arrival_time arriving_jobs.

    (* ...and let (nth_job i) denote the i-th job in the sorted sequence. *)
    Variable elem: Job.
    Let nth_job := nth elem sorted_jobs.

    (* First, we recall some trivial properties about nth_job. *)
    Remark sorted_arrivals_properties_of_nth:
      forall idx,
        idx < num_arrivals ->
        t1 <= actual_job_arrival (nth_job idx) < t2 /\
        job_task (nth_job idx) = tsk /\
        arrives_in arr_seq (nth_job idx).
    Proof.
      intros idx LTidx.
      have IN: nth_job idx \in sorted_jobs by rewrite mem_nth // size_sort.
      rewrite mem_sort mem_filter in IN.
      move: IN => /andP [JOB IN]; move: (IN) => LT.
      apply in_actual_arrivals_between_implies_arrived in IN.
      eapply in_actual_arrivals_implies_arrived_between in LT.
      by repeat split; try (by done); apply/eqP.
    Qed.

    (* Next, we conclude that consecutive jobs are different. *)
    Lemma sorted_arrivals_current_differs_from_next:
      forall idx,
        idx < num_arrivals.-1 ->
        nth_job idx <> nth_job idx.+1.
    Proof.
      intros idx LT; apply/eqP.
      destruct num_arrivals eqn:EQ; first by rewrite ltn0 in LT.
      destruct n; [by rewrite ltn0 in LT | simpl in LT].
      rewrite nth_uniq ?size_sort /arriving_jobs
              -/(num_actual_arrivals_of_task _ _ _ _ _ _ _) -/num_arrivals;
        first by rewrite neq_ltn ltnSn orTb.
      - by apply leq_trans with (n := n.+1); last by rewrite EQ. 
      - by rewrite EQ ltnS.
      - by rewrite sort_uniq filter_uniq //; apply actual_arrivals_uniq; eauto 1.
    Qed.

    (* Since the list is sorted, we prove that each job arrives at
       least (task_period tsk) time units after the previous job. *)
    Lemma sorted_arrivals_separated_by_period:
      forall idx,
        idx < num_arrivals.-1 ->
        job_arrival (nth_job idx.+1) >= job_arrival (nth_job idx) + task_period tsk.
    Proof.
      have NTH := sorted_arrivals_properties_of_nth.
      have NEQ := sorted_arrivals_current_differs_from_next.
      rename H_sporadic_jobs into SPO.
      intros idx LT.
      destruct num_arrivals eqn:EQ; first by rewrite ltn0 in LT.
      destruct n; [by rewrite ltn0 in LT | simpl in LT].
      exploit (NTH idx);
        [by apply leq_trans with (n := n.+1) | intro NTH1].
      exploit (NTH idx.+1); [by rewrite ltnS | intro NTH2].
      move: NTH1 NTH2 => [_ [JOB1 ARR1]] [_ [JOB2 ARR2]].
      rewrite -JOB1.
      apply SPO; try (by done); [by apply NEQ | by rewrite JOB1 JOB2 |].
      suff ORDERED: by_arrival_time (nth_job idx) (nth_job idx.+1) by done.
      apply sort_ordered;
        first by apply sort_sorted; intros x y; apply leq_total. 
      rewrite size_sort.
      rewrite /arriving_jobs -/(num_actual_arrivals_of_task _ _ _ _ _ _ _) -/num_arrivals.
      by rewrite EQ.
    Qed.

    (* If the list of arrivals is not empty, we analyze the distance between
       the first and last jobs. *)
    Section FirstAndLastJobs.

      (* Suppose that there is at least one job, ... *)
      Hypothesis H_at_least_one_job:
        num_arrivals >= 1.
      
      (* ...in which case we identify the first and last jobs and their
         respective arrival times (note that they could be the same job). *)
      Let j_first := nth_job 0.
      Let j_last := nth_job (num_arrivals.-1).
      Let a_first := job_arrival j_first.
      Let a_last := job_arrival j_last.
      
      (* By induction, we prove that that each job with index 'idx' arrives at
         least idx*(task_period tsk) units after the first job. *)
      Lemma sorted_arrivals_distance_from_first_job:
        forall idx,
          idx < num_arrivals ->
          job_arrival (nth_job idx) >= a_first + idx * task_period tsk.
      Proof.
        have SEP := sorted_arrivals_separated_by_period.
        unfold sporadic_task_model in *.
        rename H_sporadic_jobs into SPO.
        induction idx; first by intros _; rewrite mul0n addn0.
        intros LT.
        have LT': idx < num_arrivals by apply leq_ltn_trans with (n := idx.+1).
        specialize (IHidx LT'). 
        apply leq_trans with (n := job_arrival (nth_job idx) + task_period tsk);
          first by rewrite mulSn [task_period _ + _]addnC addnA leq_add2r.
        apply SEP.
        by rewrite -(ltn_add2r 1) 2!addn1 (ltn_predK LT).
      Qed.

      (* Therefore, the first and last jobs are separated by at least
         (num_arrivals - 1) periods. *)
      Corollary sorted_arrivals_distance_between_first_and_last:
        a_last >= a_first + (num_arrivals-1) * task_period tsk.
      Proof.
        rename H_at_least_one_job into TWO.
        have DIST := sorted_arrivals_distance_from_first_job.
        rewrite subn1; apply DIST.
        by destruct num_arrivals; first by rewrite ltn0 in TWO.
      Qed.

    End FirstAndLastJobs.

  End DistanceBetweenSporadicJobs.
  
End TaskArrivalWithJitter.