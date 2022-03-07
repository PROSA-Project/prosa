Require Export prosa.analysis.facts.periodic.arrival_times.
Require Export prosa.analysis.definitions.infinite_jobs.

(** In this file we prove some properties concerning the size 
 of task arrivals in context of the periodic model. *)
Section TaskArrivalsSize.

  (** Consider any type of periodic tasks with an offset ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  Context `{PeriodicModel Task}.
  
  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  
  (** Consider any unique arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
  Hypothesis H_uniq_arr_seq: arrival_sequence_uniq arr_seq.

  (** ... and any periodic task [tsk] with a valid offset and period. *)
  Variable tsk : Task.
  Hypothesis H_valid_offset: valid_offset arr_seq tsk.
  Hypothesis H_valid_period: valid_period tsk.
  Hypothesis H_task_respects_periodic_model: respects_periodic_task_model arr_seq tsk.

  (** We show that if an instant [t] is not an "arrival time" for 
      task [tsk] then [task_arrivals_at arr_seq tsk t] is an empty sequence. *)
  Lemma task_arrivals_size_at_non_arrival:
    forall t,
      (forall n, t <> task_offset tsk + n * task_period tsk) ->
      task_arrivals_at arr_seq tsk t = [::].
  Proof.
    intros * T.
    have EMPT_OR_EXISTS : forall xs, xs = [::] \/ exists a, a \in xs.
    { intros *.
      induction xs; first by left.
      right; exists a.
      now apply mem_head.
    }
    destruct (EMPT_OR_EXISTS Job (task_arrivals_at arr_seq tsk t)) as [EMPT | [a A_IN]] => //.
    rewrite /task_arrivals_at mem_filter in A_IN; move : A_IN => /andP [/eqP TSK A_ARR].
    move : (A_ARR) => A_IN; apply H_consistent_arrivals in A_IN.
    rewrite -A_IN in T; rewrite /arrivals_at in A_ARR.
    apply in_arrseq_implies_arrives in A_ARR.
    have EXISTS_N : exists n, job_arrival a = task_offset tsk + n * task_period tsk.
      exact: (job_arrival_times arr_seq).
    move : EXISTS_N => [n A_ARRIVAL].
    now move : (T n) => T1.
  Qed.
  
  (** We show that at any instant [t], at most one job of task [tsk] 
      can arrive (i.e. size of [task_arrivals_at arr_seq tsk t] is at most one). *)
  Lemma task_arrivals_at_size_cases: 
    forall t,
      size (task_arrivals_at arr_seq tsk t) = 0 \/
      size (task_arrivals_at arr_seq tsk t) = 1.
  Proof.
    intro t.
    case: (ltngtP (size (task_arrivals_at arr_seq tsk t)) 1) => [LT|GT|EQ]; try by auto.
    destruct (size (task_arrivals_at arr_seq tsk t)); now left.
    specialize (exists_two (task_arrivals_at arr_seq tsk t)) => EXISTS_TWO.
    destruct EXISTS_TWO as [a [b [NEQ [A_IN B_IN]]]]; [by done | by apply filter_uniq | ].
    rewrite mem_filter in A_IN; rewrite mem_filter in B_IN.
    move: A_IN B_IN => /andP [/eqP TSKA ARRA] /andP [/eqP TSKB ARRB].
    move: (ARRA); move: (ARRB); rewrite /arrivals_at => A_IN B_IN.
    apply in_arrseq_implies_arrives in A_IN; apply in_arrseq_implies_arrives in B_IN.
    have SPO : respects_sporadic_task_model arr_seq tsk; try by rt_auto.
    have EQ_ARR_A : (job_arrival a = t) by apply H_consistent_arrivals.
    have EQ_ARR_B : (job_arrival b = t) by apply H_consistent_arrivals.
    specialize (SPO a b); feed_n 6 SPO => //; try by lia.
    rewrite EQ_ARR_A EQ_ARR_B in SPO.
    rewrite /task_min_inter_arrival_time /periodic_as_sporadic in SPO.
    have POS : task_period tsk > 0 by auto.
    now lia.
  Qed.

  (** We show that the size of task arrivals (strictly) between two consecutive arrival
      times is zero. *)
  Lemma size_task_arrivals_between_eq0:
    forall n,
      let l := (task_offset tsk + n * task_period tsk).+1 in
      let r := (task_offset tsk + n.+1 * task_period tsk) in 
      size (task_arrivals_between arr_seq tsk l r) = 0.
  Proof.
    intros n l r; rewrite /l /r.
    rewrite size_of_task_arrivals_between big_nat_eq0 => //; intros t INEQ.
    rewrite task_arrivals_size_at_non_arrival => //; intros n1 EQ.
    rewrite EQ in INEQ.
    move : INEQ => /andP [INEQ1 INEQ2].
    rewrite ltn_add2l ltn_mul2r in INEQ1; rewrite ltn_add2l ltn_mul2r in INEQ2.
    move : INEQ1 INEQ2 => /andP [A B] /andP [C D].
    now lia.
  Qed.
  
  (** In this section we show some properties of task arrivals in case
      of an infinite sequence of jobs. *) 
  Section TaskArrivalsInCaseOfInfiniteJobs.
    
    (** Assume that we have an infinite sequence of jobs. *)
    Hypothesis H_infinite_jobs: infinite_jobs arr_seq. 
    
    (** We show that for any number [n], there exists a job [j] of task [tsk] 
        such that [job_index] of [j] is equal to [n] and [j] arrives
        at [task_offset tsk + n * task_period tsk]. *)
    Lemma jobs_exists_later:
      forall n,
      exists j,
        arrives_in arr_seq j /\
        job_task j = tsk /\
        job_arrival j = task_offset tsk + n * task_period tsk /\
        job_index arr_seq j = n.
    Proof.
      intros *.
      destruct (H_infinite_jobs tsk n) as [j [ARR [TSK IND]]].
      exists j; repeat split => //.
      exact: (periodic_arrival_times arr_seq).
    Qed.
    
    (** We show that the size of task arrivals at any arrival time is equal to one. *)
    Lemma task_arrivals_at_size:
      forall n,
        let l := (task_offset tsk + n * task_period tsk) in
        size (task_arrivals_at arr_seq tsk l) = 1.
    Proof.
      intros n l; rewrite /l.
      move : (jobs_exists_later n) => [j' [ARR [TSK [ARRIVAL IND]]]].
      apply (only_j_in_task_arrivals_at_j
               arr_seq H_consistent_arrivals H_uniq_arr_seq tsk) in ARR => //;
        last by rt_auto.
      rewrite /task_arrivals_at_job_arrival TSK in ARR.
      now rewrite -ARRIVAL ARR.
    Qed.
    
    (** We show that the size of task arrivals up to [task_offset tsk] is equal to one. *)
    Lemma size_task_arrivals_up_to_offset:
      size (task_arrivals_up_to arr_seq tsk (task_offset tsk)) = 1.
    Proof.
      rewrite /task_arrivals_up_to.
      specialize (task_arrivals_between_cat arr_seq tsk 0 (task_offset tsk) (task_offset tsk).+1) => CAT.
      feed_n 2 CAT => //; rewrite CAT size_cat.
      have Z : size (task_arrivals_between arr_seq tsk 0 (task_offset tsk)) = 0.
      { rewrite size_of_task_arrivals_between big_nat_eq0 => //; intros t T_EQ.
        rewrite task_arrivals_size_at_non_arrival => //; intros n EQ.
        now lia.
      }               
      rewrite Z add0n /task_arrivals_between /arrivals_between big_nat1.
      specialize (task_arrivals_at_size 0) => AT_SIZE.
      now rewrite mul0n addn0 in AT_SIZE.
    Qed.
    
    (** We show that for any number [n], the number of jobs released by task [tsk] up to  
        [task_offset tsk + n * task_period tsk] is equal to [n + 1]. *)
    Lemma task_arrivals_up_to_size:
      forall n,
        let l := (task_offset tsk + n * task_period tsk) in
        let r := (task_offset tsk + n.+1 * task_period tsk) in
        size (task_arrivals_up_to arr_seq tsk l) = n + 1.
    Proof.
      induction n.
      intros l r; rewrite /l mul0n add0n addn0.
      now apply size_task_arrivals_up_to_offset.
      intros l r.
      specialize (task_arrivals_cat arr_seq tsk (task_offset tsk + n * task_period tsk)
                                    (task_offset tsk + n.+1 * task_period tsk)) => CAT.
      feed_n 1 CAT; first by lia.
      rewrite CAT size_cat IHn.
      specialize (task_arrivals_between_cat arr_seq tsk (task_offset tsk + n * task_period tsk).+1
                 (task_offset tsk + n.+1 * task_period tsk) (task_offset tsk + n.+1 * task_period tsk).+1) => S_CAT.
      feed_n 2 S_CAT; try by lia.
      { rewrite ltn_add2l ltn_mul2r.
        now apply /andP; split => //.
      }
      rewrite S_CAT size_cat /task_arrivals_between /arrivals_between big_nat1.
      rewrite size_task_arrivals_between_eq0 task_arrivals_at_size => //.
      now lia.
    Qed.
    
    (** We show that the number of jobs released by task [tsk] at any instant [t] 
        and [t + n * task_period tsk] is the same for any number [n]. *)
    Lemma eq_size_of_task_arrivals_seperated_by_period:
      forall n t,
        t >= task_offset tsk ->
        size (task_arrivals_at arr_seq tsk t) =
        size (task_arrivals_at arr_seq tsk (t + n * task_period tsk)).
    Proof.
      intros * T_G.
      destruct (exists_or_not_add_mul_cases (task_offset tsk) (task_period tsk) t) as [[n1 JB_ARR] | JB_NOT_ARR].
      + have EXISTS_N : exists nn, t + n * task_period tsk = task_offset tsk + nn * task_period tsk.
        { exists (n1 + n).
          now rewrite JB_ARR; lia.
        }
        move : EXISTS_N => [nn JB_ARR'].
        now rewrite JB_ARR' JB_ARR !task_arrivals_at_size => //.
      + have FORALL_N : forall nn, t + n * task_period tsk <> task_offset tsk + nn * task_period tsk by apply mul_add_neq.
        now rewrite !task_arrivals_size_at_non_arrival.
    Qed.
    
  End TaskArrivalsInCaseOfInfiniteJobs.
  
End TaskArrivalsSize.
