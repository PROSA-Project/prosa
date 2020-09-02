Require Export prosa.analysis.definitions.hyperperiod.
Require Export prosa.analysis.facts.periodic.task_arrivals_size.
Require Export prosa.util.div_mod.

(** In this file we prove some simple properties of hyperperiods of periodic tasks. *)
Section Hyperperiod.

  (** Consider any type of periodic tasks, ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... any task set [ts], ... *)
  Variable ts : TaskSet Task.

  (** ... and any task [tsk] that belongs to this task set. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts: tsk \in ts.

  (** A task set's hyperperiod is an integral multiple
      of each task's period in the task set. **)
  Lemma hyperperiod_int_mult_of_any_task: 
    exists (k : nat),
      hyperperiod ts = k * task_period tsk.
  Proof.
    apply lcm_seq_is_mult_of_all_ints.
    apply map_f.
    now apply H_tsk_in_ts.
  Qed.

End Hyperperiod.

(** In this section we show a property of hyperperiod in context 
   of task sets with valid periods. *)
Section ValidPeriodsImplyPositiveHP.

  (** Consider any type of periodic tasks ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... and any task set [ts] ... *)
  Variable ts : TaskSet Task.

  (** ... such that all tasks in [ts] have valid periods. *)
  Hypothesis H_valid_periods: valid_periods ts.

  (** We show that the hyperperiod of task set [ts] 
   is positive. *)
  Lemma valid_periods_imply_pos_hp:
    hyperperiod ts > 0.
  Proof.
    apply all_pos_implies_lcml_pos.
    move => b /mapP [x IN EQ]; subst b.
    now apply H_valid_periods.
  Qed.
  
End ValidPeriodsImplyPositiveHP.

(** In this section we prove some lemmas about the hyperperiod
    in context of the periodic model. *)
Section PeriodicLemmas.

  (** Consider any type of tasks, ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  Context `{PeriodicModel Task}.

  (** ... any type of jobs, ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  
  (** ... and a consistent arrival sequence with non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
  Hypothesis H_uniq_arr_seq: arrival_sequence_uniq arr_seq.
  
  (** Consider a task set [ts] such that all tasks in
      [ts] have valid periods. *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods: valid_periods ts.

  (** Let [tsk] be any periodic task in [ts] with a valid offset and period. *)
  Variable tsk : Task.
  Hypothesis H_task_in_ts: tsk \in ts.
  Hypothesis H_valid_offset: valid_offset arr_seq tsk.
  Hypothesis H_valid_period: valid_period tsk.
  Hypothesis H_periodic_task: respects_periodic_task_model arr_seq tsk.

  (** Assume we have an infinite sequence of jobs in the arrival sequence. *)
  Hypothesis H_infinite_jobs: infinite_jobs arr_seq.
  
  (** Let [O_max] denote the maximum task offset in [ts] and let
   [HP] denote the hyperperiod of all tasks in [ts]. *)
  Let O_max := max_task_offset ts.
  Let HP := hyperperiod ts.

  (** We show that the job corresponding to any job [j1] in any other
      hyperperiod is of the same task as [j1]. *)
  Lemma corresponding_jobs_have_same_task:
    forall j1 j2,
      job_task (corresponding_job_in_hyperperiod ts arr_seq j1
               (starting_instant_of_corresponding_hyperperiod ts j2) (job_task j1)) = job_task j1.
  Proof.
    intros *.
    set ARRIVALS := (task_arrivals_between arr_seq (job_task j1) (starting_instant_of_hyperperiod ts (job_arrival j2))
          (starting_instant_of_hyperperiod ts (job_arrival j2) + HP)).
    set IND := (job_index_in_hyperperiod ts arr_seq j1 (starting_instant_of_hyperperiod ts (job_arrival j1)) (job_task j1)).
    have SIZE_G : size ARRIVALS <= IND -> job_task (nth j1 ARRIVALS IND) = job_task j1 by intro SG; rewrite nth_default.
    case: (boolP (size ARRIVALS == IND)) => [/eqP EQ|NEQ]; first by apply SIZE_G; ssrlia.
    move : NEQ; rewrite neq_ltn; move => /orP [LT | G]; first by apply SIZE_G; ssrlia.
    set jb := nth j1 ARRIVALS IND.
    have JOB_IN : jb \in ARRIVALS by apply mem_nth.
    rewrite /ARRIVALS /task_arrivals_between mem_filter in JOB_IN.
    now move : JOB_IN => /andP [/eqP TSK JB_IN].
  Qed.    

  (** We show that if a job [j] lies in the hyperperiod starting
   at instant [t] then [j] arrives in the interval <<[t, t + HP)>>. *)
  Lemma all_jobs_arrive_within_hyperperiod:
    forall j t,
      j \in jobs_in_hyperperiod ts arr_seq t tsk->
      t <= job_arrival j < t + HP.
  Proof.
    intros * JB_IN_HP.
    rewrite mem_filter in JB_IN_HP.
    move : JB_IN_HP => /andP [/eqP TSK JB_IN]; apply mem_bigcat_nat_exists in JB_IN.
    destruct JB_IN as [i [JB_IN INEQ]]; apply H_consistent_arrivals in JB_IN.
    now rewrite JB_IN.
  Qed.
  
  (** We show that the number of jobs in a hyperperiod starting at [n1 * HP + O_max] 
   is the same as the number of jobs in a hyperperiod starting at [n2 * HP + O_max] given 
   that [n1] is less than or equal to [n2]. *)
  Lemma eq_size_hyp_lt:
    forall n1 n2,
      n1 <= n2 ->
      size (jobs_in_hyperperiod ts arr_seq (n1 * HP + O_max) tsk) =
      size (jobs_in_hyperperiod ts arr_seq (n2 * HP + O_max) tsk).
  Proof.
    intros * N1_LT.
    specialize (add_mul_diff n1 n2 HP O_max) => AD; feed_n 1 AD => //.
    rewrite AD.
    destruct (hyperperiod_int_mult_of_any_task ts tsk H_task_in_ts) as [k HYP]; rewrite !/HP.
    rewrite [in X in _ = size (_ (n1 * HP + O_max + _ * X) tsk)]HYP.
    rewrite mulnA /HP /jobs_in_hyperperiod !size_of_task_arrivals_between.
    erewrite big_sum_eq_in_eq_sized_intervals => //; intros g G_LT.
    have OFF_G : task_offset tsk <= O_max by apply max_offset_g.
    have FG : forall v b n, v + b + n = v + n + b by intros *; ssrlia.
    erewrite eq_size_of_task_arrivals_seperated_by_period => //; last by ssrlia.
    now rewrite FG.
  Qed.

  (** We generalize the above lemma by lifting the condition on 
   [n1] and [n2]. *)
  Lemma eq_size_of_arrivals_in_hyperperiod:
    forall n1 n2,
      size (jobs_in_hyperperiod ts arr_seq (n1 * HP + O_max) tsk) =
      size (jobs_in_hyperperiod ts arr_seq (n2 * HP + O_max) tsk).
  Proof.
    intros *.
    case : (boolP (n1 == n2)) => [/eqP EQ | NEQ]; first by rewrite EQ.
    move : NEQ; rewrite neq_ltn; move => /orP [LT | LT].
    + now apply eq_size_hyp_lt => //; ssrlia.
    + move : (eq_size_hyp_lt n2 n1) => EQ_S.
      now feed_n 1 EQ_S => //; ssrlia.
  Qed.

  (** Consider any two jobs [j1] and [j2] that stem from the arrival sequence
   [arr_seq] such that [j1] is of task [tsk]. *)
  Variable j1 : Job.
  Variable j2 : Job.
  Hypothesis H_j1_from_arr_seq: arrives_in arr_seq j1.
  Hypothesis H_j2_from_arr_seq: arrives_in arr_seq j2.
  Hypothesis H_j1_task: job_task j1 = tsk.

  (** Assume that both [j1] and [j2] arrive after [O_max]. *)
  Hypothesis H_j1_arr_after_O_max: O_max <= job_arrival j1.
  Hypothesis H_j2_arr_after_O_max: O_max <= job_arrival j2.

  (** We show that any job [j] that arrives in task arrivals in the same 
      hyperperiod as [j2] also arrives in task arrivals up to [job_arrival j2 + HP]. *)
  Lemma job_in_hp_arrives_in_task_arrivals_up_to:
    forall j,
      j \in jobs_in_hyperperiod ts arr_seq ((job_arrival j2 - O_max) %/ HP * HP + O_max) tsk ->
      j \in task_arrivals_up_to arr_seq tsk (job_arrival j2 + HP).
  Proof.
    intros j J_IN.
    rewrite /task_arrivals_up_to.
    set jobs_in_hp := (jobs_in_hyperperiod ts arr_seq ((job_arrival j2 - O_max) %/ HP * HP + O_max) tsk).
    move : (J_IN) => J_ARR; apply all_jobs_arrive_within_hyperperiod in J_IN.
    rewrite /jobs_in_hp /jobs_in_hyperperiod /task_arrivals_up_to /task_arrivals_between mem_filter in J_ARR.
    move : J_ARR =>  /andP [/eqP TSK' NTH_IN].
    apply job_in_task_arrivals_between => //; first by apply in_arrivals_implies_arrived in NTH_IN.
    apply mem_bigcat_nat_exists in NTH_IN.
    move : NTH_IN => [i [NJ_IN INEQ]]; apply H_consistent_arrivals in NJ_IN; rewrite -NJ_IN in INEQ.
    apply /andP; split => //.
    rewrite ltnS.
    apply leq_trans with (n := (job_arrival j2 - O_max) %/ HP * HP + O_max + HP); first by ssrlia.
    rewrite leq_add2r.
    have O_M : (job_arrival j2 - O_max) %/ HP * HP <= job_arrival j2 - O_max by apply leq_trunc_div.
    have ARR_G : job_arrival j2 >= O_max by auto.
    now ssrlia.
  Qed.

  (** We show that job [j1] arrives in its own hyperperiod. *)
  Lemma job_in_own_hp:
    j1 \in jobs_in_hyperperiod ts arr_seq ((job_arrival j1 - O_max) %/ HP * HP + O_max) tsk.
  Proof.
    apply job_in_task_arrivals_between => //.
    apply /andP; split.
    + rewrite addnC -leq_subRL => //.
      now apply leq_trunc_div.
    + specialize (div_floor_add_g (job_arrival j1 - O_max) HP) => AB.
      feed_n 1 AB; first by apply valid_periods_imply_pos_hp => //.
      apply ltn_subLR in AB.
      now rewrite -/(HP); ssrlia.
  Qed.

  (** We show that the [corresponding_job_in_hyperperiod] of [j1] in [j2]'s hyperperiod
   arrives in task arrivals up to [job_arrival j2 + HP]. *)
  Lemma corr_job_in_task_arrivals_up_to:
    corresponding_job_in_hyperperiod ts arr_seq j1 (starting_instant_of_corresponding_hyperperiod ts j2) tsk \in
      task_arrivals_up_to arr_seq tsk (job_arrival j2 + HP).
  Proof.
    rewrite /corresponding_job_in_hyperperiod /starting_instant_of_corresponding_hyperperiod.
    rewrite /job_index_in_hyperperiod /starting_instant_of_hyperperiod /hyperperiod_index.
    set ind := (index j1 (jobs_in_hyperperiod ts arr_seq ((job_arrival j1 - O_max) %/ HP * HP + O_max) tsk)).
    set jobs_in_hp := (jobs_in_hyperperiod ts arr_seq ((job_arrival j2 - O_max) %/ HP * HP + O_max) tsk).
    set nj := nth j1 jobs_in_hp ind.
    apply job_in_hp_arrives_in_task_arrivals_up_to => //.
    rewrite mem_nth /jobs_in_hp => //.
    specialize (eq_size_of_arrivals_in_hyperperiod ((job_arrival j2 - O_max) %/ HP) ((job_arrival j1 - O_max) %/ HP)) => EQ.
    rewrite EQ /ind index_mem.
    now apply job_in_own_hp.
  Qed.    

  (** Finally, we show that the [corresponding_job_in_hyperperiod] of [j1] in [j2]'s hyperperiod 
   arrives in the arrival sequence [arr_seq]. *)
  Lemma corresponding_job_arrives:
      arrives_in arr_seq (corresponding_job_in_hyperperiod ts arr_seq j1 (starting_instant_of_corresponding_hyperperiod ts j2) tsk).
  Proof.
    move : (corr_job_in_task_arrivals_up_to) => ARR_G.
    rewrite /task_arrivals_up_to /task_arrivals_between mem_filter in ARR_G.
    move : ARR_G =>  /andP [/eqP TSK' NTH_IN].
    now apply in_arrivals_implies_arrived in NTH_IN.
  Qed.

End PeriodicLemmas.
