Require Export prosa.analysis.definitions.hyperperiod.
Require Export prosa.analysis.facts.periodic.task_arrivals_size.
Require Export prosa.analysis.facts.sporadic.arrival_bound.
Require Export prosa.analysis.facts.model.workload.
Require Export prosa.analysis.facts.model.task_cost.
Require Export prosa.util.div_mod.
Require Export prosa.util.tactics.

(** In this file we prove some simple properties of hyperperiods of periodic tasks. *)
Section Hyperperiod.

  (** Consider any type of periodic tasks, ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... any task set [ts], ... *)
  Variable ts : TaskSet Task.

  (** ... and any task [tsk] that belongs to this task set. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** A task set's hyperperiod is an integral multiple
      of each task's period in the task set. **)
  Lemma hyperperiod_int_mult_of_any_task :
    exists (k : nat),
      hyperperiod ts = k * task_period tsk.
  Proof. by apply/dvdnP; apply lcm_seq_is_mult_of_all_ints, map_f, H_tsk_in_ts. Qed.

End Hyperperiod.

(** In this section we show a property of hyperperiod in context
    of task sets with valid periods. *)
Section ValidPeriodsImplyPositiveHP.

  (** Consider any type of periodic tasks ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... and any task set [ts] ... *)
  Variable ts : TaskSet Task.

  (** ... such that all tasks in [ts] have valid periods. *)
  Hypothesis H_valid_periods : valid_periods ts.

  (** We show that the hyperperiod of task set [ts]
      is positive. *)
  Lemma valid_periods_imply_pos_hp :
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
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Consider a task set [ts] such that all tasks in
      [ts] have valid periods. *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods : valid_periods ts.

  (** Let [tsk] be any periodic task in [ts] with a valid offset and period. *)
  Variable tsk : Task.
  Hypothesis H_task_in_ts : tsk \in ts.
  Hypothesis H_valid_offset : valid_offset arr_seq tsk.
  Hypothesis H_valid_period : valid_period tsk.
  Hypothesis H_periodic_task : respects_periodic_task_model arr_seq tsk.

  (** Each task in [ts] continues releasing jobs indefinitely. *)
  Hypothesis H_infinite_jobs : tasks_have_infinite_arrivals arr_seq ts.

  (** Let [O_max] denote the maximum task offset in [ts] and let
      [HP] denote the hyperperiod of all tasks in [ts]. *)
  Let O_max := max_task_offset ts.
  Let HP := hyperperiod ts.

  (** We show that the job corresponding to any job [j1] in any other
      hyperperiod is a job of the same task as [j1]. *)
  Lemma corresponding_jobs_have_same_task :
    forall j1 j2,
      job_task (corresponding_job_in_hyperperiod ts arr_seq j1
               (starting_instant_of_corresponding_hyperperiod ts j2) (job_task j1)) = job_task j1.
  Proof.
    clear H_task_in_ts H_valid_period.
    move=> j1 j2.
    set ARRIVALS := (task_arrivals_between arr_seq (job_task j1) (starting_instant_of_hyperperiod ts (job_arrival j2))
          (starting_instant_of_hyperperiod ts (job_arrival j2) + HP)).
    set IND := (job_index_in_hyperperiod ts arr_seq j1 (starting_instant_of_hyperperiod ts (job_arrival j1)) (job_task j1)).
    have SIZE_G : size ARRIVALS <= IND -> job_task (nth j1 ARRIVALS IND) = job_task j1 by intro SG; rewrite nth_default.
    case: (boolP (size ARRIVALS == IND)) => [/eqP EQ|NEQ]; first by apply SIZE_G; lia.
    move : NEQ; rewrite neq_ltn => /orP [LT | G]; first by apply SIZE_G; lia.
    set jb := nth j1 ARRIVALS IND.
    have JOB_IN : jb \in ARRIVALS by apply mem_nth.
    rewrite /ARRIVALS /task_arrivals_between mem_filter in JOB_IN.
    now move : JOB_IN => /andP [/eqP TSK JB_IN].
  Qed.

  (** We show that if a job [j] lies in the hyperperiod starting
   at instant [t] then [j] arrives in the interval <<[t, t + HP)>>. *)
  Lemma all_jobs_arrive_within_hyperperiod :
    forall j t,
      j \in jobs_in_hyperperiod ts arr_seq t tsk ->
      t <= job_arrival j < t + HP.
  Proof.
    intros * JB_IN_HP.
    rewrite mem_filter in JB_IN_HP.
    move : JB_IN_HP => /andP [/eqP TSK JB_IN]; apply mem_bigcat_nat_exists in JB_IN.
    destruct JB_IN as [i [JB_IN INEQ]].
    apply job_arrival_at in JB_IN => //.
    by rewrite JB_IN.
  Qed.

  (** We show that the number of jobs in a hyperperiod starting at [n1 * HP + O_max]
      is the same as the number of jobs in a hyperperiod starting at [n2 * HP + O_max] given
      that [n1] is less than or equal to [n2]. *)
  Lemma eq_size_hyp_lt :
    forall n1 n2,
      n1 <= n2 ->
      size (jobs_in_hyperperiod ts arr_seq (n1 * HP + O_max) tsk)
      = size (jobs_in_hyperperiod ts arr_seq (n2 * HP + O_max) tsk).
  Proof.
    move=> n1 n2 N1_LT.
    have -> : n2 * HP + O_max = n1 * HP + O_max + (n2 - n1) * HP.
    { by rewrite -[in LHS](subnKC N1_LT) mulnDl addnAC. }
    destruct (hyperperiod_int_mult_of_any_task ts tsk H_task_in_ts) as [k HYP]; rewrite !/HP.
    rewrite [in X in _ = size (_ (n1 * HP + O_max + _ * X) tsk)]HYP.
    rewrite mulnA /HP /jobs_in_hyperperiod !size_of_task_arrivals_between.
    erewrite big_sum_eq_in_eq_sized_intervals => //; intros g G_LT.
    have OFF_G : task_offset tsk <= O_max by apply max_offset_g.
    have FG : forall v b n, v + b + n = v + n + b by intros *; lia.
    erewrite eq_size_of_task_arrivals_seperated_by_period => //; last lia.
    by rewrite FG.
  Qed.

  (** We generalize the above lemma by lifting the condition on
      [n1] and [n2]. *)
  Lemma eq_size_of_arrivals_in_hyperperiod :
    forall n1 n2,
      size (jobs_in_hyperperiod ts arr_seq (n1 * HP + O_max) tsk)
      = size (jobs_in_hyperperiod ts arr_seq (n2 * HP + O_max) tsk).
  Proof.
    move=> n1 n2.
    case : (boolP (n1 == n2)) => [/eqP EQ | NEQ]; first by rewrite EQ.
    move : NEQ; rewrite neq_ltn => /orP [LT | LT].
    + by apply eq_size_hyp_lt => //; lia.
    + move : (eq_size_hyp_lt n2 n1) => EQ_S.
      by feed_n 1 EQ_S => //; lia.
  Qed.

  (** Consider any two jobs [j1] and [j2] that stem from the arrival sequence
      [arr_seq] such that [j1] is of task [tsk]. *)
  Variable j1 : Job.
  Variable j2 : Job.
  Hypothesis H_j1_from_arr_seq : arrives_in arr_seq j1.
  Hypothesis H_j2_from_arr_seq : arrives_in arr_seq j2.
  Hypothesis H_j1_task : job_task j1 = tsk.

  (** Assume that both [j1] and [j2] arrive after [O_max]. *)
  Hypothesis H_j1_arr_after_O_max : O_max <= job_arrival j1.
  Hypothesis H_j2_arr_after_O_max : O_max <= job_arrival j2.

  (** We show that any job [j] that arrives in task arrivals in the same
      hyperperiod as [j2] also arrives in task arrivals up to [job_arrival j2 + HP]. *)
  Lemma job_in_hp_arrives_in_task_arrivals_up_to :
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
    apply job_in_task_arrivals_between => //;
      first by apply in_arrivals_implies_arrived in NTH_IN.
    apply mem_bigcat_nat_exists in NTH_IN.
    apply /andP; split => //.
    rewrite ltnS.
    apply leq_trans with (n := (job_arrival j2 - O_max) %/ HP * HP + O_max + HP); first by lia.
    rewrite leq_add2r.
    have O_M : (job_arrival j2 - O_max) %/ HP * HP <= job_arrival j2 - O_max by apply leq_divM.
    have ARR_G : job_arrival j2 >= O_max by [].
    lia.
  Qed.

  (** We show that job [j1] arrives in its own hyperperiod. *)
  Lemma job_in_own_hp :
    j1 \in jobs_in_hyperperiod ts arr_seq ((job_arrival j1 - O_max) %/ HP * HP + O_max) tsk.
  Proof.
    apply job_in_task_arrivals_between => //.
    apply /andP; split.
    + rewrite addnC -leq_subRL => //.
      by apply leq_divM.
    + specialize (div_floor_add_g (job_arrival j1 - O_max) HP) => AB.
      feed_n 1 AB; first by apply valid_periods_imply_pos_hp => //.
      rewrite ltn_subLR // in AB.
      by rewrite -/(HP); lia.
  Qed.

  (** We show that the [corresponding_job_in_hyperperiod] of [j1] in [j2]'s hyperperiod
      arrives in task arrivals up to [job_arrival j2 + HP]. *)
  Lemma corr_job_in_task_arrivals_up_to :
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
    by apply job_in_own_hp.
  Qed.

  (** Finally, we show that the [corresponding_job_in_hyperperiod] of [j1] in [j2]'s hyperperiod
      arrives in the arrival sequence [arr_seq]. *)
  Lemma corresponding_job_arrives :
      arrives_in arr_seq (corresponding_job_in_hyperperiod ts arr_seq j1 (starting_instant_of_corresponding_hyperperiod ts j2) tsk).
  Proof.
    move : (corr_job_in_task_arrivals_up_to) => ARR_G.
    rewrite /task_arrivals_up_to /task_arrivals_between mem_filter in ARR_G.
    move : ARR_G =>  /andP [/eqP TSK' NTH_IN].
    by apply in_arrivals_implies_arrived in NTH_IN.
  Qed.

End PeriodicLemmas.

(** ** Jobs in Adjacent Hyperperiods *)

Section AdjacentHyperperiodJobs.

  (** Consider periodic tasks, their jobs, ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** ... and a valid arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Consider a given task set ... *)
  Variable ts : TaskSet Task.

  (** ... and any valid periodic task in this set. *)
  Variable tsk : Task.
  Hypothesis H_task_in_ts : tsk \in ts.
  Hypothesis H_valid_period : valid_period tsk.
  Hypothesis H_periodic_task : respects_periodic_task_model arr_seq tsk.

  (** Trivially, the hyperperiod can be expressed in terms of the task's period. *)
  Lemma hyperperiod_as_job_count :
    hyperperiod ts = jobs_per_hyperperiod ts tsk * task_period tsk.
  Proof.
    rewrite /jobs_per_hyperperiod.
    have [k ->] := hyperperiod_int_mult_of_any_task ts tsk H_task_in_ts.
    by rewrite mulnK.
  Qed.

  (** By definition, the task stays the same going forwards ...  *)
  Lemma next_hyperperiod_job_task :
    forall j,
      job_task (next_hyperperiod_job ts arr_seq j) = job_task j.
  Proof.
    move=> j; rewrite /next_hyperperiod_job/same_task.
    case HEAD: [seq _ <- _ | _] => [|j' js] //=.
    have: j' \in [seq x <- arr_seq (job_arrival j + hyperperiod ts) | same_task x j]
      by rewrite HEAD mem_head.
    by rewrite mem_filter => /andP [/eqP].
  Qed.

  (** ... and also backwards. *)
  Lemma prev_hyperperiod_job_task :
    forall j,
      job_task (prev_hyperperiod_job ts arr_seq j) = job_task j.
  Proof.
    move=> j; rewrite /prev_hyperperiod_job/same_task.
    case HEAD: [seq _ <- _ | _ ] => [|j' js] //=.
    have: j' \in [seq x <- arr_seq (job_arrival j - hyperperiod ts) | same_task x j]
      by rewrite HEAD  mem_head.
    by rewrite mem_filter => /andP [/eqP].
  Qed.


  (** The list of task-specific arrivals is a singleton list. *)
  Local Fact prev_next_hyperperiod_job_selection :
    forall j j' t,
      arrives_in arr_seq j' ->
      job_task j = tsk ->
      job_task j' = tsk ->
      job_arrival j' = t ->
      [seq j'' <- arr_seq t | same_task j'' j] = [::j'].
  Proof.
    move=> j j' t IN TSK  TSK' ARR.
    rewrite /same_task TSK.
    by apply: only_j_at_job_arrival_j.
  Qed.

  (** We can identify the next job based on its arrival time. *)
  Lemma next_hyperperiod_job_from_arrival :
    forall j j',
      arrives_in arr_seq j' ->
      job_task j = tsk ->
      job_task j' = tsk ->
      job_arrival j' = job_arrival j + hyperperiod ts ->
      next_hyperperiod_job ts arr_seq j = j'.
  Proof.
    move=> j j'  IN TSK TSK' ARR.
    by rewrite /next_hyperperiod_job (prev_next_hyperperiod_job_selection j j').
  Qed.

  (** We can also identify the previous job based on its arrival time. *)
  Lemma prev_hyperperiod_job_from_arrival :
    forall j j',
      arrives_in arr_seq j' ->
      job_task j = tsk ->
      job_task j' = tsk ->
      job_arrival j' = job_arrival j - hyperperiod ts ->
      prev_hyperperiod_job ts arr_seq j = j'.
  Proof.
    move=> j j' IN TSK TSK' ARR.
    by rewrite /prev_hyperperiod_job (prev_next_hyperperiod_job_selection j j').
  Qed.

  (** *** Forward Correspondence *)

  Section ForwardCorrespondence.

    (** Suppose [tsk] releases jobs indefinitely. *)
    Hypothesis H_infinite_jobs : infinite_jobs arr_seq tsk.

    (** Consider any job of the task under analysis. *)
    Variable j : Job.
    Hypothesis H_arrives : arrives_in arr_seq j.
    Hypothesis H_tsk : job_task j = tsk.

    (** We establish some basic facts about the "matching" job in the next
        hyperperiod in one go, which we then expose as individual facts. *)
    Local Fact next_hyperperiod_job_properties :
      let
        j' := next_hyperperiod_job ts arr_seq j
      in
      [/\ arrives_in arr_seq j'
       , job_task j' = tsk
       , job_arrival j' = job_arrival j + hyperperiod ts
       & job_index arr_seq j' = job_index arr_seq j + jobs_per_hyperperiod ts tsk].
    Proof.
      have [j' [IN' [TSK' IDX']]] :=
        H_infinite_jobs (job_index arr_seq j + jobs_per_hyperperiod ts tsk).
      have ARR' : job_arrival j' = job_arrival j + hyperperiod ts
        by rewrite hyperperiod_as_job_count; apply: periodic_job_index_separation.
      by rewrite (next_hyperperiod_job_from_arrival j j').
    Qed.

    (** The successor belongs to the arrival sequence, ... *)
    Fact next_hyperperiod_job_arrives :
      arrives_in arr_seq (next_hyperperiod_job ts arr_seq j).
    Proof. by have [] := next_hyperperiod_job_properties. Qed.

    (** ... has an arrival time exactly one hyperperiod apart, ...  *)
    Fact next_hyperperiod_job_arrival :
      job_arrival (next_hyperperiod_job ts arr_seq j)
      = job_arrival j + hyperperiod ts.
    Proof. by have [] := next_hyperperiod_job_properties. Qed.

    (** ... and the obvious job index. *)
    Fact next_hyperperiod_job_index :
      job_index arr_seq (next_hyperperiod_job ts arr_seq j)
      = job_index arr_seq j + jobs_per_hyperperiod ts tsk.
    Proof. by have [] := next_hyperperiod_job_properties. Qed.

    (** The "prev" and "next" operations cancel out. *)
    Fact prev_next_hyperperiod_job :
      prev_hyperperiod_job ts arr_seq (next_hyperperiod_job ts arr_seq j)
      = j.
    Proof.
      apply: prev_hyperperiod_job_from_arrival => //.
      - by rewrite next_hyperperiod_job_task.
      - by rewrite next_hyperperiod_job_arrival // addnK.
    Qed.

  End ForwardCorrespondence.

  (** ** Backward Correspondence *)

  Section BackwardCorrespondence.

    (** Consider a job of the task with at least one hyperperiod's worth
        of earlier releases. *)
    Variable j : Job.
    Hypothesis H_arrives : arrives_in arr_seq j.
    Hypothesis H_tsk : job_task j = tsk.
    Hypothesis H_index : jobs_per_hyperperiod ts tsk <= job_index arr_seq j.

    (** We establish the properties of the matching job in the previous
        hyperperiod together, then expose them individually. *)
    Local Fact prev_hyperperiod_job_properties :
      let j' := prev_hyperperiod_job ts arr_seq j in
      [/\ arrives_in arr_seq j'
       , job_task j' = tsk
       , job_arrival j' + hyperperiod ts = job_arrival j
       & job_index arr_seq j' = job_index arr_seq j - jobs_per_hyperperiod ts tsk].
    Proof.
      case COUNT: (jobs_per_hyperperiod ts tsk) => [|k].
      - have HP0 : hyperperiod ts = 0 by rewrite hyperperiod_as_job_count COUNT.
        have -> : prev_hyperperiod_job ts arr_seq j = j
          by apply: prev_hyperperiod_job_from_arrival => //; rewrite HP0 subn0.
        by split => //; rewrite ?COUNT ?HP0 ?addn0 ?subn0.
      - have LT : job_index arr_seq j - jobs_per_hyperperiod ts tsk < job_index arr_seq j by lia.
        have [j' [_ [TSK' [IN' IDX']]]] :=
          exists_jobs_before_j arr_seq H_valid_arrival_sequence j H_arrives _ LT.
        rewrite H_tsk in TSK'.
        have ARR : job_arrival j = job_arrival j' + hyperperiod ts.
        { rewrite hyperperiod_as_job_count.
          apply: periodic_job_index_separation => //.
          by rewrite IDX' subnK. }
        have -> : prev_hyperperiod_job ts arr_seq j = j'
          by apply: prev_hyperperiod_job_from_arrival => //; rewrite ARR addnK.
        by split => //; lia.
    Qed.

    (** The predecessor belongs to the arrival sequence, ... *)
    Fact prev_hyperperiod_job_arrives :
      arrives_in arr_seq (prev_hyperperiod_job ts arr_seq j).
    Proof. by have [] := prev_hyperperiod_job_properties. Qed.

    (** ... arrives exactly one hyperperiod earlier, ... *)
    Lemma prev_hyperperiod_job_arrival :
      job_arrival (prev_hyperperiod_job ts arr_seq j)
      = job_arrival j - hyperperiod ts.
    Proof.
      have [_ _ ARR _] := prev_hyperperiod_job_properties.
      by rewrite -ARR addnK.
    Qed.

    (** ... and has the preceding hyperperiod's job index. *)
    Fact prev_hyperperiod_job_index :
      job_index arr_seq (prev_hyperperiod_job ts arr_seq j)
      = job_index arr_seq j - jobs_per_hyperperiod ts tsk.
    Proof. by have [] := prev_hyperperiod_job_properties. Qed.

    (** The "next" and "prev" operations cancel out. *)
    Fact next_prev_hyperperiod_job :
      next_hyperperiod_job ts arr_seq (prev_hyperperiod_job ts arr_seq j) = j.
    Proof.
      have [_ _ ARR _] := prev_hyperperiod_job_properties.
      apply: next_hyperperiod_job_from_arrival => //.
      by rewrite prev_hyperperiod_job_task.
    Qed.

  End BackwardCorrespondence.

End AdjacentHyperperiodJobs.

(** ** Workload in a Hyperperiod *)

(** The task parameters bound the work released in any hyperperiod. *)
Section HyperperiodWorkloadBound.

  (** Consider periodic tasks with worst-case execution costs ... *)
  Context {Task : TaskType} `{PeriodicModel Task} `{TaskCost Task}.

  (** ... and their jobs. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobCost Job}.

  (** Consider a given set of such periodic tasks ...  *)
  Variable ts : TaskSet Task.
  Hypothesis H_valid_periods : valid_periods ts.

  (** ... and a corresponding valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_periodic_arrivals : taskset_respects_periodic_task_model arr_seq ts.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** If task WCETs bound the execution requirements of arriving jobs, ... *)
  Hypothesis H_valid_job_costs : arrivals_have_valid_job_costs arr_seq.

  (** ... then the total workload in any hyperperiod-sized interval
      is upper-bounded by the hyperperiod workload.  *)
  Lemma workload_in_hyperperiod_bounded :
    forall start,
      total_workload_between arr_seq start (start + hyperperiod ts)
      <= hyperperiod_workload ts.
  Proof.
    move=> start.
    apply: (@leq_trans (\sum_(tsk <- ts)
      task_workload_between arr_seq tsk start (start + hyperperiod ts))).
    - apply: workload_of_jobs_le_sum_over_partitions => // j IN.
      by apply/H_all_jobs_from_taskset/in_arrivals_implies_arrived.
    - rewrite /hyperperiod_workload.
      apply: leq_sum_seq => tsk IN _.
      rewrite /task_workload_between /task_workload /workload_of_jobs -big_filter mulnC.
      apply: leq_trans; first apply: sum_job_costs_bounded.
      + move=> j /[! mem_filter] /andP [TSK ARR]; apply/andP; split=> //.
        by apply/H_valid_job_costs/in_arrivals_implies_arrived.
      + rewrite leq_mul2l; apply/orP; right.
        apply: leq_trans; first by apply: sporadic_task_arrivals_bound.
        rewrite /max_sporadic_arrivals /task_min_inter_arrival_time /periodic_as_sporadic
          addKn /div_ceil /jobs_per_hyperperiod ifT //.
        by apply/lcm_seq_is_mult_of_all_ints/map_f.
  Qed.

End HyperperiodWorkloadBound.
