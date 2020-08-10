Require Export prosa.model.task.arrivals.
Require Export prosa.util.all.
Require Export prosa.analysis.facts.behavior.arrivals.
        
(** In this file we provide basic properties related to tasks on arrival sequences. *)
Section TaskArrivals.

  (** Consider any type of job associated with any type of tasks. *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  
  (** Consider any job arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  
  (** We show that the number of arrivals of task can be split into disjoint intervals. *) 
  Lemma num_arrivals_of_task_cat:
    forall tsk t t1 t2,
      t1 <= t <= t2 ->
      number_of_task_arrivals arr_seq tsk t1 t2 =
      number_of_task_arrivals arr_seq tsk t1 t + number_of_task_arrivals arr_seq tsk t t2.
  Proof.
    move => tsk t t1 t2 /andP [GE LE].
    rewrite /number_of_task_arrivals /task_arrivals_between /arrivals_between. 
    now rewrite (@big_cat_nat _ _ _ t) //= filter_cat size_cat.
  Qed.

  (** To simplify subsequent proofs, we further lift [arrivals_between_cat] to
      the filtered version [task_arrivals_between]. *)
  Lemma task_arrivals_between_cat:
    forall tsk t1 t t2,
      t1 <= t ->
      t <= t2 ->
      task_arrivals_between arr_seq tsk t1 t2
      = task_arrivals_between arr_seq tsk t1 t ++ task_arrivals_between arr_seq tsk t t2.
  Proof.
    move=> tsk t1 t t2 LEQ_t1 LEQ_t2.
    now rewrite /task_arrivals_between -filter_cat -arrivals_between_cat.
  Qed.
  
  (** We show that [task_arrivals_up_to_job_arrival j1] is a prefix 
   of [task_arrivals_up_to_job_arrival j2] if [j2] arrives at the same time 
   or after [j1]. *)
  Lemma task_arrivals_up_to_prefix_cat: 
    forall j1 j2,
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 ->
      job_task j1 = job_task j2 ->
      job_arrival j1 <= job_arrival j2 ->
      prefix Job (task_arrivals_up_to_job_arrival arr_seq j1) (task_arrivals_up_to_job_arrival arr_seq j2).
  Proof.
    intros j1 j2 ARR1 ARR2 TSK ARR_LT.
    exists (task_arrivals_between arr_seq (job_task j1) (job_arrival j1 + 1) (job_arrival j2 + 1)).
    now rewrite /task_arrivals_up_to_job_arrival !addn1 TSK -task_arrivals_between_cat.
  Qed.    

  (** Let [tsk] be any task. *)
  Variable tsk : Task.
  
  (** Any job [j] from the arrival sequence is contained in 
   [task_arrivals_up_to_job_arrival j]. *)
  Lemma arrives_in_task_arrivals_up_to:
    forall j,
      arrives_in arr_seq j ->
      j \in task_arrivals_up_to_job_arrival arr_seq j.
  Proof.
    intros j ARR.
    rewrite mem_filter; apply /andP.
    split; first by apply /eqP => //. 
    move : ARR => [t ARR]; move : (ARR) => EQ.
    apply H_consistent_arrivals in EQ.
    rewrite (mem_bigcat_nat _ (fun t => arrivals_at arr_seq t) j 0 _ (job_arrival j)) // EQ //.
    now ssrlia.
  Qed.

  (** Also, any job [j] from the arrival sequence is contained in 
   [task_arrivals_at_job_arrival j]. *)
  Lemma arrives_in_task_arrivals_at:
    forall j,
      arrives_in arr_seq j ->
      j \in task_arrivals_at_job_arrival arr_seq j.
  Proof.
    intros j ARR.
    rewrite mem_filter; apply /andP.
    split; first by apply /eqP => //. 
    rewrite /arrivals_at.
    move : ARR => [t ARR].
    now rewrite (H_consistent_arrivals j t ARR).
  Qed.

  (** We show that for any time [t_m] less than or equal to [t], 
      task arrivals up to [t_m] forms a prefix of task arrivals up to [t]. *)
  Lemma task_arrivals_cat:
    forall t_m t,
      t_m <= t ->
      task_arrivals_up_to arr_seq tsk t =
      task_arrivals_up_to arr_seq tsk t_m ++ task_arrivals_between arr_seq tsk t_m.+1 t.+1.
  Proof.
    intros t1 t2 INEQ.
    now rewrite -filter_cat -arrivals_between_cat. 
  Qed.

  (** We observe that for any job [j], task arrivals up to [job_arrival j] is a 
      concatenation of task arrivals before [job_arrival j] and task arrivals 
      at [job_arrival j]. *)
  Lemma task_arrivals_up_to_cat:
    forall j,
      arrives_in arr_seq j ->
      task_arrivals_up_to_job_arrival arr_seq j =
      task_arrivals_before_job_arrival arr_seq j ++ task_arrivals_at_job_arrival arr_seq j.
  Proof.
    intros j ARR.
    rewrite /task_arrivals_up_to_job_arrival /task_arrivals_up_to
            /task_arrivals_before /task_arrivals_between. 
    rewrite -filter_cat (arrivals_between_cat _ 0 (job_arrival j) (job_arrival j).+1) //.
    now rewrite /arrivals_between big_nat1.
  Qed.

  (** We show that any job [j] in the arrival sequence is also contained in task arrivals 
      between time instants [t1] and [t2], if [job_arrival j] lies in the interval <<[t1,t2)>>. *)
  Lemma job_in_task_arrivals_between:
    forall j t1 t2,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      t1 <= job_arrival j < t2 -> 
      j \in task_arrivals_between arr_seq tsk t1 t2.
  Proof.
    intros * ARR TSK INEQ.
    rewrite mem_filter; apply/andP.
    split; first by apply /eqP => //.
    now apply arrived_between_implies_in_arrivals.
  Qed.

  (** An arrival sequence with non-duplicate arrivals implies that the 
      task arrivals also contain non-duplicate arrivals. *)
  Lemma uniq_task_arrivals:
    forall j,
      arrives_in arr_seq j ->
      arrival_sequence_uniq arr_seq ->
      uniq (task_arrivals_up_to arr_seq (job_task j) (job_arrival j)).
  Proof.
    intros j ARR UNQ_ARR.
    apply filter_uniq.
    now apply arrivals_uniq.
  Qed.

  (** A job cannot arrive before it's arrival time. *) 
  Lemma job_notin_task_arrivals_before:
    forall j t, 
      arrives_in arr_seq j ->
      job_arrival j > t ->
      j \notin task_arrivals_up_to arr_seq (job_task j) t.
  Proof.
    intros j t ARR INEQ.
    apply /negP; rewrite mem_filter => /andP [_ IN].
    apply mem_bigcat_nat_exists in IN; move : IN => [t' [IN NEQt']].
    rewrite -(H_consistent_arrivals j t') in NEQt' => //.
    now ssrlia.
  Qed.

  (** We show that for any two jobs [j1] and [j2], task arrivals up to arrival of job [j1] form a 
      strict prefix of task arrivals up to arrival of job [j2]. *)
  Lemma arrival_lt_implies_strict_prefix:
    forall j1 j2,
      job_task j1 = tsk ->
      job_task j2 = tsk ->
      arrives_in arr_seq j1 ->
      arrives_in arr_seq j2 -> 
      job_arrival j1 < job_arrival j2 ->
      strict_prefix _ (task_arrivals_up_to_job_arrival arr_seq j1) (task_arrivals_up_to_job_arrival arr_seq j2).
  Proof.
    intros j1 j2 TSK1 TSK2 ARR_1 ARR_2 ARR_INEQ.
    exists (task_arrivals_between arr_seq tsk ((job_arrival j1).+1) ((job_arrival j2).+1)).
    split.
    - move: (in_nil j2) => /negP => JIN NIL.
      rewrite -NIL in JIN; contradict JIN.
      now apply job_in_task_arrivals_between => //; ssrlia.
    - rewrite /task_arrivals_up_to_job_arrival TSK1 TSK2.
      now rewrite -task_arrivals_cat; try by ssrlia.
  Qed.
  
End TaskArrivals.
