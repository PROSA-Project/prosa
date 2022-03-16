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
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.

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
    now lia.
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

  (** Any job [j] in [task_arrivals_between arr_seq tsk t1 t2] is also
      contained in [arrivals_between arr_seq t1 t2]. *)
  Lemma task_arrivals_between_subset:
    forall t1 t2 j,
      j \in task_arrivals_between arr_seq tsk t1 t2 ->
      j \in arrivals_between arr_seq t1 t2.
  Proof. move=> t1 t2 j. by rewrite mem_filter; move => /andP [/eqP TSK JB_IN]. Qed.

  (** Any job [j] in [task_arrivals_between arr_seq tsk t1 t2] arrives 
      in the arrival sequence [arr_seq]. *)
  Corollary arrives_in_task_arrivals_implies_arrived:
    forall t1 t2 j,
      j \in task_arrivals_between arr_seq tsk t1 t2 ->
      arrives_in arr_seq j.
  Proof. move=> t1 t2 j IN; apply/in_arrivals_implies_arrived/task_arrivals_between_subset; exact IN. Qed.

  (** Any job [j] in [task_arrivals_before arr_seq tsk t] has an arrival
      time earlier than [t]. *)
  Lemma arrives_in_task_arrivals_before_implies_arrives_before :
    forall j t,
      j \in task_arrivals_before arr_seq tsk t ->
      job_arrival j < t.
  Proof.
    intros * IN.
    unfold task_arrivals_before, task_arrivals_between in *.
    move: IN; rewrite mem_filter => /andP [_ IN].
    by apply in_arrivals_implies_arrived_between in IN => //.
  Qed.

  (** Any job [j] in [task_arrivals_before arr_seq tsk t] is a job of task [tsk]. *)
  Lemma arrives_in_task_arrivals_implies_job_task :
    forall j t,
      j \in task_arrivals_before arr_seq tsk t ->
      job_task j == tsk.
  Proof.
    intros * IN.
    unfold task_arrivals_before, task_arrivals_between in *.
    by move: IN; rewrite mem_filter => /andP [TSK _].
  Qed.

  (** We repeat the observation for [task_arrivals_between]. *)
  Lemma in_task_arrivals_between_implies_job_of_task :
    forall t1 t2 j,
      j \in task_arrivals_between arr_seq tsk t1 t2 ->
      job_task j = tsk.
  Proof.
    move=> t1 t2 j.
    rewrite mem_filter => /andP [JT _].
    by move: JT; rewrite /job_of_task => /eqP.
  Qed.

  (** If a job arrives between to points in time, then the corresponding interval is nonempty... *)
  Lemma task_arrivals_nonempty :
    forall t1 t2 j,
      j \in task_arrivals_between arr_seq tsk t1 t2 ->
      t1 < t2.
  Proof. move=> t1 t2 j IN. by apply /(arrivals_between_nonempty arr_seq _ _ j)/task_arrivals_between_subset. Qed.

  (** ... which we can also express in terms of [number_of_task_arrivals] being nonzero. *)
  Corollary number_of_task_arrivals_nonzero :
    forall t1 t2,
      number_of_task_arrivals arr_seq tsk t1 t2 > 0 ->
      t1 < t2.
  Proof. by move=> t1 t2; rewrite -has_predT => /hasP [j IN] _; eapply task_arrivals_nonempty; eauto. Qed.

  (** An arrival sequence with non-duplicate arrivals implies that the 
      task arrivals also contain non-duplicate arrivals. *)
  Lemma uniq_task_arrivals:
    forall t,
      arrival_sequence_uniq arr_seq ->
      uniq (task_arrivals_up_to arr_seq tsk t).
  Proof.
    intros * UNQ_SEQ.
    apply filter_uniq.
    now apply arrivals_uniq.
  Qed.

  (** The same observation applies to [task_arrivals_between]. *)
  Lemma task_arrivals_between_uniq :
    forall t1 t2,
      arrival_sequence_uniq arr_seq ->
      uniq (task_arrivals_between arr_seq tsk t1 t2).
  Proof. move=> t1 t2 UNIQ. by apply/filter_uniq/arrivals_uniq. Qed.
  
  (** A job cannot arrive before it's arrival time. *) 
  Lemma job_notin_task_arrivals_before :
    forall j t, 
      arrives_in arr_seq j ->
      job_arrival j > t ->
      j \notin task_arrivals_up_to arr_seq (job_task j) t.
  Proof.
    intros j t ARR INEQ.
    apply /negP; rewrite mem_filter => /andP [_ IN].
    apply mem_bigcat_nat_exists in IN; move : IN => [t' [IN NEQt']].
    rewrite -(H_consistent_arrivals j t') in NEQt' => //.
    now lia.
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
      now apply job_in_task_arrivals_between => //; lia.
    - rewrite /task_arrivals_up_to_job_arrival TSK1 TSK2.
      now rewrite -task_arrivals_cat; try by lia.
  Qed.

  (** For any job [j2] with [job_index] equal to [n], the nth job 
   in the sequence [task_arrivals_up_to arr_seq tsk t] is [j2], given that
   [t] is not less than [job_arrival j2]. *)
  (** Note that [j_def] is used as a default job for the access function and
   has nothing to do with the lemma. *)
  Lemma nth_job_of_task_arrivals:
    forall n j_def j t,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_index arr_seq j = n ->
      t >= job_arrival j ->
      nth j_def (task_arrivals_up_to arr_seq tsk t) n = j.
  Proof.
    intros * ARR TSK IND T_G.
    rewrite -IND.
    have EQ_IND : index j (task_arrivals_up_to_job_arrival arr_seq j) = index j (task_arrivals_up_to arr_seq tsk t).
    { have CAT : exists xs, task_arrivals_up_to_job_arrival arr_seq j ++ xs = task_arrivals_up_to arr_seq tsk t.
      { rewrite /task_arrivals_up_to_job_arrival TSK.
        exists (task_arrivals_between arr_seq tsk ((job_arrival j).+1) t.+1).
        now rewrite -task_arrivals_cat.
      }
      move : CAT => [xs ARR_CAT].
      now rewrite -ARR_CAT index_cat ifT; last by apply arrives_in_task_arrivals_up_to.
    }
    rewrite /job_index EQ_IND nth_index => //.
    rewrite mem_filter; apply /andP.
    split; first by apply /eqP.
    now apply job_in_arrivals_between => //.
  Qed.

  (** We show that task arrivals in the interval <<[t1, t2)>> 
   is the same as concatenation of task arrivals at each instant in <<[t1, t2)>>. *)
  Lemma task_arrivals_between_is_cat_of_task_arrivals_at:
    forall t1 t2,
      task_arrivals_between arr_seq tsk t1 t2 = \cat_(t1 <= t < t2) task_arrivals_at arr_seq tsk t.
  Proof.
    intros *.
    rewrite /task_arrivals_between /task_arrivals_at /arrivals_between.
    now apply bigcat_nat_filter_eq_filter_bigcat_nat.
  Qed.

  (** The number of jobs of a task [tsk] in the interval <<[t1, t2)>> is the same 
   as sum of the number of jobs of the task [tsk] at each instant in <<[t1, t2)>>. *)
  Lemma size_of_task_arrivals_between:
    forall t1 t2,
      size (task_arrivals_between arr_seq tsk t1 t2)
      = \sum_(t1 <= t < t2) size (task_arrivals_at arr_seq tsk t). 
  Proof.
    intros *.
    rewrite /task_arrivals_between /task_arrivals_at /arrivals_between.
    now rewrite size_big_nat bigcat_nat_filter_eq_filter_bigcat_nat.
  Qed.

  (** We note that, trivially, the list of task arrivals
      [task_arrivals_between] is sorted by arrival times because the
      underlying [arrivals_between] is sorted, as established by the
      lemma [arrivals_between_sorted]. *)
  Corollary task_arrivals_between_sorted :
    forall t1 t2,
      sorted by_arrival_times (task_arrivals_between arr_seq tsk t1 t2).
  Proof.
    move=> t1 t2. apply sorted_filter;
      first by rewrite /by_arrival_times /transitive; lia.
    exact: arrivals_between_sorted.
  Qed.

End TaskArrivals.
