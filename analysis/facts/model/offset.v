Require Export prosa.model.task.offset.
Require Export prosa.analysis.facts.job_index.

(** In this module, we prove some properties of task offsets. *)
Section OffsetLemmas.

  (** Consider any type of tasks with an offset ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any arrival sequence with consistent and non-duplicate arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any job [j] (that stems from the arrival sequence) of any
      task [tsk] with a valid offset. *)
  Variable tsk : Task.
  Variable j : Job.
  Hypothesis H_job_of_task: job_task j = tsk.
  Hypothesis H_valid_offset: valid_offset arr_seq tsk.
  Hypothesis H_job_from_arrseq: arrives_in arr_seq j.

  (** We show that the if [j] is the first job of task [tsk]
      then [j] arrives at [task_offset tsk]. *)
  Lemma first_job_arrival:
    job_index arr_seq j = 0 ->
    job_arrival j = task_offset tsk.
  Proof.
    intros INDX.
    move: H_valid_offset => [BEFORE [j' [ARR' [TSK ARRIVAL]]]].
    case: (boolP (j' == j)) => [/eqP EQ|NEQ]; first by rewrite -EQ.
    destruct (PeanoNat.Nat.zero_or_succ (job_index arr_seq j')) as [Z | [m N]].
    - move: NEQ => /eqP NEQ; contradict NEQ.
      by eapply equal_index_implies_equal_jobs; eauto;
        [rewrite TSK | rewrite Z INDX].
    - have IND_LTE : (job_index arr_seq j <= job_index arr_seq j') by rewrite INDX N.
      apply index_lte_implies_arrival_lte in IND_LTE => //; last by rewrite TSK.
      by apply/eqP; rewrite eqn_leq; apply/andP; split;
        [lia | apply H_valid_offset].
  Qed.

  (** Consider any task set [ts]. *)
  Variable ts : TaskSet Task.

  (** If task [tsk] is in [ts], then its offset
   is less than or equal to the maximum offset of all tasks
   in [ts]. *)
  Lemma max_offset_g:
    tsk \in ts ->
    task_offset tsk <= max_task_offset ts.
  Proof.
    intros TSK_IN.
    apply in_max0_le.
    by apply map_f.
  Qed.

End OffsetLemmas.
