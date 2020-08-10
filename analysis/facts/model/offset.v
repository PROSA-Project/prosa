Require Export prosa.model.task.offset.
Require Export prosa.analysis.facts.job_index.

(** In this module, we'll prove a property of task offsets. *)
Section OffsetLemmas.
  
  (** Consider any type of tasks with an offset ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.

  (** Consider any arrival sequence with consistent and non-duplicate arrivals, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
  Hypothesis H_uniq_arr_seq: arrival_sequence_uniq arr_seq.

  (** ... and any job [j] of any task [tsk] with a valid offset. *)
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
      now eapply equal_index_implies_equal_jobs; eauto;
        [rewrite TSK | rewrite Z INDX].
    - have IND_LTE : (job_index arr_seq j <= job_index arr_seq j') by rewrite INDX N.
      apply index_lte_implies_arrival_lte in IND_LTE => //; last by rewrite TSK.
      now apply/eqP; rewrite eqn_leq; apply/andP; split;
        [ssrlia | apply H_valid_offset].
  Qed.
  
End OffsetLemmas.
