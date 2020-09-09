Require Export prosa.analysis.facts.periodic.max_inter_arrival.
Require Export prosa.analysis.facts.model.offset.
Require Export prosa.analysis.facts.periodic.sporadic.

(** In this module, we'll prove the known arrival
    times of jobs that stem from periodic tasks. *)
Section PeriodicArrivalTimes.
  
  (** Consider periodic tasks with an offset ... *)
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
        
  (** We show that the nth job [j] of task [tsk] 
      arrives at the instant [task_offset tsk + n * task_period tsk]. *)
  Lemma periodic_arrival_times:
    forall n (j : Job), 
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_index arr_seq j = n -> 
      job_arrival j = task_offset tsk + n * task_period tsk.
  Proof.
    induction n.
    { intros j ARR TSK_IN ZINDEX.
      rewrite mul0n addn0.
      apply first_job_arrival with (arr_seq0 := arr_seq) (tsk0 := job_task j) => //.
    }
    { intros j ARR TSK_IN JB_INDEX.
      move : (H_task_respects_periodic_model j ARR) => PREV_JOB.
      feed_n 2 PREV_JOB => //; first by ssrlia.
      move : PREV_JOB => [pj [ARR' [IND [TSK ARRIVAL]]]].
      specialize (IHn pj); feed_n 3 IHn => //; first by rewrite IND JB_INDEX; ssrlia.
      rewrite ARRIVAL IHn; ssrlia.
    }
  Qed.

  (** We show that for every job [j] of task [tsk] there exists a number 
   [n] such that [j] arrives at the instant [task_offset tsk + n * task_period tsk]. *)
  Lemma job_arrival_times:
    forall j,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      exists n, job_arrival j = task_offset tsk + n * task_period tsk.
  Proof.
    intros * ARR TSK.
    exists (job_index arr_seq j).
    specialize (periodic_arrival_times (job_index arr_seq j) j) => J_ARR.
    now feed_n 3 J_ARR => //.
  Qed.

  (** If a job [j] of task [tsk] arrives at [task_offset tsk + n * task_period tsk] 
   then the [job_index] of [j] is equal to [n]. *)
  Lemma job_arr_index:
    forall n j,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_arrival j = task_offset tsk + n * task_period tsk ->
      job_index arr_seq j = n.
  Proof.
    have F : task_period tsk > 0 by auto.
    induction n.
    + intros * ARR_J TSK ARR.
      destruct (PeanoNat.Nat.zero_or_succ (job_index arr_seq j)) as [Z | [m SUCC]] => //. 
      now apply periodic_arrival_times in SUCC => //; ssrlia.
    + intros * ARR_J TSK ARR.
      specialize (H_task_respects_periodic_model j); feed_n 3 H_task_respects_periodic_model => //.
      { rewrite lt0n; apply /eqP; intro EQ.
        apply first_job_arrival with (tsk0 := tsk) in EQ => //.
        now rewrite EQ in ARR; ssrlia.
      }
      move : H_task_respects_periodic_model => [j' [ARR' [IND' [TSK' ARRIVAL']]]].
      specialize (IHn j'); feed_n 3 IHn => //; first by rewrite ARR in ARRIVAL'; ssrlia.
      rewrite IHn in IND'.
      destruct (PeanoNat.Nat.zero_or_succ (job_index arr_seq j)) as [Z | [m SUCC]]; last by ssrlia.
      apply first_job_arrival with (tsk0 := tsk) in Z => //.
      now rewrite Z in ARR; ssrlia.
  Qed.
  
End PeriodicArrivalTimes.
