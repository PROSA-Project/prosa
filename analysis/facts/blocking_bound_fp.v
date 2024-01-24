Require Export prosa.analysis.definitions.blocking_bound_fp.
Require Export prosa.analysis.facts.busy_interval.pi.


(** * Lower-Priority Non-Preemptive Segment is Bounded *)
(** In this file, we prove that, under the FP scheduling policy, the
    length of the maximum non-preemptive segment of a lower-priority
    job (w.r.t. a job of a task [tsk]) is bounded by
    [blocking_bound]. *)
Section  MaxNPSegmentIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider an FP policy. *)
  Context {FP : FP_policy Task}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Consider an arbitrary task set [ts], ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider any job [j] of [tsk]. *)
  Variable j : Job.
  Hypothesis H_job_of_tsk : job_of_task tsk j.

  (** Then, the maximum length of a nonpreemptive segment among all
      lower-priority jobs (w.r.t. the given job [j]) arrived so far is
      bounded by [blocking_bound]. *)
  Lemma priority_inversion_is_bounded_by_blocking :
    forall t,
      max_lp_nonpreemptive_segment arr_seq j t <= blocking_bound ts tsk.
  Proof.
    move=> t; move: H_job_of_tsk => /eqP TSK.
    apply: leq_trans; first exact: max_np_job_segment_bounded_by_max_np_task_segment.
    apply: (@leq_trans (\max_(j_lp <- arrivals_between arr_seq 0 t
                             | (~~ hep_task (job_task j_lp) tsk) && (0 < job_cost j_lp))
                         (task_max_nonpreemptive_segment (job_task j_lp) - ε))).
    { rewrite /hep_job /FP_to_JLFP TSK.
      apply: leq_big_max => j' JINB NOTHEP.
      by rewrite leq_sub2r //. }
    { apply /bigmax_leq_seqP => j' JINB /andP[NOTHEP POS].
      apply leq_bigmax_cond_seq with
        (x := (job_task j')) (F := fun tsk => task_max_nonpreemptive_segment tsk - 1);
        last by done.
      apply: H_all_jobs_from_taskset.
      by apply: in_arrivals_implies_arrived (JINB). }
  Qed.

End MaxNPSegmentIsBounded.
