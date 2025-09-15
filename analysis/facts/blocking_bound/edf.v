Require Export prosa.analysis.definitions.blocking_bound.edf.
Require Export prosa.analysis.facts.busy_interval.pi.
Require Export prosa.model.priority.edf.
Require Export prosa.model.task.absolute_deadline.
Require Export prosa.analysis.facts.model.arrival_curves.

(** * Lower-Priority Non-Preemptive Segment is Bounded *)
(** In this file, we prove that, under the EDF scheduling policy, the
    length of the maximum non-preemptive segment of a lower-priority
    job (w.r.t. a job of a task [tsk]) is bounded by
    [blocking_bound]. *)
Section  MaxNPSegmentIsBounded.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], an arrival curve [max_arrivals], a relative
      deadline [task_deadline], and a bound on the task's longest
      non-preemptive segment [task_max_nonpreemptive_segment] ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], and an arrival
      time [job_arrival]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** Consider any kind of processor state model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider the EDF policy. *)
  Let EDF := EDF Job.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** We further require that a job's cost cannot exceed its task's stated WCET ... *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** ... and assume that jobs have bounded non-preemptive segments. *)
  Context `{JobPreemptable Job}.
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Consider an arbitrary task set [ts], ... *)
  Variable ts : seq Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Let [max_arrivals] be a family of arrival curves. *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Consider any job [j] of [tsk]. *)
  Variable j : Job.
  Hypothesis H_job_of_tsk : job_of_task tsk j.

  (** Then, the maximum length of a nonpreemptive segment among all
      lower-priority jobs (w.r.t. the given job [j]) arrived so far is
      bounded by [blocking_bound]. *)
  Lemma nonpreemptive_segments_bounded_by_blocking :
    forall t1 t2,
      busy_interval_prefix arr_seq sched j t1 t2 ->
      max_lp_nonpreemptive_segment arr_seq j t1 <= blocking_bound ts tsk (job_arrival j - t1).
  Proof.
    move=> t1 t2 BUSY; rewrite /max_lp_nonpreemptive_segment /blocking_bound.
    apply: leq_trans;first by exact: max_np_job_segment_bounded_by_max_np_task_segment.
    apply /bigmax_leq_seqP => j' JINB NOTHEP.
    have ARR': arrives_in arr_seq j'
      by apply: in_arrivals_implies_arrived; exact: JINB.
    apply leq_bigmax_cond_seq with (x := (job_task j')) (F := fun tsk => task_max_nonpreemptive_segment tsk - 1);
      first by apply H_all_jobs_from_taskset.
    apply in_arrivals_implies_arrived_between in JINB => [|//].
    move: JINB; move => /andP [_ TJ'].
    repeat (apply/andP; split); last first.
    { rewrite /hep_job -ltnNge in NOTHEP.
      move: H_job_of_tsk => /eqP <-.
      have ARRLE: job_arrival j' < job_arrival j.
      { by apply: (@leq_trans t1) => //; move: BUSY => [ _  [ _ [ _ /andP [F G]]] ]. }
      move: NOTHEP; rewrite /job_deadline /absolute_deadline.job_deadline_from_task_deadline.
      by lia. }
    { move: NOTHEP => /andP [_ NZ].
      move: (H_valid_job_cost j' ARR'); rewrite /valid_job_cost.
      by lia. }
    { apply: non_pathological_max_arrivals; last first.
      - exact: ARR'.
      - by rewrite /job_of_task.
      - by apply H_is_arrival_curve, H_all_jobs_from_taskset, ARR'. }
  Qed.

End MaxNPSegmentIsBounded.
