From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Import prosa.analysis.facts.busy_interval.ideal.priority_inversion_bounded.

(** * Priority Inversion is Bounded *)

(** In this file, we prove that any priority inversion that occurs in a model with
    a given JLFP policy and bounded nonpreemptive segments is bounded. *)
Section PriorityInversionIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In addition, we assume that each task has a maximal non-preemptive
    segment ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (**  ... and any type of preemptable jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any valid arrival sequence,... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any ideal uniprocessor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** Consider a JLFP policy that indicates a higher-or-equal priority relation,
      and assume that the relation is reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive: reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive: transitive_job_priorities JLFP.

  (** And assume that they define a valid preemption model with
      bounded nonpreemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Further, allow for any work-bearing notion of job readiness. *)
  Context `{@JobReady Job (ideal.processor_state Job) Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** We assume that the schedule is valid. *)
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ...,it respects the scheduling policy at every preemption point,... *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** ... and complies with the preemption model. *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** Now, we consider an arbitrary task set [ts]... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Let [blocking_bound] be a bound on the priority inversion caused by jobs
      with lower priority. *)
  Variable blocking_bound: duration -> duration.

  (** First, we observe that the maximum non-preemptive segment length of any
      task that releases a job with lower priority (w.r.t. a given job [j])
      and non-zero execution cost upper-bounds the maximum possible length
      of priority inversion (of said job [j]).  *)
  Lemma priority_inversion_is_bounded_by_max_np_segment:
  forall j t1,
    max_length_of_priority_inversion arr_seq j t1
    <= \max_(j_lp <- arrivals_between arr_seq 0 t1 | (~~ JLFP j_lp j)
                                                     && (job_cost j_lp >0))
      (task_max_nonpreemptive_segment (job_task j_lp) - ε).
  Proof.
    move=> j t.
    rewrite /max_length_of_priority_inversion.
    apply: leq_big_max => j' JINB NOTHEP.
    rewrite leq_sub2r //.
    apply in_arrivals_implies_arrived in JINB.
    by apply H_valid_model_with_bounded_nonpreemptive_segments.
  Qed.

  (** We show that, if the maximum length of a priority inversion of a given job [j]
      is bounded by the blocking bound,... *)
  Hypothesis H_priority_inversion_is_bounded_by_blocking:
    forall j t1 t2,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      busy_interval_prefix arr_seq sched j t1 t2 ->
      max_length_of_priority_inversion arr_seq j t1 <= blocking_bound (job_arrival j - t1).

  (** ... then the priority inversion incurred by any job is bounded by the blocking bound. *)
  Lemma priority_inversion_is_bounded:
    priority_inversion_is_bounded_by arr_seq sched tsk blocking_bound.
  Proof.
    move=> j ARR TSK POS t1 t2 PREF.
    move: (PREF) => [_ [_ [_ /andP [T _]]]].
    move: H_valid_schedule => [COARR MBR].
    have [NEQ|NEQ] := boolP ((t2-t1) <= blocking_bound (job_arrival j - t1)).
    { apply leq_trans with (t2 -t1) => [|//].
      rewrite /cumulative_priority_inversion.
      rewrite -[X in _ <= X]addn0 -[t2 - t1]mul1n -iter_addn -big_const_nat.
      by rewrite leq_sum //; move=> t _; destruct (priority_inversion). }
    have [ppt [PPT' /andP[GE LE]]]: exists ppt : instant,
                                      preemption_time arr_seq sched ppt /\
                                      t1 <= ppt <=
                                      t1 + max_length_of_priority_inversion arr_seq j t1.
    by apply /preemption_time_exists.
    apply leq_trans with (cumulative_priority_inversion arr_seq sched j t1 ppt);
      last apply leq_trans with (ppt - t1).
    apply: priority_inversion_occurs_only_till_preemption_point =>//.
    { rewrite /cumulative_priority_inversion -[X in _ <= X]addn0 -[ppt - t1]mul1n
              -iter_addn -big_const_nat.
      by rewrite leq_sum //; move=> t _; case: priority_inversion. }
    { rewrite leq_subLR; apply leq_trans with (t1 + max_length_of_priority_inversion arr_seq j t1) => [//|].
      by rewrite leq_add2l; apply: (H_priority_inversion_is_bounded_by_blocking j t1 t2). }
    Qed.

End PriorityInversionIsBounded.
