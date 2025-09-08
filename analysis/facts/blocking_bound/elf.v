Require Export prosa.analysis.definitions.blocking_bound.elf.
Require Export prosa.analysis.facts.busy_interval.pi.
Require Export prosa.model.task.absolute_deadline.
Require Export prosa.analysis.facts.model.arrival_curves.
Require Import prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.facts.priority.elf.

(** * Lower-Priority Non-Preemptive Segment is Bounded *)
(** In this file, we prove that, under the ELF scheduling policy, the
    length of the maximum non-preemptive segment of a lower-priority
    job (w.r.t. a job of a task [tsk]) is bounded by
    [blocking_bound]. *)
Section MaxNPSegmentIsBounded.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], an arrival curve [max_arrivals], a relative
      deadline [task_deadline], a bound on the task's longest
      non-preemptive segment [task_max_nonpreemptive_segment] and
      relative priority points, ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.
  Context `{PriorityPoint Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], and an arrival
      time [job_arrival]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** Consider any kind of processor state model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any valid arrival sequence ... *)
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

  (** Consider an FP policy that indicates a higher-or-equal priority
      relation, and assume that the relation is reflexive, transitive
      and total. *)
  Context (FP : FP_policy Task).
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** Then, the maximum length of a nonpreemptive segment among all
      lower-priority jobs (w.r.t. the given job [j]) arrived so far is
      bounded by [blocking_bound]. *)
  Lemma nonpreemptive_segments_bounded_by_blocking :
    forall t1 t2,
      busy_interval_prefix arr_seq sched j t1 t2 ->
      max_lp_nonpreemptive_segment arr_seq j t1 <= blocking_bound ts tsk (job_arrival j - t1).
  Proof.
    move=> t1 t2 BUSY; rewrite /max_lp_nonpreemptive_segment /blocking_bound //.
    apply: leq_trans; first by apply: max_np_job_segment_bounded_by_max_np_task_segment.
    apply /bigmax_leq_seqP => j' JINB NOTHEP.
    have ARR': arrives_in arr_seq j'
      by apply: in_arrivals_implies_arrived; exact: JINB.
    apply leq_bigmax_cond_seq with (x := (job_task j')) (F := fun tsk => task_max_nonpreemptive_segment tsk - 1);
      first by apply H_all_jobs_from_taskset.
    apply in_arrivals_implies_arrived_between in JINB => //.
    move: JINB; move => /andP [_ TJ'].
    have ->: (max_arrivals (job_task j') ε > 0) && (task_cost (job_task j') > 0) = true.
    { apply /andP; split.
      { apply: non_pathological_max_arrivals; last first.
        - exact: ARR'.
        - by rewrite /job_of_task.
        - by apply H_is_arrival_curve, H_all_jobs_from_taskset, ARR'. }
      { move: NOTHEP => /andP [_ NZ].
        move: (H_valid_job_cost j' ARR'); rewrite /valid_job_cost.
        by lia. } }
    { move: NOTHEP => /andP [/norP [NOTHP NOTEP] JCOST].
      rewrite ?andbT.
      move: H_job_of_tsk; rewrite /job_of_task => /eqP <-.
      case: (boolP (hep_task (job_task j') (job_task j))) => NOTHEP_Tsk'.
      { rewrite /hp_task NOTHEP_Tsk' => //=.
        rewrite andbF orFb /ep_task.
        rewrite not_hp_hep_task in NOTHP => //.
        rewrite NOTHP NOTHEP_Tsk' //=.
        rewrite NOTHEP_Tsk' Bool.andb_true_l /hep_job /GEL /job_priority_point -ltNge in NOTEP.
        have LT: ((job_arrival j)%:R + task_priority_point (job_task j)
                < (t1)%:R + task_priority_point (job_task j'))%R by lia.
        rewrite natrB; first by lia.
        move: BUSY; rewrite /busy_interval_prefix.
        move=> [? [? [? J_ARR]]].
        by lia. }
      { rewrite not_hep_hp_task in NOTHEP_Tsk' => //.
        by rewrite NOTHEP_Tsk'. } }
  Qed.

End MaxNPSegmentIsBounded.
