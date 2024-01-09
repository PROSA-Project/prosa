Require Import prosa.model.readiness.basic.
Require Export prosa.model.task.sequentiality.
Require Export prosa.model.priority.fifo.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.analysis.definitions.priority_inversion.
Require Export prosa.analysis.facts.priority.sequential.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.busy_interval.all.
Require Export prosa.analysis.facts.preemption.job.nonpreemptive.
Require Export prosa.analysis.facts.priority.inversion.

(** We first make some trivial observations about the FIFO priority policy to
    avoid having to re-reason these steps repeatedly in the subsequent
    proofs. *)
Section PriorityFacts.

  (** Consider any type of jobs. *)
  Context `{Job : JobType} {Arrival : JobArrival Job}.

  (** Under FIFO scheduling, [hep_job] is simply a statement about arrival
      times. *)
  Fact hep_job_arrival_FIFO :
    forall j j',
      hep_job j j' = (job_arrival j <= job_arrival j').
  Proof.
    move=> j j'.
    by rewrite /hep_job /FIFO.
  Qed.

  (** Similarly, [~~ hep_job] implies a strict inequality on arrival times. *)
  Fact not_hep_job_arrival_FIFO :
    forall j j',
      ~~ hep_job j j' = (job_arrival j' < job_arrival j).
  Proof. by move=> j j'; rewrite hep_job_arrival_FIFO -ltnNge. Qed.

  (** Combining the above two facts, we get that, trivially, [~~ hep_job j j']
      implies [hep_job j' j], ... *)
  Fact not_hep_job_FIFO :
    forall j j',
      ~~ hep_job j j' -> hep_job j' j.
  Proof.
    move=> j j'; rewrite not_hep_job_arrival_FIFO hep_job_arrival_FIFO.
    exact: ltnW.
  Qed.

  (** ... from which we can infer [always_higher_priority]. *)
  Fact not_hep_job_always_higher_priority_FIFO :
    forall j j',
      ~~ hep_job j j' -> always_higher_priority j' j.
  Proof.
    move=> j j' NHEP.
    rewrite always_higher_priority_jlfp; apply/andP; split => //.
    exact: not_hep_job_FIFO.
  Qed.

End PriorityFacts.

(** In this section, we prove some fundamental properties of the FIFO policy. *)
Section BasicLemmas.

  (** We assume the basic (i.e., Liu & Layland)
      readiness model under which any pending job is ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any type of jobs with arrival times and execution costs. *)
  Context `{Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job}.

  (** Consider any valid arrival sequence of such jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and the resulting uniprocessor schedule. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.
  Variable sched : schedule PState.
  (** We assume that the schedule is valid and work-conserving. *)
  Hypothesis H_schedule_is_valid : valid_schedule sched arr_seq.
  Hypothesis H_work_conservation : work_conserving arr_seq sched.

  (** Suppose jobs have preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ...and that the preemption model is valid. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Assume that the schedule respects the FIFO scheduling policy whenever jobs
      are preemptable. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).

  (** We observe that there is no priority inversion in a
      FIFO-compliant schedule. *)
  Lemma FIFO_implies_no_priority_inversion :
    forall j t,
      arrives_in arr_seq j ->
      pending sched j t ->
      ~~ priority_inversion arr_seq sched j t.
  Proof.
    move=> j t IN /andP[ARR]; apply: contraNN => pijt.
    have [j' + PRIO] : exists2 j', scheduled_at sched j' t & ~~ hep_job j' j
      by exact/uni_priority_inversion_P.
    apply: (early_hep_job_is_scheduled arr_seq) => //.
    - by rewrite -not_hep_job_arrival_FIFO.
    - exact: not_hep_job_always_higher_priority_FIFO.
  Qed.

  (** We prove that in a FIFO-compliant schedule, if a job [j] is
      scheduled, then all jobs with higher priority than [j] have been
      completed. *)
  Lemma scheduled_implies_higher_priority_completed :
    forall j t,
      scheduled_at sched j t ->
      forall j_hp,
        arrives_in arr_seq j_hp ->
        ~~ hep_job j j_hp ->
        completed_by sched j_hp t.
  Proof.
    move => j' t SCHED j_hp ARRjhp HEP.
    apply: early_hep_job_is_scheduled => //.
    - by rewrite -not_hep_job_arrival_FIFO.
    - exact: not_hep_job_always_higher_priority_FIFO.
  Qed.

  (** In this section, we prove the cumulative priority inversion for any task
      is bounded by [0]. *)
  Section PriorityInversionBounded.

    (** Consider any kind of tasks. *)
    Context `{Task : TaskType} `{JobTask Job Task}.

    (** Consider a task [tsk]. *)
    Variable tsk : Task.

    (** Assume the arrival times are consistent. *)
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

    (** Assume that the schedule follows the FIFO policy at preemption time. *)
    Hypothesis H_respects_policy_at_preemption_point :
      respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).

    (** Assume the schedule is valid. *)
    Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

    (** Assume there are no duplicates in the arrival sequence. *)
    Hypothesis H_arrival_sequence_is_a_set : arrival_sequence_uniq arr_seq.

    (** Then we prove that the amount of priority inversion is bounded by 0. *)
    Lemma FIFO_implies_no_pi :
      priority_inversion_is_bounded_by arr_seq sched tsk (constant 0).
    Proof.
      move=> j ARRIN TASK POS t1 t2 BUSY.
      rewrite leqn0; apply/eqP; rewrite big_nat_eq0 => t /andP[T1 T2].
      apply/eqP; rewrite eqb0.
      apply: contraT => /negPn pijt.
      have [j' SCHED NHEP] : exists2 j', scheduled_at sched j' t & ~~ hep_job j' j
        by exact/uni_priority_inversion_P.
      move: T1; rewrite leq_eqVlt => /orP [/eqP EQ | GT].
      { have /completed_implies_scheduled_before [//|//|t' [/andP [+ +] _]]:
          completed_by sched j t by apply: (scheduled_implies_higher_priority_completed j').
        by have: t1 <= job_arrival j by []; rewrite -EQ; lia. }
      { exfalso; apply: busy_interval_prefix_no_quiet_time => // [|? ARR HEP ARRB];
          first by apply/andP; split; [|exact: T2].
        apply: (scheduled_implies_higher_priority_completed j') => //.
        move: NHEP; rewrite !not_hep_job_arrival_FIFO.
        by apply: leq_trans. }
    Qed.

  End PriorityInversionBounded.


  (** The next lemma considers FIFO schedules in the context of tasks. *)
  Section SequentialTasks.

    (** If the scheduled jobs stem from a set of tasks, ... *)
    Context {Task : TaskType}.
    Context `{JobTask Job Task}.

    (** ... then the tasks in a FIFO-compliant schedule necessarily
        execute sequentially.  *)
    Lemma tasks_execute_sequentially : sequential_tasks arr_seq sched.
    Proof.
      move => j1 j2 t ARRj1 ARRj2 SAME_TASKx LT => //.
      apply: (early_hep_job_is_scheduled) => //.
      apply: not_hep_job_always_higher_priority_FIFO.
      by rewrite not_hep_job_arrival_FIFO.
    Qed.

    (** We also note that the [FIFO] policy respects sequential tasks. *)
    Fact fifo_respects_sequential_tasks : policy_respects_sequential_tasks (FIFO Job).
    Proof. by move => j1 j2 SAME ARRLE; rewrite hep_job_arrival_FIFO. Qed.

  End SequentialTasks.

  (** Finally, let us further assume that there are no needless
      preemptions among jobs of equal priority. *)
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** In the absence of superfluous preemptions and under assumption
      of the basic readiness model, there are no preemptions at all in
      a FIFO-compliant schedule. *)
  Lemma no_preemptions_under_FIFO :
    forall j t,
      ~~ preempted_at sched j t.
  Proof.
    move => j t; apply /negP => /andP [/andP [SCHED1 NCOMPL] SCHED2].
    case SJA: (scheduled_job_at arr_seq sched t) => [j'|].
    { move: SJA => /eqP; rewrite scheduled_job_at_scheduled_at // => SCHED'.
      have: ~~ hep_job j j'.
      { apply: H_no_superfluous_preemptions; last exact: SCHED'.
        by repeat (apply /andP ; split). }
      rewrite /hep_job /fifo.FIFO -ltnNge => EARLIER.
      eapply (early_hep_job_is_scheduled arr_seq) with (JLFP:=FIFO Job) in SCHED1 => //.
      - apply scheduled_implies_not_completed in SCHED' => //.
        by eapply (incompletion_monotonic sched j' t.-1 t) in SCHED'; [move: SCHED' => /negP|lia].
      - by move=> ?; apply /andP; split; [apply ltnW | rewrite -ltnNge //=]. }
    { move: SJA; rewrite scheduled_job_at_none => // NSCHED.
      have [j' SCHED']: exists j', scheduled_at sched j' t.
      { apply: (H_work_conservation j t) => //.
        apply/andP; split => //.
        rewrite /job_ready/basic_ready_instance/pending.
        apply/andP; split => //.
        have: has_arrived j t.-1; last by rewrite /has_arrived; lia.
        exact: has_arrived_scheduled. }
      by move: (NSCHED  j') => /negP. }
  Qed.

  (** It immediately follows that FIFO schedules are
      non-preemptive. *)
  Corollary FIFO_is_nonpreemptive : nonpreemptive_schedule sched.
  Proof.
    by rewrite -no_preemptions_equiv_nonpreemptive; apply no_preemptions_under_FIFO.
  Qed.

End BasicLemmas.

(** We add the following lemmas to the basic facts database *)
Global Hint Resolve
  fifo_respects_sequential_tasks
  tasks_execute_sequentially
  : basic_rt_facts.
