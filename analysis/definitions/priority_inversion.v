Require Export prosa.analysis.definitions.busy_interval.

(** * Priority Inversion *)
(** In this section, we define the notion of priority inversion for
    arbitrary processors. *)
Section PriorityInversion.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** Consider an arbitrary job. *)
  Variable j : Job.

  (** We say that the job incurs priority inversion if it has higher
      priority than the scheduled job. Note that this definition
      implicitly assumes that the scheduler is
      work-conserving. Therefore, it cannot be applied to models with
      jitter or self-suspensions. *)
  Definition priority_inversion (t : instant) :=
    ~~ scheduled_at sched j t /\
      exists jlp,
        scheduled_at sched jlp t && ~~ hep_job jlp j.

  (** Similarly, we define a decidable counterpart of
      [priority_inversion]. *)
  Definition priority_inversion_dec (t : instant) :=
    ~~ scheduled_at sched j t &&
      has (fun jlp => scheduled_at sched jlp t && ~~ hep_job jlp j)
          (arrivals_before arr_seq t.+1).

  (** In the following short section we show that the propositional
      and computational versions of [priority_inversion] are
      equivalent. *)
  Section PriorityInversionReflection.

    (** We assume that all jobs come from the arrival sequence and do
        not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
    Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

    (** Then the propositional and computational versions of
        [priority_inversion] are equivalent.*)
    Lemma priority_inversion_P :
      forall t, reflect (priority_inversion t) (priority_inversion_dec t).
    Proof.
      move => t; apply /introP.
      - move=> /andP [SCHED /hasP [jlp ARR PRIO]].
        by split => //; (exists jlp).
      - rewrite negb_and /priority_inversion; move=> /orP NPRIO.
        destruct NPRIO as [NSCHED | NHAS].
        + rewrite Bool.negb_involutive in NSCHED.
          by rewrite NSCHED; move => [F _].
        + move => [NSCHED [jlp /andP[SCHED_jlp NHEP]]].
          move: NHAS => /hasPn NJOBS.
          specialize (NJOBS jlp).
          have ARR: jlp \in arrivals_before arr_seq t.+1.
          { move: (H_jobs_must_arrive_to_execute jlp t SCHED_jlp) => ARR.
            apply arrived_between_implies_in_arrivals => //=.
            by apply (H_jobs_come_from_arrival_sequence jlp t).
          }
          move: (NJOBS ARR) => /negP NN.
          by apply NN; apply /andP; split => //.
    Qed.

    (** Similarly, we prove that the negated counterparts are also equivalent. *)
    Corollary priority_inversion_negP :
      forall t, reflect (~ priority_inversion t) (~~ priority_inversion_dec t).
    Proof.
      move=> t; apply /introP.
      - by move => /priority_inversion_P DEC.
      - by move=> /negPn /priority_inversion_P; auto.
    Qed.

  End PriorityInversionReflection.

  (** Cumulative priority inversion incurred by a job within some time
      interval <<[t1, t2)>> is the total number of time instances
      within <<[t1,t2)>> at which job [j] incurred priority
      inversion. *)
  Definition cumulative_priority_inversion (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) priority_inversion_dec t.

  (** We say that the priority inversion experienced by a job [j] is
      bounded by a constant [B] if the cumulative priority inversion
      within any busy interval prefix is bounded by [B]. *)
  Definition priority_inversion_of_job_is_bounded_by_constant (B : duration) :=
    forall (t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 ->
      cumulative_priority_inversion t1 t2 <= B.

  (** More generally, if the priority inversion experienced by job [j]
      depends on its relative arrival time w.r.t. the beginning of its
      busy interval at a time [t1], we say that the priority inversion
      of job [j] is bounded by a function [B : duration -> duration] if
      the cumulative priority inversion within any busy interval
      prefix is bounded by [B (job_arrival j - t1)] *)
  Definition priority_inversion_of_job_is_bounded_by (B : duration -> duration) :=
    forall (t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 ->
      cumulative_priority_inversion t1 t2 <= B (job_arrival j - t1).

End PriorityInversion.

(** In this section, we define a notion of the bounded priority inversion for tasks. *)
Section TaskPriorityInversionBound.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** We say that priority inversion of task [tsk] is bounded by a constant
      [B] if all jobs released by the task have cumulative priority inversion
      bounded by [B]. *)
  Definition priority_inversion_is_bounded_by_constant (B : duration) :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost j > 0 ->
      priority_inversion_of_job_is_bounded_by_constant arr_seq sched j B.

  (** We say that task [tsk] has bounded priority inversion if all its
      jobs have bounded cumulative priority inversion that depends on
      its relative arrival time w.r.t. the beginning of the busy
      interval. *)
  Definition priority_inversion_is_bounded_by (B : duration -> duration) :=
    forall (j : Job),
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost j > 0 ->
      priority_inversion_of_job_is_bounded_by arr_seq sched j B.

End TaskPriorityInversionBound.
