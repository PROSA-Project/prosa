Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.facts.model.scheduled.

(** In this section, we establish two basic facts about preemption times. *)
Section PreemptionTimes.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume the existence of a function mapping a job and
      its progress to a boolean value saying whether this job is
      preemptable at its current point of execution. *)
  Context `{JobPreemptable Job}.

  (** Consider any valid arrival sequence *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Allow for any uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.

  (** Next, consider any schedule of the arrival sequence... *)
  Variable sched : schedule PState.

  (** ... where jobs come from the arrival sequence and don't execute before
      their arrival time. *)
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_must_arrive: jobs_must_arrive_to_execute sched.

  (** Consider a valid preemption model. *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** An idle instant is a preemption time. *)
  Lemma idle_time_is_pt :
    forall t,
      is_idle arr_seq sched t ->
      preemption_time arr_seq sched t.
  Proof. by move=> t; rewrite is_idle_iff /preemption_time => /eqP ->. Qed.

  (**  We show that time 0 is a preemption time. *)
  Lemma zero_is_pt: preemption_time arr_seq sched 0.
  Proof.
    rewrite /preemption_time.
    case SCHED: (scheduled_job_at _ _  0) => [j|//].
    have ARR: arrives_in arr_seq j.
    { apply: H_jobs_come_from_arrival_sequence.
      rewrite -(scheduled_job_at_iff arr_seq) //; exact: SCHED. }
    rewrite /service /service_during big_geq //.
    by move: (H_valid_preemption_model j ARR) => [PP _].
  Qed.

  (** Also, we show that the first instant of execution is a preemption time. *)
  Lemma first_moment_is_pt:
    forall j prt,
      arrives_in arr_seq j ->
      ~~ scheduled_at sched j prt ->
      scheduled_at sched j prt.+1 ->
      preemption_time arr_seq sched prt.+1.
  Proof.
    move=> s pt ARR NSCHED SCHED.
    move: (SCHED); rewrite /preemption_time -(scheduled_job_at_iff arr_seq) // => ->.
    by move: (H_valid_preemption_model s ARR) => [_ [_ [_ P]]]; apply P.
  Qed.

  (** If a job is scheduled at a point in time that is not a preemption time,
      then it was previously scheduled. *)
  Lemma neg_pt_scheduled_at :
    forall j t,
      scheduled_at sched j t.+1 ->
      ~~ preemption_time arr_seq sched t.+1 ->
      scheduled_at sched j t.
  Proof.
    move => j t sched_at_next.
    apply contraNT => NSCHED.
    exact: (first_moment_is_pt j).
  Qed.

  (** If we observe two different jobs scheduled at two points in time, then
      there necessarily is a preemption time in between. *)
  Lemma neq_scheduled_at_pt :
    forall j t,
      scheduled_at sched j t ->
      forall j' t',
        scheduled_at sched j' t' ->
        j != j' ->
        t <= t' ->
        exists2 pt, preemption_time arr_seq sched pt & t < pt <= t'.
  Proof.
    move=> j t SCHED j'.
    elim.
    { move=> SCHED' NEQ /[!leqn0]/eqP EQ.
      exfalso; apply/neqP; [exact: NEQ|].
      apply: H_uniproc.
      - exact: SCHED.
      - by rewrite EQ. }
    { move=> t' IH SCHED' NEQ.
      rewrite leq_eqVlt => /orP [/eqP EQ|LT //].
      - exfalso; apply/neqP; [exact: NEQ|].
        by rewrite -EQ in SCHED'; exact: (H_uniproc _ _ _ _ SCHED SCHED').
      - have [PT|NPT] := boolP (preemption_time arr_seq sched t'.+1);
          first by exists t'.+1 => //; apply/andP; split.
        have [pt PT /andP [tpt ptt']] :
          exists2 pt, preemption_time arr_seq sched pt & t < pt <= t'.
        { apply: IH => //.
          by apply: neg_pt_scheduled_at. }
        by exists pt => //; apply/andP; split. }
  Qed.


End PreemptionTimes.

(** In this section, we prove a lemma relating scheduling and preemption times. *)
Section PreemptionFacts.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** Allow for any uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.

  Context `{@JobReady Job PState Cost Arrival}.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Next, consider any valid schedule of this arrival sequence. *)
  Variable sched : schedule PState.
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** In addition, we assume the existence of a function mapping jobs to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model. *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** We prove that every nonpreemptive segment always begins with a preemption time. *)
  Lemma scheduling_of_any_segment_starts_with_preemption_time:
    forall j t,
      scheduled_at sched j t ->
      exists pt,
        job_arrival j <= pt <= t /\
          preemption_time arr_seq sched pt /\
          (forall t', pt <= t' <= t -> scheduled_at sched j t').
  Proof.
    intros s t SCHEDst.
    have EX: exists t', (t' <= t) && (scheduled_at sched s t')
                   && (all (fun t'' => scheduled_at sched  s t'') (index_iota t' t.+1 )).
    { exists t. apply/andP; split; [ by apply/andP; split | ].
      apply/allP; intros t'.
      by rewrite mem_index_iota ltnS -eqn_leq; move => /eqP <-.
    }
    have MATE : jobs_must_arrive_to_execute sched by [].
    move :  (H_sched_valid) =>  [COME_ARR READY].
    have MIN := ex_minnP EX.
    move: MIN => [mpt /andP [/andP [LT1 SCHEDsmpt] /allP ALL] MIN]; clear EX.
    destruct mpt as [|mpt].
    - exists 0; repeat split.
      + by apply/andP; split => //; apply MATE.
      +  eapply (zero_is_pt arr_seq); eauto 2.
      + by intros; apply ALL; rewrite mem_iota subn0 add0n ltnS.
    - have NSCHED: ~~ scheduled_at sched  s mpt.
      { apply/negP; intros SCHED.
        enough (F : mpt < mpt); first by rewrite ltnn in F.
        apply MIN.
        apply/andP; split; [by apply/andP; split; [ apply ltnW | ] | ].
        apply/allP; intros t'.
        rewrite mem_index_iota; move => /andP [GE LE].
        move: GE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LT].
        - by subst t'.
        - by apply ALL; rewrite mem_index_iota; apply/andP; split.
      }
      have PP: preemption_time arr_seq sched mpt.+1
        by eapply (first_moment_is_pt arr_seq)  with (j := s); eauto 2.
      exists mpt.+1; repeat split=> //.
      + by apply/andP; split=> [|//]; apply MATE in SCHEDsmpt.
      + move => t' /andP [GE LE].
        by apply ALL; rewrite mem_index_iota; apply/andP; split.
  Qed.

End PreemptionFacts.
