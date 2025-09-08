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

  (** We start with a trivial fact that, given a time interval <<[t1, t2)>>,
      the interval either contains a preemption time [t] or it does not.  *)
  Lemma preemption_time_interval_case :
    forall t1 t2,
      (forall t, t1 <= t < t2 -> ~~ preemption_time arr_seq sched t)
      \/ (exists t,
            t1 <= t < t2
            /\ preemption_time arr_seq sched t
            /\ forall t', t1 <= t' -> preemption_time arr_seq sched t' -> t <= t').
  Proof. by apply earliest_pred_element_exists_case. Qed.

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
      rewrite -(scheduled_job_at_scheduled_at arr_seq) //; exact/eqP/SCHED. }
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
    move: (SCHED); rewrite /preemption_time -(scheduled_job_at_scheduled_at arr_seq) // => /eqP ->.
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

  (** If a job is scheduled at time [t-1] and time [t] is not a
      preemption time, then the job is scheduled at time [t] as
      well. *)
  Lemma neg_pt_scheduled_before :
    forall j t,
      ~~ preemption_time arr_seq sched t ->
      scheduled_at sched j t.-1 ->
      scheduled_at sched j t.
  Proof.
    move => j t NP SCHED; apply negbNE; apply/negP => NSCHED.
    have [Z|POS] := posnP t.
    { by move: SCHED; subst => //= => SCHED; rewrite SCHED in NSCHED. }
    { edestruct scheduled_at_cases as [IDLE| [s SCHEDs]] => //.
      { move: NP => /negP NP; apply: NP; rewrite /preemption_time.
        by rewrite is_idle_iff in IDLE; move: IDLE => /eqP ->. }
      { instantiate (1 := t) in SCHEDs.
        destruct t as [ | t]; [by done | rewrite -pred_Sn in SCHED].
        move: (SCHEDs) => SCHEDst; eapply neg_pt_scheduled_at in SCHEDs => //.
        have EQ : s = j by apply: H_uniproc; [apply SCHEDs | apply SCHED].
        by subst; rewrite SCHEDst in NSCHED. } }
  Qed.

  (** Next we extend the above lemma to an interval. That is, as long as there
      is no preemption time, a job will remain scheduled. *)
  Lemma neg_pt_scheduled_continuously_before :
    forall j t1 t2,
      scheduled_at sched j t1 ->
      t1 <= t2 ->
      (forall t, t1 < t <= t2 -> ~~ preemption_time arr_seq sched t) ->
      scheduled_at sched j t2.
  Proof.
    move => j1 t1 t2 SCHEDBEF LE NPT.
    interval_to_duration t1 t2 t.
    induction t as [ | t IHt]; first by rewrite addn0.
    apply neg_pt_scheduled_before; last rewrite addnS -pred_Sn.
    + by apply NPT; lia.
    + by apply IHt => ??; apply NPT; lia.
  Qed.

  (** Conversely if a job is scheduled at some time [t2] and
      we know that there is no preemption time between [t1]
      and [t2] then the job must have been scheduled at [t1]
      too. *)
  Lemma neg_pt_scheduled_continuously_after :
    forall j t1 t2,
      scheduled_at sched j t2 ->
      t1 <= t2 ->
      (forall t, t1 <= t <= t2 -> ~~ preemption_time arr_seq sched t) ->
      scheduled_at sched j t1.
  Proof.
    move => j1 t1 t2 SCHEDBEF LE NPT.
    interval_to_duration t1 t2 t.
    induction t as [ | t IHt]; first by rewrite addn0 in SCHEDBEF.
    apply IHt.
    - move => ??.
      apply NPT.
      by lia.
    - apply neg_pt_scheduled_at; first by rewrite -addnS.
      apply NPT.
      by lia.
  Qed.

  (** Finally, using the above two lemmas we can prove that, if there is no
      preemption time in an interval <<[t1, t2)>>, then if a job is scheduled
      at time <<t ∈ [t1, t2)>>, then the same job is also scheduled at
      another time <<t' ∈ [t1, t2)>>. *)
  Lemma neg_pt_scheduled_continuous :
    forall j t1 t2 t t',
      t1 <= t < t2 ->
      t1 <= t' < t2 ->
      (forall t, t1 <= t < t2 -> ~~ preemption_time arr_seq sched t) ->
      scheduled_at sched j t ->
      scheduled_at sched j t'.
  Proof.
    move=> j t1 t2 t t' NEQ1 NEQ2 NP SCHED.
    case (t <= t') eqn : EQ.
    - apply: neg_pt_scheduled_continuously_before => //.
      move => ??.
      apply NP.
      by lia.
    - apply (neg_pt_scheduled_continuously_after j t' t) => //; first by lia.
      move => ??.
      apply NP.
      by lia.
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

  (** We can strengthen the above lemma to say that there exists a preemption
      time such that, after the preemption point, the next job to be scheduled
      is scheduled continuously. *)
  Lemma neq_scheduled_at_pt_continuous_sched :
    forall j t,
      scheduled_at sched j t ->
      forall j' t',
        scheduled_at sched j' t' ->
        j != j' ->
        t <= t' ->
        exists pt, 
          preemption_time arr_seq sched pt 
          /\ t < pt <= t' 
          /\ scheduled_at sched j' pt.
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
      - have [PT|NPT] := boolP (preemption_time arr_seq sched t'.+1).
        + exists t'.+1 => //.
          split; [done | split; [|done]].
          by lia.
        + feed_n 3 IH; [by apply neg_pt_scheduled_at => // | done|lia|].
          move : IH => [pt [PT [IN1 SCHED1]]].
          exists pt.
          by split; [done| split; [lia |done]]. }
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

  (** We strengthen the above lemma to say that the preemption time that a segment
      starts with must lie between the last preemption time and the instant we
      know the job is scheduled at. *)
  Lemma scheduling_of_any_segment_starts_with_preemption_time_continuously_sched :
    forall j t1 t2,
      t1 <= t2 ->
      preemption_time arr_seq sched t1 ->
      scheduled_at sched j t2 ->
      exists ptst, 
        t1 <= ptst <= t2 
        /\ preemption_time arr_seq sched ptst 
        /\ scheduled_at sched j ptst.
  Proof.
    move => j t1 t2 GE PREEMPT SCHED.
    have [pt [/andP[LEpt GEpt][PREEMPT' NSCHED]]] :=
      scheduling_of_any_segment_starts_with_preemption_time j t2 SCHED.
    case (t1 <= pt) eqn : T1pt;
      first by (exists pt; split; [lia| split; [done| apply NSCHED => //]; lia]).
    move : T1pt => /negP /negP Eq.
    rewrite -ltnNge in Eq.
    exists t1.
    split; [lia|split; [done|]].
    apply NSCHED.
    lia.
  Qed.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** Assume that the scheduled is valid... *)
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** ... and that the schedule respects the JLFP policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Consider an arbitrary job [j]... *)
  Variable j : Job.

  (** ... and assume that [j] is scheduled at time instants [t1] and [t2]. *)
  Variables t1 t2 : instant.
  Hypothesis H_sched_t1 : scheduled_at sched j t1.
  Hypothesis H_sched_t2 : scheduled_at sched j t2.

  (** In addition, we assume that job [j] remains ready throughout the
      interval <<[t1, t2)>>. *)
  Hypothesis H_j_is_ready :
    forall t, t1 <= t < t2 -> job_ready sched j t.

  (** We prove that if a job [jhp] is scheduled at some time [t]
      within the interval <<[t1, t2)>>, then [jhp] must have higher or
      equal priority than [j].

      This follows from the fact that if a different job [jhp] were to
      be scheduled while [j] is executing, it would require a
      preemption time. Since [j] is ready throughout <<[t1, t2)>>, the
      preemption must have been caused by a job with higher or equal
      priority. *)
  Corollary priority_higher_than_pending_job_priority :
    forall (t : instant),
      t1 <= t < t2 ->
      forall (jhp : Job),
        scheduled_at sched jhp t ->
        hep_job jhp j.
  Proof.
    move=> t NEQ jhp SCHED.
    move: NEQ => /andP [NEQ1 NEQ2]; move: NEQ1; rewrite leq_eqVlt => /orP [/eqP EQ| NEQ1].
    { subst.
      have EQ: jhp = j by apply: H_uniproc => //.
      by subst; apply H_priority_is_reflexive.
    }
    have [/eqP EQ|E] := boolP (j == jhp).
    { by subst; apply H_priority_is_reflexive. }
    { have EX := neq_scheduled_at_pt_continuous_sched _ _ _ _ _ _ _ _ _ H_sched_t1 _ _ SCHED.
      edestruct EX as [pt [PT [NEQ SCHEDpt]]] => //.
      clear EX; apply H_respects_policy with (t := pt) => //.
      apply/andP; split.
      { by apply H_j_is_ready; lia. }
      { apply/negP => SCHEDpt2; move: E => /negP; apply.
        by apply/eqP; apply: H_uniproc => //.
      }
    }
  Qed.

End PreemptionFacts.
