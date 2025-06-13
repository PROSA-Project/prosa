Require Export prosa.analysis.definitions.busy_interval.classical.
Require Export prosa.analysis.facts.model.preemption.

(** In this file, we prove a few useful lemmas about the
    [completes_at] predicate. *)
Section CompletesAtLemmas.

  (** Consider any type of jobs with a priority relation. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JLFP_policy Job}.

  (** Consider any kind of uniprocessor state model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.

  (** Consider any arrival sequence with consistent non-duplicate arrivals *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** If a job [j] completes at time [t > 0], then it must have been
      scheduled at time [t - 1]. *)
  Lemma scheduled_at_precedes_completes_at :
    forall (j : Job) (t : instant),
      t > 0 ->
      completes_at sched j t ->
      scheduled_at sched j t.-1.
  Proof.
    move=> j t POS COMP.
    move: COMP; rewrite /completes_at /completed_by -ltnNge.
    destruct t as [|t]; first by lia.
    rewrite -pred_Sn -service_last_plus_before.
    have ->: t.+1 == 0 = false by lia.
    rewrite orbF; move => /andP [A B]; move: (leq_trans A B).
    rewrite -addn1 leq_add2l => SP.
    by apply service_at_implies_scheduled_at.
  Qed.

  (** Next, we show that any job [j] can be completed at most once. *)
  Lemma job_completes_at_most_once :
    forall (j : Job) (t1 t2 : instant),
      \sum_(t1 <= t < t2) completes_at sched j t <= 1.
  Proof.
    move=> j t1 t2; move_neq_up TWO.
    apply sum_ge_2_nat in TWO; last by intros; destruct completes_at.
    destruct TWO as [to1 [to2 [LE1 [LE2 [LE3 [EQ1 EQ2]]]]]].
    move: EQ1 EQ2; rewrite !eqb1 => /andP [_ C1] /andP [NC2 _].
    have EQ: (to2 == 0) = false; [by lia | rewrite EQ orbF in NC2; clear EQ].
    move: NC2 => /negP NC2; apply:NC2.
    by apply: completion_monotonic; try exact C1; lia.
  Qed.

  (** At any time [t > 0], at most one job satisfying predicate [P]
      and arriving before time [B] can complete. *)
  Lemma only_one_job_completes_at_a_time :
    forall (P : pred Job) (t B : instant),
      t > 0 ->
      \sum_(j <- arrivals_before arr_seq B | P j) completes_at sched j t <= 1.
  Proof.
    move=> P t B POS; rewrite big_seq_cond big_mkcond //=.
    move_neq_up TWO; apply sum_ge_2_seq in TWO; first last.
    { by intros; destruct (_ \in _), P, completes_at. }
    { by apply arrivals_uniq. }
    destruct TWO as [j1 [j2 [NEQ [IN1 [IN2 [CA1 CA2]]]]]].
    rewrite IN1 andTb in CA1; rewrite IN2 andTb in CA2.
    destruct (P j1), (P j2) => //.
    move: CA1 CA2; rewrite !eqb1 => CA1 CA2; apply scheduled_at_precedes_completes_at in CA1, CA2 => //.
    move: NEQ => /negP NEQ; apply: NEQ; apply/eqP.
    by apply: H_uniprocessor_proc_model.
  Qed.

  (** Consider a valid preemption model. *)
  Context `{JobPreemptable Job}.
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** We prove that any completion time is a preemption time. *)
  Lemma completetion_time_is_preemption_time :
    forall (j : Job) (t : instant),
      completes_at sched j t ->
      preemption_time arr_seq sched t.
  Proof.
    move=> s t CA; move: (CA) => /andP [NCOMP COMP].
    have [Z|POS] := posnP t.
    { subst. apply zero_is_pt => //. }
    { eapply scheduled_at_precedes_completes_at in CA => //.
      apply completed_implies_not_scheduled in COMP => //.
      apply/negPn/negP => NPI.
      eapply neg_pt_scheduled_before in NPI => //.
      by rewrite NPI in COMP.
    }
  Qed.

  (** No higher-or-equal priority job that arrived before the start of
      a busy-interval prefix can complete during the prefix. *)
  Lemma no_early_hep_job_completes_during_busy_prefix :
    forall (j : Job) (t t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 ->
      t1 < t <= t2 ->
      forall jhp : Job,
        (jhp \in arrivals_before arr_seq t1) ->
        hep_job jhp j ->
        ~~ completes_at sched jhp t.
  Proof.
    move=> j t t1 t2 BUSY NEQ jhp ARR HEP.
    rewrite /completes_at.
    have ->: t == 0 = false by lia.
    rewrite orbF negb_and; apply/orP; left.
    apply/negPn; apply completion_monotonic with t1; first by lia.
    apply BUSY => //.
    { by apply: in_arrivals_implies_arrived. }
    { by apply in_arrivals_implies_arrived_between in ARR => //. }
  Qed.

End CompletesAtLemmas.
