Require Export prosa.analysis.definitions.priority_inversion.

(** * Lemma about Priority Inversion for arbitrary processors *)
(** In this section, we prove a lemma about the notion of priority
    inversion for arbitrary processors. *)
Section PIGenericProcessorModelLemma.

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


  (** Then we prove that cumulative priority inversion (CPI) that job
      [j] incurs in an interval <<[t1, t2)>> is equal to the sum of
      CPI in an interval <<[t1, t_mid)>> and CPI in an interval
      <<[t_mid, t2)>>. *)
  Lemma cumulative_priority_inversion_cat:
    forall (t_mid t1 t2 : instant),
      t1 <= t_mid ->
      t_mid <= t2 ->
      cumulative_priority_inversion arr_seq sched j t1 t2 =
        cumulative_priority_inversion arr_seq sched j t1 t_mid
        + cumulative_priority_inversion arr_seq sched j t_mid t2.
  Proof.
    intros t_mid t1 t2 LE1 LE2.
    rewrite /cumulative_priority_inversion -big_cat //=.
    replace (index_iota t1 t_mid ++ index_iota t_mid t2) with (index_iota t1 t2); first by reflexivity.
    interval_to_duration t1 t_mid δ1.
    interval_to_duration (t1 + δ1) t2 δ2.
    rewrite -!addnA /index_iota.
    erewrite iotaD_impl with (n_le := δ1); last by lia.
    by rewrite !addKn addnA addKn.
  Qed.

  (** Assume that [j] is scheduled at time [t], then there is no
      priority inversion at time [t]. *)
  Lemma sched_itself_implies_no_priority_inversion :
    forall t,
      scheduled_at sched j t ->
      priority_inversion_dec arr_seq sched j t = false.
  Proof. by move => t SCHED; rewrite /priority_inversion_dec SCHED. Qed.

End PIGenericProcessorModelLemma.
