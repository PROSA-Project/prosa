Require Export prosa.analysis.definitions.priority_inversion.
Require Export prosa.analysis.facts.model.uniprocessor.

(** * Lemmas about Priority Inversion *)

(** This file collects basic facts about the notion of priority inversion in the
    general context of arbitrary processor models. *)
Section PI.

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

  (** ... any valid arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any valid schedule. *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** Assume a given reflexive JLFP policy... *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** ... and consider an arbitrary job. *)
  Variable j : Job.

  (** ** Occurrence of Priority Inversion *)

  (** First, we observe conditions under which priority inversions does, or does
      not, arise. *)

    (** Assume that [j] is scheduled at time [t], then there is no
        priority inversion at time [t]. *)
  Lemma sched_itself_implies_no_priority_inversion :
    forall t,
      scheduled_at sched j t ->
      ~~ priority_inversion arr_seq sched j t.
  Proof. by move=> t SCHED; rewrite negb_and negbK scheduled_jobs_at_iff// SCHED. Qed.

  (** Conversely, if job [j] experiences a priority inversion at time [t], then
      some (other) job is scheduled at the time, ... *)
  Lemma priority_inversion_scheduled_at :
    forall t,
      priority_inversion arr_seq sched j t ->
      exists j', scheduled_at sched j' t.
  Proof.
    move=> t /andP [_ /hasP [j' SCHED  _]].
    by exists j'; move: SCHED; rewrite scheduled_jobs_at_iff.
  Qed.

  (** ... and thus there is no priority inversion at idle instants. *)
  Lemma no_priority_inversion_when_idle :
    forall t,
      is_idle arr_seq sched t ->
      ~~ priority_inversion arr_seq sched j t.
  Proof.
    move=> t /[!is_idle_iff] /eqP // /[!scheduled_job_at_none] // IDLE.
    apply: contraT => /negPn.
    move=> /andP [_ /hasP [j' SCHED  _]].
    rewrite scheduled_jobs_at_iff // in SCHED.
    by move: (IDLE j') => /negP.
  Qed.

  Section Uniprocessors.

    (** ** Occurrence of Priority Inversion on Uniprocessors *)

    (** Stronger conditions hold on uniprocessors since only one job can be
        scheduled at any time. *)
    Hypothesis H_uni : uniprocessor_model PState.

    (** On a uniprocessor, the job scheduled when [j] incurs priority inversion
        necessarily has lower priority than [j]. *)
    Lemma priority_inversion_hep_job :
      forall t j',
        scheduled_at sched j' t ->
        priority_inversion arr_seq sched j t = ~~ hep_job j' j.
    Proof.
      move=> t j' SCHED'.
      case HEP: (~~ hep_job _ _); apply/eqP.
      { rewrite eqb_id; apply/andP; split.
        - rewrite scheduled_jobs_at_iff //.
          apply: scheduled_job_at_neq => //.
          apply: contraT => /negPn/eqP EQ.
          by move: HEP; rewrite EQ H_priority_is_reflexive.
        - apply/hasP; exists j' => //.
          by rewrite scheduled_jobs_at_iff. }
      { rewrite eqbF_neg; apply contraT => /negPn /andP[_ /hasP [j'' /[!scheduled_jobs_at_iff] // SCHED''  HEP'']].
        move: HEP HEP''.
        by have -> : j' = j'' by apply: H_uni. }
    Qed.

    (** Conversely, if a higher-priority job is scheduled on a uniprocessor, then
        [j] does not incur priority inversion. *)
    Corollary no_priority_inversion_when_hep_job_scheduled :
      forall t j',
        scheduled_at sched j' t ->
        hep_job j' j ->
        ~~ priority_inversion arr_seq sched j t.
    Proof.
      move=> t j' SCHED HEP.
      rewrite (priority_inversion_hep_job t j') //.
      by apply/negPn.
    Qed.

    (** From the above lemmas, we obtain a simplified definition of
        [priority_inversion] that holds on uniprocessors. *)
    Lemma uni_priority_inversion_P :
      forall t,
        reflect (exists2 j', scheduled_at sched j' t & ~~ hep_job j' j)
          (priority_inversion arr_seq sched j t).
    Proof.
      move=> t; apply: (iffP idP) => [PI | [j' SCHED' NHEP]].
      - have [j' SCHED'] := priority_inversion_scheduled_at t PI.
        by move: PI; rewrite (priority_inversion_hep_job t j').
      - apply/andP; split.
        + rewrite scheduled_jobs_at_iff //.
          apply: scheduled_job_at_neq => //.
          by apply/eqP => EQ; move: NHEP; rewrite EQ H_priority_is_reflexive.
        + by apply/hasP; exists j' => //; rewrite scheduled_jobs_at_iff.
    Qed.

  End Uniprocessors.

  (** ** Cumulative Priority Inversion *)

  (** We observe that the cumulative priority inversion (CPI) that job
      [j] incurs in an interval <<[t1, t2)>> can be split arbitrarily: is equal
      to the sum of CPI in an interval <<[t1, t_mid)>> and CPI in an interval
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

End PI.
