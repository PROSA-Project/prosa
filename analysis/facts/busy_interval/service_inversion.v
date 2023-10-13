Require Export prosa.model.task.arrival.curves.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.analysis.definitions.service_inversion.pred.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.facts.model.task_schedule.
Require Export prosa.analysis.facts.busy_interval.pi_bound.
Require Export prosa.model.schedule.work_conserving.

(** * Service Inversion Lemmas *)
(** In this section, we prove a few lemmas about service inversion. *)
Section ServiceInversion.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of fully supply-consuming uniprocessor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any uni-processor schedule of this arrival sequence... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after
      completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** In this section, we prove a few basic lemmas about priority inversion. *)
  Section BasicLemmas.

    (** Consider an JLDP policy that indicates a higher-or-equal
        priority relation, and assume that the relation is
        reflexive. *)
    Context {JLDP : JLDP_policy Job}.
    Hypothesis H_priority_is_reflexive : reflexive_priorities JLDP.

    (** First, we show that a blackout at a time instant [t] implies
        that there is no service inversion at time [t]. *)
    Lemma blackout_implies_no_service_inversion :
      forall (j : Job) (t : instant),
        is_blackout sched t ->
        ~~ service_inversion arr_seq sched j t.
    Proof.
      move=> j t SUP.
      apply/negP => /andP [_ /hasP [s IN LP]].
      move: (SUP) => /negP NSUP; apply: NSUP.
      by apply: receives_service_implies_has_supply.
    Qed.

    (** Similarly, there is no service inversion at an idle time instant. *)
    Lemma idle_implies_no_service_inversion :
      forall (j : Job) (t : instant),
        is_idle arr_seq sched t ->
        ~~ service_inversion arr_seq sched j t.
    Proof.
      move=> j t IDLE; rewrite /service_inversion.
      rewrite negb_and negbK; apply/orP; right.
      apply/hasPn => [s A].
      apply served_at_and_receives_service_consistent in A.
      exfalso.
      by apply/negP; first apply: no_service_received_when_idle => //.
    Qed.

    (** Next, we prove that if a job [j] receives service at time [t],
        job [j] does not incur service inversion at time [t].  *)
    Lemma receives_service_implies_no_service_inversion :
      forall (j : Job) (t : instant),
        receives_service_at sched j t ->
        ~~ service_inversion arr_seq sched j t.
    Proof.
      move=> j t RSERV; apply/negP => /andP [_ /hasP [s IN LP]].
      have EQ: j = s by apply: only_one_job_receives_service_at_uni => //.
      subst; move: LP => /negP NHEP; apply: NHEP.
      by apply H_priority_is_reflexive.
    Qed.

    (** We show that cumulative service inversion received during an
        interval <<[t1, t2)>> can be split into the sum of cumulative
        service inversion <<[t1, t)>> and <<[t, t2)>> for any <<t2 \in
        [t1, t3]>>.  *)
    Lemma service_inversion_cat :
      forall (j : Job) (t1 t2 t : instant),
        t1 <= t ->
        t <= t2 ->
        cumulative_service_inversion arr_seq sched j t1 t2
        = cumulative_service_inversion arr_seq sched j t1 t
          + cumulative_service_inversion arr_seq sched j t t2.
    Proof. by move=> j t1 t2 t LE1 LE2; rewrite -big_cat_nat //=. Qed.

    (** Next, we show that cumulative service inversion on an interval
        <<[al, ar)>> is bounded by the cumulative service inversion on
        an interval <<[bl,br)>> if <<[al,ar)>> ⊆ <<[bl,br)>>. *)
    Lemma service_inversion_widen :
      forall (j : Job) (al ar bl br : instant),
        bl <= al ->
        ar <= br ->
        cumulative_service_inversion arr_seq sched j al ar
        <= cumulative_service_inversion arr_seq sched j bl br.
    Proof.
      move=> j al ar bl br LE1 LE2.
      rewrite /cumulative_service_inversion.
      have [NEQ1|NEQ1] := leqP al ar; last by rewrite big_geq //.
      rewrite (big_cat_nat _ _ _ LE1) //=; last by lia.
      by rewrite (big_cat_nat _ _ _ _ LE2) //= addnC -addnA leq_addr //=.
    Qed.

  End BasicLemmas.

  (** In the following section, we prove one rewrite rule about
      service inversion. *)
  Section ServiceInversionRewrite.

    (** Consider a reflexive JLDP policy. *)
    Context {JLDP : JLDP_policy Job}.
    Hypothesis H_priority_is_reflexive : reflexive_priorities JLDP.

    (** Consider a time instant [t] ... *)
    Variable t : instant.

    (** ... and assume that there is supply at [t]. *)
    Hypothesis H_supply : has_supply sched t.

    (** Consider two (not necessarily distinct) jobs [j] and [j'] and
        assume that job [j] is scheduled at time [t]. *)
    Variables j j' : Job.
    Hypothesis H_sched : scheduled_at sched j t.

    (** Then the predicate "is there service inversion for job [j'] at
        time [t]?" is equal to the predicate "is job [j] has lower
        priority than job [j']?" *)
    Lemma service_inversion_supply_sched :
      service_inversion arr_seq sched j' t = ~~ hep_job_at t j j'.
    Proof.
      have RSERV : receives_service_at sched j t by apply ideal_progress_inside_supplies.
      apply/idP/idP.
      { move => /andP [IN /hasP [s SE LP]].
        have EQj: s = j by apply: only_one_job_receives_service_at_uni.
        by subst. }
      { move => NHEP; apply/andP; split.
        - move: NHEP; apply contra => SERV.
          have EQj: j = j' by apply: only_one_job_receives_service_at_uni.
          by subst; apply H_priority_is_reflexive.
        - apply/hasP; exists j => //.
          by apply: receives_service_and_served_at_consistent. }
    Qed.

  End ServiceInversionRewrite.

  (** In the last section, we prove that cumulative service inversion
      is bounded by cumulative priority inversion. *)
  Section PriorityInversion.

    (** Consider a reflexive JLFP policy.

        Note that, unlike the other sections, this section assumes a
        JLFP policy. This is due to the fact that priority inversion
        is defined in terms of JLFP policies. This is not a
        fundamental assumption and may be relaxed in the future. *)
    Context {JLFP : JLFP_policy Job}.
    Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

    (** We prove that service inversion implies priority inversion ... *)
    Lemma service_inv_implies_priority_inv :
      forall (j : Job) (t : instant),
        service_inversion arr_seq sched j t ->
        priority_inversion arr_seq sched j t.
    Proof.
      move=> j t.
      move=> /andP [NSERV /hasP [s IN LP]]; apply/andP; split.
      { apply/negP => INj; rewrite scheduled_jobs_at_iff in INj => //.
        have EQ : s = j.
        { apply: H_uniprocessor_proc_model => //.
          by eapply service_at_implies_scheduled_at, served_at_and_receives_service_consistent. }
        by subst; move: LP => /negP LP; apply: LP; apply H_priority_is_reflexive. }
      { apply/hasP; exists s => //.
        rewrite scheduled_jobs_at_iff => //.
        by apply service_at_implies_scheduled_at; apply: served_at_and_receives_service_consistent. }
    Qed.

    (** ... and, as a corollary, it is easy to see that cumulative
        service inversion is bounded by cumulative priority
        inversion. *)
    Corollary cumul_service_inv_le_cumul_priority_inv :
      forall (j : Job) (t1 t2 : instant),
        cumulative_service_inversion arr_seq sched j t1 t2
        <= cumulative_priority_inversion arr_seq sched j t1 t2.
    Proof.
      move=> j t1 t2; apply leq_sum => t _.
      have L : forall (a b : bool), (a -> b) -> a <= b by clear; move => [] [].
      by apply L, service_inv_implies_priority_inv.
    Qed.

  End PriorityInversion.

End ServiceInversion.
