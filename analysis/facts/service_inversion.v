Require Export prosa.analysis.definitions.service_inversion.readiness_aware.

(** * Service Inversion Lemmas *)
(** In this section, we prove a few lemmas about service inversion. *)
(** Note that the service inversion used here is the readiness aware notion of service inversion. *)
Section ServiceInversion.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of fully supply-consuming uniprocessor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  Context `{!JobReady Job PState}.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any uni-processor schedule of this arrival sequence... *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Consider an JLFP policy that indicates a higher-or-equal
      priority relation, and assume that the relation is
      reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** In this section, we prove a few basic lemmas about service inversion. *)
  Section BasicLemmas.

    (** First, we show that a blackout at a time instant [t] implies
        that there is no service inversion at time [t]. *)
    Lemma blackout_implies_no_service_inversion :
      forall (j : Job) (t : instant),
        is_blackout sched t ->
        ~~ service_inversion arr_seq sched j t.
    Proof.
      move=> j t /negP SUP.
      apply/negP => /andP [_ /hasP [s IN LP]].
      apply: SUP.
      by apply: receives_service_implies_has_supply.
    Qed.

    (** Similarly, there is no service inversion at an idle time instant. *)
    Lemma idle_implies_no_service_inversion :
      forall (j : Job) (t : instant),
        is_idle arr_seq sched t ->
        ~~ service_inversion arr_seq sched j t.
    Proof.
      move=> j t IDLE; rewrite /service_inversion.
      rewrite negb_and ; apply/orP; right.
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
        service inversion <<[t1, t)>> and <<[t, t2)>> for any
        <<t2 ∈ [t1, t3]>>. *)
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

    (** Consider a time instant [t] ... *)
    Variable t : instant.

    (** ... and assume that there is supply at [t]. *)
    Hypothesis H_supply : has_supply sched t.

    (** Consider two (not necessarily distinct) jobs [j] and [j'] and
        assume that job [j] is scheduled at time [t]. *)
    Variables j j' : Job.
    Hypothesis H_sched : scheduled_at sched j' t.

    (** Then, if [j] incurs service inversion at [t], we know that [j'] has
        lower priority than [j]. *)
    Lemma service_inversion_supply_sched :
      service_inversion arr_seq sched j t -> ~~ hep_job j' j.
    Proof.
      have RSERV : receives_service_at sched j' t by apply ideal_progress_inside_supplies.
      move => /andP [IN /hasP [s SE LP]].
      have EQj: s = j' by apply: only_one_job_receives_service_at_uni.
      by subst.
    Qed.

  End ServiceInversionRewrite.

End ServiceInversion.

