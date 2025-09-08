Require Export prosa.analysis.definitions.service_inversion.busy_prefix.
Require Export prosa.analysis.facts.busy_interval.pi.


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
        service inversion <<[t1, t)>> and <<[t, t2)>> for any <<t2 \in [t1, t3]>>.  *)
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
      rewrite (big_cat_nat LE1) //=; last by lia.
      by rewrite (big_cat_nat _ LE2) //= addnC -addnA leq_addr //=.
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

(** In the following, we prove that the cumulative service inversion
    in a busy interval prefix is bounded. *)
Section ServiceInversionIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of fully supply-consuming unit-supply
      uniprocessor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider an JLFP policy that indicates a higher-or-equal priority
      relation, and assume that the relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any uni-processor schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Next, allow for any work-bearing notion of job readiness ... *)
  Context `{!JobReady Job PState}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid.  *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (**  Next, we assume that the schedule respects the scheduling policy. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** In the following section, we prove that cumulative service
      inversion in a busy-interval prefix is necessarily caused by one
      lower-priority job. *)
  Section CumulativeServiceInversionFromOneJob.

    (** Consider any job [j] with a positive job cost. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Let <<[t1, t2)>> be a busy-interval prefix. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_prefix : busy_interval_prefix arr_seq sched j t1 t2.

    (** Consider a time instant [t : t <= t2] such that ... *)
    Variable t : instant.
    Hypothesis H_t_le_t2 : t <= t2.

    (** ... the cumulative service inversion is positive in <<[t1, t)>>. *)
    Hypothesis H_service_inversion_positive : 0 < cumulative_service_inversion arr_seq sched j t1 t.

    (** First, note that there is a lower-priority job that receives
        service at some time during the time interval <<[t1, t)>>. *)
    Local Lemma lower_priority_job_receives_service :
      exists (jlp : Job) (to : instant),
        t1 <= to < t
        /\ ~~ hep_job jlp j
        /\ receives_service_at sched jlp to.
    Proof.
      move: H_service_inversion_positive; rewrite sum_nat_gt0 filter_predT => /hasP [t' IN POS].
      rewrite mem_index_iota in IN; rewrite lt0b in POS.
      move: POS => /andP [NIN /hasP [jlp INlp LP]].
      exists jlp, t'.
      by rewrite IN LP.
    Qed.

    (** Then we prove that the service inversion incurred by job [j]
        can only be caused by _one_ lower priority job. *)
    Lemma cumulative_service_inversion_from_one_job :
      exists (jlp : Job),
        job_arrival jlp < t1
        /\ ~~ hep_job jlp j
        /\ cumulative_service_inversion arr_seq sched j t1 t = service_during sched jlp t1 t.
    Proof.
      have [jlp [to [NEQ [LP SERV]]]] := lower_priority_job_receives_service.
      exists jlp; split; last split => //.
      - apply: low_priority_job_arrives_before_busy_interval_prefix => //=.
        + by instantiate (1 := to); lia.
        + by apply service_at_implies_scheduled_at.
      - apply: eq_sum_seq => t'; rewrite mem_index_iota => NEQt' _.
        have [ZERO | POS] := unit_supply_proc_service_case H_unit_supply_proc_model sched jlp t'.
        + rewrite ZERO eqb0; apply/negP => /andP [_ /hasP [joo SERVoo LPoo]].
          have EQ : jlp = joo.
          { apply: only_one_pi_job => //=.
            * by instantiate (1 := to); lia.
            * by apply service_at_implies_scheduled_at.
            * by instantiate (1 := t'); lia.
            * apply: service_at_implies_scheduled_at.
              by apply: served_at_and_receives_service_consistent.
          }
          subst joo.
          apply served_at_and_receives_service_consistent in SERVoo.
          by move: SERVoo; rewrite /receives_service_at ZERO.
        + rewrite POS eqb1; apply/andP; split.
          * apply/negP => IN; apply served_at_and_receives_service_consistent in IN.
            have EQ: j = jlp by apply: only_one_job_receives_service_at_uni => //; rewrite /receives_service_at.
            by subst jlp; move: LP => /negP LP; apply: LP; apply H_priority_is_reflexive. 
          * apply/hasP; exists jlp; last by apply: LP.
            apply receives_service_and_served_at_consistent => //.
            by rewrite /receives_service_at POS.
    Qed.

  End CumulativeServiceInversionFromOneJob.

  (** In this section, we prove that, given a job [j] with a busy
      interval prefix <<[t1, t2)>> and a lower-priority job [jlp], the
      service of [jlp] within the busy interval prefix is bounded by
      the maximum non-preemptive segment of job [jlp]. *)
  Section ServiceOfLowPriorityJobIsBounded.

    (** Consider an arbitrary job [j] with positive cost ... *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_j_job_cost_positive : job_cost_positive j.

    (** ... and a lower-priority job [jlp]. *)
    Variable jlp : Job.
    Hypothesis H_jlp_arrives : arrives_in arr_seq jlp.
    Hypothesis H_jlp_lp : ~~ hep_job jlp j.

    (** Let <<[t1, t2)>> be a busy interval prefix of job [j]. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_prefix : busy_interval_prefix arr_seq sched j t1 t2.

    (** First, we consider a scenario when there is no preemption time
        inside of the busy interval prefix _but_ there is a time
        instant where [jlp] is scheduled. In this case, the cumulative
        service inversion of job [j] in the time interval <<[t1, t2)>>
        is bounded by the total service of job [jlp] received in the
        interval <<[t1, t2)>>. *)
    Local Lemma no_preemption_impl_service_inv_bounded :
      (forall t, t1 <= t < t2 -> ~~ preemption_time arr_seq sched t) ->
      (exists t, t1 <= t < t2 /\ scheduled_at sched jlp t) ->
      cumulative_service_inversion arr_seq sched j t1 t2 <= service_during sched jlp t1 t2.
    Proof.
      move=> NPT SCHED.
      rewrite [leqLHS]big_seq [leqRHS]big_seq; apply leq_sum => t.
      rewrite mem_index_iota => /andP [LE LT].
      have F : forall (b : bool) (n : nat), (b -> 0 < n) -> b <= n by lia.
      apply: F => /andP [ZE /hasP [h IN LPh]].
      have EQ: h = jlp; last by subst; apply: served_at_and_receives_service_consistent.
      apply: H_uniprocessor_proc_model.
      { by apply served_at_and_receives_service_consistent in IN; apply: service_at_implies_scheduled_at. }
      { move: SCHED => [t' [/andP [LE' LT'] SCHED]].
        unshelve apply: neg_pt_scheduled_continuous => //.
        - by generalize dependent t'; clear; lia.
        - by generalize dependent t; clear; lia.
      }
    Qed.

    (** In this section, we assume that [jlp] is scheduled inside of
        the busy interval prefix and prove that its service is bounded
        by [jlp]'s maximum non-preemptive segment. *)
    Section ServiceOfLPJobIsBounded.

      (** Consider an arbitrary time instant [t] such that [t <= t2]. *)
      Variables t : instant.
      Hypothesis H_t_le_t2 : t <= t2.

      (** Consider a second time instant [st] such that [t1 <= st < t]
          and [jlp] is scheduled at time [st]. *)
      Variable st : instant.
      Hypothesis H_t1_le_st_lt_t : t1 <= st < t.
      Hypothesis H_jlp_sched : scheduled_at sched jlp st.

      (** Consider a preemption point [σ] of job [jlp] such that ... *)
      Variable σ : duration.
      Hypothesis H_σ_is_pt : job_preemptable jlp σ.

      (** ... [σ] is greater than or equal to the service of [jlp] at
          time [t1] but exceeds the service by at most
          [job_max_nonpreemptive_segment jlp - ε]. *)
      Hypothesis H_σ_constrained :
        service sched jlp t1
        <= σ
        <= service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε).

      (** Next, we perform case analysis on whether job [jlp] has
          reached [σ] units of service by time [t]. *)

      (** First, assume that the service of [jlp] at time [t] is
          smaller than [σ]. In this case, it is easy to see from the
          hypothesis [H_σ_constrained] that the service received by
          [jlp] within time interval <<[t1, t)>> is bounded by
          [job_max_nonpreemptive_segment jlp - ε]. *)
      Local Lemma small_service_implies_bounded_service :
        service sched jlp t < σ ->
        service_during sched jlp t1 t <= job_max_nonpreemptive_segment jlp - ε.
      Proof.
        move => B; move_neq_up CO.
        have E : σ <= service sched jlp t1 + service_during sched jlp t1 t by lia.
        by move: B E; rewrite service_cat /service; lia.
      Qed.

      (** Next, assume that [σ <= service sched jlp t]. In this case,
          we can show that [jlp] is preempted after it reaches [σ]
          units of service and hence, again, the service during <<[t1, t)>>
          is bounded by [job_max_nonpreemptive_segment jlp - ε]. *)
      Local Lemma big_service_implies_bounded_service :
        σ <= service sched jlp t ->
        service_during sched jlp t1 t <= job_max_nonpreemptive_segment jlp - ε.
      Proof.
        rewrite -[service_during _ _ _ _ <= _](leq_add2l (service sched jlp t1)).
        rewrite leq_eqVlt => /orP [/eqP EQ|GT].
        { by rewrite service_cat; [ rewrite -EQ; move: H_σ_constrained => /andP [A B] | lia]. }
        exfalso.
        have [pt [LTpt EQ]] : exists pt, pt < t /\ service sched jlp pt = σ.
        { by apply exists_intermediate_service => //; apply unit_supply_is_unit_service. }
        have NPT : ~~ preemption_time arr_seq sched t1.
        { by eapply lower_priority_job_scheduled_implies_no_preemption_time
          with (t1 := t1) (t2:= t2) (t := st) (jlp := jlp) (j := j)=> //; lia. }
        have LEpt: t1 <= pt.
        { move_neq_up LEpt.
          have EQ1: service sched jlp t1 = σ.
          { apply/eqP; rewrite eqn_leq; apply/andP; split;
              first by move: H_σ_constrained => /andP [A B].
            by rewrite -EQ; apply: service_monotonic; lia. }
          have PT :  preemption_time arr_seq sched t1.
          { rewrite /preemption_time.
            have ->: scheduled_job_at arr_seq sched t1 = Some jlp.
            { apply/eqP; rewrite scheduled_job_at_scheduled_at => //.
              eapply lower_priority_job_continuously_scheduled
                with (t1 := t1) (t2:= t2) (t := st) (jlp := jlp) (j := j)=> //=; lia. }
            by rewrite EQ1.
          }
          by rewrite PT in NPT. }
        have [t' [NEQ' [SERV' SCHED']]] := kth_scheduling_time sched _ _ _ _ EQ GT.
        have PT : preemption_time arr_seq sched t'.
        { move: SCHED'; erewrite <-scheduled_job_at_scheduled_at => //.
          by rewrite /preemption_time; move => /eqP ->; rewrite SERV'. }
        move: H_jlp_lp => /negP LP2; apply: LP2.
        apply: scheduled_at_preemption_time_implies_higher_or_equal_priority => //.
        by move: NEQ' LEpt H_t_le_t2; clear; lia.
      Qed.

      (** Either way, the service of job [jlp] during the time
          interval <<[t1, t)>> is bounded by
          [job_max_nonpreemptive_segment jlp - ε]. *)
      Local Lemma lp_job_bounded_service_aux :
        service_during sched jlp t1 t <= job_max_nonpreemptive_segment jlp - ε.
      Proof.
        have [B|S] := leqP σ (service sched jlp t); last first.
        - by apply small_service_implies_bounded_service.
        - by apply big_service_implies_bounded_service.
      Qed.

    End ServiceOfLPJobIsBounded.

    (** Note that the preemption point [σ] assumed in the previous
        section always exists. *)
    Local Remark preemption_point_of_jlp_exists :
      exists σ,
        service sched jlp t1 <= σ <= service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε)
        /\ job_preemptable jlp σ.
    Proof.
      move: (proj2 (H_valid_model_with_bounded_nonpreemptive_segments) jlp H_jlp_arrives) =>[_ EXPP].
      have T: 0 <= service sched jlp t1 <= job_cost jlp.
      { by apply/andP; split=> [//|]; apply service_at_most_cost, unit_supply_is_unit_service => //. }
      by move: (EXPP (service sched jlp t1) T) => [pt [NEQ2 PP]]; exists pt.
    Qed.

    (** We strengthen the lemma [lp_job_bounded_service_aux] by
        removing the assumption that [jlp] is scheduled somewhere in
        the busy interval prefix. *)
    Lemma lp_job_bounded_service :
      forall t,
        t <= t2 ->
        service_during sched jlp t1 t <= job_max_nonpreemptive_segment jlp - ε.
    Proof.
      move=> t LT.
      have [ZE|POS] := posnP (service_during sched jlp t1 t); first by rewrite ZE.
      have [st [NEQ SCHED]] := cumulative_service_implies_scheduled _ _ _ _ POS.
      have [σ [EX PTσ]] := preemption_point_of_jlp_exists.
      by apply: lp_job_bounded_service_aux.
    Qed.

    (** Finally, we remove [jlp] from the RHS of the inequality by
        taking the maximum over all jobs that arrive before time [t1]. *)
    Lemma lp_job_bounded_service_max :
      forall t,
        t <= t2 ->
        service_during sched jlp t1 t <= max_lp_nonpreemptive_segment arr_seq j t1.
    Proof.
      move=> t LT.
      have [ZE|POS] := posnP (service_during sched jlp t1 t); first by rewrite ZE.
      have [st [NEQ SCHED]] := cumulative_service_implies_scheduled _ _ _ _ POS.
      rewrite (leqRW (lp_job_bounded_service _ _)) //.
      rewrite /max_lp_nonpreemptive_segment -(leqRW (leq_bigmax_cond_seq _ _ _ jlp _ _)) //.
      { apply: arrived_between_implies_in_arrivals => //.
        apply/andP; split => //.
        by (apply: low_priority_job_arrives_before_busy_interval_prefix; try apply: H_busy_prefix) => //; lia.
      }
      { by rewrite H_jlp_lp andTb; apply: scheduled_implies_positive_cost. }
    Qed.

  End ServiceOfLowPriorityJobIsBounded.

  (** Let [tsk] be any task to be analyzed. *)
  Variable tsk : Task.

  (** Let [blocking_bound] be a bound on the maximum length of a
      nonpreemptive segment of a lower-priority job. *)
  Variable blocking_bound : duration -> duration.

  (** We show that, if the maximum length of a nonpreemptive segment
      is bounded by the blocking bound, ... *)
  Hypothesis H_priority_inversion_is_bounded_by_blocking :
    forall j t1 t2,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      busy_interval_prefix arr_seq sched j t1 t2 ->
      max_lp_nonpreemptive_segment arr_seq j t1 <= blocking_bound (job_arrival j - t1).

  (** ... then the service inversion incurred by any job is bounded by
      the blocking bound. *)
  Lemma service_inversion_is_bounded :
    service_inversion_is_bounded_by arr_seq sched tsk blocking_bound.
  Proof.
    move=> j ARR TSK POS t1 t2 BUSY.
    rewrite -(leqRW (H_priority_inversion_is_bounded_by_blocking _ _ _ _ _ _ )) //.
    edestruct busy_interval_pi_cases as [CPI|PI]; (try apply BUSY) => //.
    { by rewrite (leqRW (cumul_service_inv_le_cumul_priority_inv _ _  _ _ _ _ _ _ _ _)) //. }
    { move: (PI) => /andP [_ /hasP [jlp INjlp LPjlp]].
      have SCHEDjlp : scheduled_at sched jlp t1 by erewrite <-scheduled_jobs_at_iff => //.
      have [NPT| [pt [/andP [LE1 LE2] [PT MIN]]]] := preemption_time_interval_case arr_seq sched t1 t2.
      { rewrite (leqRW (no_preemption_impl_service_inv_bounded j _ jlp _ _ _ _ _ )) //.
        - by apply: lp_job_bounded_service_max.
        - by exists t1; split => //; apply/andP; split; [ | move: BUSY => [T _]]; lia. }
      { have LEQ : cumulative_service_inversion arr_seq sched j t1 t2
                   <= cumulative_service_inversion arr_seq sched j t1 pt.
        { have [LE|WF] := leqP t2 pt.
          { by rewrite (leqRW (service_inversion_widen arr_seq sched j t1 _ _ pt _ _ )) => //. }
          { rewrite (service_inversion_cat _ _ _ _ _ pt) //
                    -{2}[_ _ _ j t1 pt]addn0 leq_add2l
                    (leqRW (cumul_service_inv_le_cumul_priority_inv _ _ _ _ _ _ _ _ _ _))//  leqn0.
            rewrite /cumulative_priority_inversion big_nat_cond; apply/eqP; apply big1 => t /andP [NEQ3 _]; apply/eqP.
            by rewrite eqb0; apply: no_priority_inversion_after_preemption_point => //; lia. } }
        rewrite (leqRW LEQ) (leqRW (no_preemption_impl_service_inv_bounded j _ jlp _ _ _ _ _ )) //; clear LEQ.
        { by apply: lp_job_bounded_service_max => //; lia. }
        { move=> t /andP [NEQ1 NEQ2]; apply/negP => PTt.
          by specialize (MIN _ NEQ1 PTt); move: MIN NEQ2; clear; lia. }
        { exists t1; split => //.
          apply/andP; split => //.
          move_neq_up LE; have EQ: pt = t1; [by lia | subst].
          eapply no_preemption_time_before_pi with (t := t1) in PI => //.
          - by rewrite PT in PI.
          - by move: LE2; clear; lia.
          - by clear; lia. }
      }
    }
  Qed.

End ServiceInversionIsBounded.
