Require Export prosa.analysis.facts.interference.
Require Export prosa.analysis.abstract.IBF.supply_task.
Require Export prosa.analysis.facts.busy_interval.service_inversion.

(** * JLFP Instantiation of Interference and Interfering Workload for Restricted-Supply Uniprocessor *)
(** In this module we instantiate functions Interference and
    Interfering Workload for the restricted-supply uni-processor
    schedulers with an arbitrary JLFP-policy that satisfies the
    sequential-tasks hypothesis. We also prove equivalence of
    Interference and Interfering Workload to the more conventional
    notions of service or workload. *)
Section JLFPInstantiation.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of fully supply-consuming unit-supply
      uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider any valid arrival sequence with consistent arrivals... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any valid uni-processor schedule of this arrival sequence... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** * Interference and Interfering Workload *)
  (** In the following, we introduce definitions of interference and
      interfering workload. *)

  (** ** Instantiation of Interference *)

  (** We say that job [j] incurs interference at time [t] iff it
      cannot execute due to (1) the lack of supply at time [t], (2)
      due to service inversion (i.e., a lower-priority job receiving
      service at [t]), or higher-or-equal-priority job receiving
      service. *)
  #[local] Instance rs_jlfp_interference : Interference Job :=
    {
      interference (j : Job) (t : instant) :=
        is_blackout sched t
        || service_inversion arr_seq sched j t
        || another_hep_job_interference arr_seq sched j t
    }.

  (** ** Instantiation of Interfering Workload *)

  (** The interfering workload, in turn, is defined as the sum of the
      blackout predicate, service inversion predicate, and interfering
      workload of jobs with higher or equal priority. *)
  #[local] Instance rs_jlfp_interfering_workload : InterferingWorkload Job :=
    {
      interfering_workload (j : Job) (t : instant) :=
        is_blackout sched t
        + service_inversion arr_seq sched j t
        + other_hep_jobs_interfering_workload arr_seq j t
    }.

  (** ** Equivalences *)

  (** In this section we prove useful equivalences between the
      definitions obtained by instantiation of definitions from the
      Abstract RTA module (interference and interfering workload) and
      definitions corresponding to the conventional concepts.

      As it was mentioned previously, instantiated functions of
      interference and interfering workload usually do not have any
      useful lemmas about them. However, it is possible to prove their
      equivalence to the more conventional notions like service or
      workload. Next we prove the equivalence between the
      instantiations and conventional notions. *)
  Section Equivalences.

    (** We prove that we can split cumulative interference into three
        parts: (1) blackout time, (2) cumulative service inversion,
        and (3) cumulative interference from jobs with higher or equal
        priority. *)
    Lemma cumulative_interference_split :
      forall j t1 t2,
        cumulative_interference j t1 t2
        = blackout_during sched t1 t2
          + cumulative_service_inversion arr_seq sched j t1 t2
          + cumulative_another_hep_job_interference arr_seq sched j t1 t2.
    Proof.
      rewrite /cumulative_interference /cumul_cond_interference /rs_jlfp_interference /cond_interference /interference.
      move=> j t1 t2; rewrite -big_split //= -big_split //=.
      apply/eqP; rewrite eqn_leq; apply/andP; split; rewrite leq_sum//; move=> t _.
      { by case is_blackout, service_inversion, another_hep_job_interference. }
      { have [BL|SUP] := blackout_or_supply sched t.
        { rewrite BL //= -addnA addnC addn1 ltnS leqn0 addn_eq0.
          by apply/andP; split;
            [rewrite eqb0 blackout_implies_no_service_inversion
            | rewrite eqb0 no_hep_job_interference_without_supply]. }
        { rewrite /is_blackout SUP //= add0n.
          have [IDLE|[s SCHEDs]] := scheduled_at_cases arr_seq ltac:(eauto) sched ltac:(eauto) ltac:(eauto) t.
          { by rewrite -[service_inversion _ _ _ _]negbK idle_implies_no_service_inversion //=. }
          { rewrite (service_inversion_supply_sched _ _ _ _ _ _ _ _ _ _ s) //
                    (interference_ahep_def _ _ _ _ _ _ _ _ _ _ s) //
                    /another_hep_job.
            have [EQ|NEQ] := eqVneq s j.
            { by rewrite andbF orbF addn0. }
            { by unfold hep_job_at, JLFP_to_JLDP, hep_job; rewrite andbT; case (JLFP s j) => //. }
          }
        }
      }
    Qed.

    (** Similarly, we prove that we can split cumulative interfering
        workload into three parts: (1) blackout time, (2) cumulative
        service inversion, and (3) cumulative interfering workload
        from jobs with higher or equal priority. *)
    Lemma cumulative_interfering_workload_split :
      forall j t1 t2,
        cumulative_interfering_workload j t1 t2
        = blackout_during sched t1 t2
          + cumulative_service_inversion arr_seq sched j t1 t2
          + cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2.
    Proof.
      by move=> j t1 t2; rewrite -big_split //= -big_split //=.
    Qed.

    (** Let <<[t1, t2)>> be a time interval and let [j] be any job of
        task [tsk] that is not completed by time [t2]. Then cumulative
        interference received due jobs of other tasks executing can be
        bounded by the sum of the cumulative service inversion of job
        [j] and the cumulative interference incurred by task [tsk] due
        to other tasks. *)
    Lemma cumulative_task_interference_split :
      forall j t1 t2,
        arrives_in arr_seq j ->
        job_of_task tsk j ->
        ~~ completed_by sched j t2 ->
        cumul_cond_interference (nonself_intra arr_seq sched) j t1 t2
        <= cumulative_service_inversion arr_seq sched j t1 t2
          + cumulative_another_task_hep_job_interference arr_seq sched j t1 t2.
    Proof.
      move=> j t1 R ARR TSK NCOMPL.
      rewrite /cumul_task_interference /cumul_cond_interference.
      rewrite -big_split //= big_seq_cond [leqRHS]big_seq_cond.
      apply leq_sum => t /andP [IN _].
      rewrite /cond_interference /nonself /interference /rs_jlfp_interference /nonself_intra.
      have [SUP|NOSUP] := boolP (has_supply sched t); last first.
      { by move: (NOSUP); rewrite /is_blackout => -> //=; rewrite andbT andbF //. }
      { move: (SUP); rewrite /is_blackout => ->; rewrite andbT //=.
        have [IDLE|[s SCHEDs]] := scheduled_at_cases arr_seq ltac:(eauto) sched ltac:(eauto) ltac:(eauto) t.
        { rewrite /nonself.
          by rewrite -[service_inversion _ _ _ _]negbK
                     idle_implies_no_service_inversion //;
             rewrite_neg no_hep_job_interference_when_idle;
             rewrite_neg no_hep_task_interference_when_idle; rewrite andbF. }
        { rewrite /nonself; move: (TSK) => /eqP ->.
          erewrite task_served_at_eq_job_of_task => //; erewrite service_inversion_supply_sched => //.
          erewrite interference_ahep_def => //.
          erewrite interference_athep_def => //.
          rewrite /another_hep_job /another_task_hep_job.
          have [EQj|NEQj] := eqVneq s j.
          { by subst; rewrite /job_of_task; move: TSK => /eqP => ->; rewrite H_priority_is_reflexive eq_refl. }
          have [/eqP EQt|NEQt] := eqVneq (job_task s) (job_task j).
          { rewrite /job_of_task; move: TSK => /eqP <-; rewrite EQt.
            by apply/eqP; rewrite andbF andFb addn0 //=. }
          { unfold hep_job_at, JLFP_to_JLDP, hep_job.
            by rewrite /job_of_task; move: TSK => /eqP <-; rewrite NEQt //= andbT; case: JLFP. }
        }
      }
    Qed.

    (** We also show that the cumulative intra-supply interference can
        be split into the sum of the cumulative service inversion and
        cumulative interference incurred by the job due to other
        higher-or-equal priority jobs. *)
    Lemma cumulative_intra_interference_split :
      forall j t1 t2,
        cumul_cond_interference (fun (_j : Job) (t : instant) => has_supply sched t) j t1 t2
        <= cumulative_service_inversion arr_seq sched j t1 t2
          + cumulative_another_hep_job_interference arr_seq sched j t1 t2.
    Proof.
      move=> j t1 t2.
      rewrite /cumul_cond_interference -big_split //= big_seq_cond [leqRHS]big_seq_cond.
      apply leq_sum => t /andP [IN _].
      rewrite /cond_interference /nonself /interference /rs_jlfp_interference.
      have [SUP|NOSUP] := boolP (has_supply sched t); last first.
      { by move: (NOSUP); rewrite /is_blackout => -> //=; rewrite andbT andbF //. }
      { move: (SUP); rewrite /is_blackout => ->; rewrite andTb //=.
        have L : forall (a b : bool), a || b <= a + b by clear => [] [] [].
        by apply L. }
    Qed.

    (** In this section, we prove that the (abstract) cumulative
        interfering workload due to other higher-or-equal priority
        jobs is equal to the conventional workload (from other
        higher-or-equal priority jobs). *)
    Section InstantiatedWorkloadEquivalence.

      (** Let <<[t1, t2)>> be any time interval. *)
      Variables t1 t2 : instant.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.

      (** The cumulative interfering workload (w.r.t. [j]) due to
          other higher-or-equal priority jobs is equal to the
          conventional workload from other higher-or-equal priority
          jobs. *)
      Lemma cumulative_iw_hep_eq_workload_of_ohep :
        cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2
        = workload_of_other_hep_jobs arr_seq j t1 t2.
      Proof.
        rewrite /cumulative_other_hep_jobs_interfering_workload /workload_of_other_hep_jobs.
        case NEQ: (t1 < t2); last first.
        { move: NEQ => /negP /negP; rewrite -leqNgt => NEQ.
          rewrite big_geq // /arrivals_between big_geq //.
          by rewrite /workload_of_jobs big_nil. }
        { interval_to_duration t1 t2 k.
          elim: k => [|k IHk].
          - rewrite !addn0 big_geq// /arrivals_between big_geq//.
            by rewrite /workload_of_jobs big_nil.
          - rewrite addnS big_nat_recr //=; last by rewrite leq_addr.
            rewrite IHk /arrivals_between big_nat_recr //=.
            + by rewrite /workload_of_jobs big_cat.
            + by rewrite leq_addr. }
      Qed.

    End InstantiatedWorkloadEquivalence.

    (** In this section we prove that the abstract definition of busy
        interval is equivalent to the conventional, concrete
        definition of busy interval for JLFP scheduling. *)
    Section BusyIntervalEquivalence.

      (** In order to avoid confusion, we denote the notion of a quiet
          time in the _classical_ sense as [quiet_time_cl], and the
          notion of quiet time in the _abstract_ sense as
          [quiet_time_ab]. *)
      Let quiet_time_cl := classical.quiet_time arr_seq sched.
      Let quiet_time_ab := abstract.definitions.quiet_time sched.

      (** Same for the two notions of a busy interval prefix ... *)
      Let busy_interval_prefix_cl := classical.busy_interval_prefix arr_seq sched.
      Let busy_interval_prefix_ab := abstract.definitions.busy_interval_prefix sched.

      (** ... and the two notions of a busy interval. *)
      Let busy_interval_cl := classical.busy_interval arr_seq sched.
      Let busy_interval_ab := abstract.definitions.busy_interval sched.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.

      (** To show the equivalence of the notions of busy intervals, we
          first show that the notions of quiet time are also
          equivalent. *)

      (** First, we show that the classical notion of quiet time
          implies the abstract notion of quiet time. *)
      Lemma quiet_time_cl_implies_quiet_time_ab :
        forall t, quiet_time_cl j t -> quiet_time_ab j t.
      Proof.
        have zero_is_quiet_time: forall j, quiet_time_cl j 0.
        { by move => jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0. }
        move=> t QT; apply/andP; split; last first.
        { rewrite negb_and negbK; apply/orP.
          by case ARR: (arrived_before j t); [right | left]; [apply QT | ]. }
        { erewrite cumulative_interference_split, cumulative_interfering_workload_split; rewrite eqn_add2l.
          rewrite cumulative_i_ohep_eq_service_of_ohep //.
          rewrite //= cumulative_iw_hep_eq_workload_of_ohep eq_sym; apply/eqP.
          apply all_jobs_have_completed_equiv_workload_eq_service => //.
          move => j0 IN HEP; apply QT.
          - by apply in_arrivals_implies_arrived in IN.
          - by move: HEP => /andP [HEP HP].
          - by apply in_arrivals_implies_arrived_between in IN.
        }
      Qed.

      (** And vice versa, the abstract notion of quiet time implies
          the classical notion of quiet time. *)
      Lemma quiet_time_ab_implies_quiet_time_cl :
        forall t, quiet_time_ab j t -> quiet_time_cl j t.
      Proof.
        have zero_is_quiet_time: forall j, quiet_time_cl j 0.
        { by move => jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0. }
        move => t /andP [T0 T1] jhp ARR HP ARB.
        eapply all_jobs_have_completed_equiv_workload_eq_service with
          (P := fun jhp => hep_job jhp j) (t1 := 0) (t2 := t) => //.
        erewrite service_of_jobs_case_on_pred with (P2 := fun j' => j' != j).
        erewrite workload_of_jobs_case_on_pred with (P' := fun j' => j' != j) => //.
        replace ((fun j0 : Job => hep_job j0 j && (j0 != j))) with (another_hep_job^~j); last by rewrite /another_hep_job.
        rewrite -/(service_of_other_hep_jobs arr_seq sched j 0 t) -cumulative_i_ohep_eq_service_of_ohep //.
        rewrite -/(workload_of_other_hep_jobs arr_seq j 0 t) -cumulative_iw_hep_eq_workload_of_ohep //.
        move: T1; rewrite negb_and => /orP [NA | /negPn COMP].
        { have PRED__eq: {in arrivals_between arr_seq 0 t, (fun j__copy : Job => hep_job j__copy j && ~~ (j__copy != j)) =1 pred0}.
          { move => j__copy IN; apply negbTE.
            rewrite negb_and; apply/orP; right; apply/negPn/eqP => EQ; subst j__copy.
            move: NA => /negP CONTR; apply: CONTR.
            by apply in_arrivals_implies_arrived_between in IN. }
          erewrite service_of_jobs_equiv_pred with (P2 := pred0) => [|//].
          erewrite workload_of_jobs_equiv_pred with (P' := pred0) => [|//].
          move: T0; erewrite cumulative_interference_split, cumulative_interfering_workload_split; rewrite eqn_add2l => /eqP EQ.
          rewrite EQ; clear EQ; apply/eqP; rewrite eqn_add2l.
          by erewrite workload_of_jobs_pred0, service_of_jobs_pred0.
        }
        { have PRED__eq: {in arrivals_between arr_seq 0 t, (fun j0 : Job => hep_job j0 j && ~~ (j0 != j)) =1 eq_op j}.
          { move => j__copy IN.
            replace (~~ (j__copy != j)) with (j__copy == j); last by case: (j__copy == j).
            rewrite eq_sym; destruct (j == j__copy) eqn:EQ; last by rewrite Bool.andb_false_r.
            by move: EQ => /eqP EQ; rewrite Bool.andb_true_r; apply/eqP; rewrite eqb_id; subst. }
          erewrite service_of_jobs_equiv_pred with (P2 := eq_op j) => [|//].
          erewrite workload_of_jobs_equiv_pred with (P' := eq_op j) => [|//].
          move: T0; erewrite cumulative_interference_split, cumulative_interfering_workload_split; rewrite eqn_add2l => /eqP EQ.
          rewrite EQ; clear EQ; apply/eqP; rewrite eqn_add2l.
          apply/eqP; eapply all_jobs_have_completed_equiv_workload_eq_service with
            (P := eq_op j) (t1 := 0) (t2 := t) => //.
          { by move => j__copy _ /eqP EQ; subst j__copy. }
        }
      Qed.

      (** The equivalence trivially follows from the lemmas above. *)
      Corollary instantiated_quiet_time_equivalent_quiet_time :
        forall t,
          quiet_time_cl j t <-> quiet_time_ab j t.
      Proof.
        move => ?; split.
        - by apply quiet_time_cl_implies_quiet_time_ab.
        - by apply quiet_time_ab_implies_quiet_time_cl.
      Qed.

      (** Based on that, we prove that the concept of a busy-interval
          prefix obtained by instantiating the abstract definition of
          busy-interval prefix coincides with the conventional
          definition of busy-interval prefix. *)
      Lemma instantiated_busy_interval_prefix_equivalent_busy_interval_prefix :
        forall t1 t2, busy_interval_prefix_cl j t1 t2 <-> busy_interval_prefix_ab j t1 t2.
      Proof.
        move => t1 t2; split.
        { move => [NEQ [QTt1 [NQT REL]]].
          split=> [//|]; split.
          - by apply instantiated_quiet_time_equivalent_quiet_time in QTt1.
          - by move => t NE QT; eapply NQT; eauto 2; apply instantiated_quiet_time_equivalent_quiet_time.
        }
        { move => [/andP [NEQ1 NEQ2] [QTt1 NQT]].
          split; [ | split; [ |split] ].
          - by apply leq_ltn_trans with (job_arrival j).
          - by eapply instantiated_quiet_time_equivalent_quiet_time.
          - by move => t NEQ QT; eapply NQT; eauto 2; eapply instantiated_quiet_time_equivalent_quiet_time in QT.
          - by apply/andP.
        }
      Qed.

      (** Similarly, we prove that the concept of busy interval
          obtained by instantiating the abstract definition of busy
          interval coincides with the conventional definition of busy
          interval. *)
      Lemma instantiated_busy_interval_equivalent_busy_interval :
        forall t1 t2, busy_interval_cl j t1 t2 <-> busy_interval_ab j t1 t2.
      Proof.
        move => t1 t2; split.
        { move => [PREF QTt2]; split.
          - by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
          - by eapply instantiated_quiet_time_equivalent_quiet_time in QTt2.
        }
        { move => [PREF QTt2]; split.
          - by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
          - by eapply instantiated_quiet_time_equivalent_quiet_time.
        }
      Qed.

      (** For the sake of proof automation, we note the frequently needed
          special case of an abstract busy window implying the existence of a
          classic quiet time. *)
      Fact abstract_busy_interval_classic_quiet_time :
        forall t1 t2,
          busy_interval_ab j t1 t2 -> quiet_time_cl j t1.
      Proof.
        by move=> ? ? /instantiated_busy_interval_equivalent_busy_interval [[_ [? _]] _].
      Qed.

      (** Also for automation, we note a similar fact about classic busy-window prefixes. *)
      Fact abstract_busy_interval_classic_busy_interval_prefix :
        forall t1 t2,
          busy_interval_ab j t1 t2 -> busy_interval_prefix_cl j t1 t2.
      Proof. by move=> ? ? /instantiated_busy_interval_equivalent_busy_interval [+ _]. Qed.

    End BusyIntervalEquivalence.

  End Equivalences.

  (** In this section we prove some properties about the interference
      and interfering workload as defined in this file. *)
  Section I_IW_correctness.

    (** Consider work-bearing readiness. *)
    Context `{!JobReady Job PState}.
    Hypothesis H_work_bearing_readiness : work_bearing_readiness arr_seq sched.

    (** Assume that the schedule is valid and work-conserving. *)
    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    (** Note that we differentiate between abstract and classical
        notions of work-conserving schedule ... *)
    Let work_conserving_ab := definitions.work_conserving arr_seq sched.
    Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

    (** ... as well as notions of busy interval prefix. *)
    Let busy_interval_prefix_ab := definitions.busy_interval_prefix sched.
    Let busy_interval_prefix_cl := classical.busy_interval_prefix arr_seq sched.

    (** We assume that the schedule is a work-conserving schedule in
        the _classical_ sense, and later prove that the hypothesis
        about abstract work-conservation also holds. *)
    Hypothesis H_work_conserving : work_conserving_cl.

    (** In this section, we prove the correctness of interference
        inside the busy interval, i.e., we prove that if interference
        for a job is [false] then the job is scheduled and vice versa.
        This property is referred to as abstract work conservation. *)
    Section Abstract_Work_Conservation.

      (** Consider a job [j] that is in the arrival sequence
          and has a positive job cost. *)
      Variable j : Job.
      Hypothesis H_arrives : arrives_in arr_seq j.
      Hypothesis H_job_cost_positive : 0 < job_cost j.

      (** Let the busy interval of the job be <<[t1, t2)>>. *)
      Variable t1 t2 : instant.
      Hypothesis H_busy_interval_prefix : busy_interval_prefix_ab j t1 t2.

      (** Consider a time [t] inside the busy interval of the job. *)
      Variable t : instant.
      Hypothesis H_t_in_busy_interval : t1 <= t < t2.

      (** First, we note that, similarly to the ideal uni-processor
          case, there is no idle time inside of a busy interval. That
          is, there is a job scheduled at time [t]. *)
      Local Lemma busy_implies_not_idle :
        exists j, scheduled_at sched j t.
      Proof.
        have [IDLE|[s SCHEDs]] := scheduled_at_cases arr_seq ltac:(eauto) sched ltac:(eauto) ltac:(eauto) t; last by (exists s).
        exfalso; eapply instant_t_is_not_idle in IDLE => //.
        by apply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
      Qed.

      (** We then prove that if interference is [false] at a time [t]
          then the job is scheduled. *)
      Lemma not_interference_implies_scheduled :
        ~~ interference j t -> receives_service_at sched j t.
      Proof.
        rewrite !negb_or /another_hep_job_interference => /andP [/andP [HYP1 HYP2] /hasPn HYP3].
        move: HYP1; rewrite /is_blackout negbK => SUP; apply ideal_progress_inside_supplies => //.
        move: HYP2; rewrite negb_and negbK => /orP [SERV | /hasPn SI].
        { by apply service_at_implies_scheduled_at; apply: served_at_and_receives_service_consistent => //. }
        move: busy_implies_not_idle => [jo SCHED].
        have RSERV : receives_service_at sched jo t by apply ideal_progress_inside_supplies.
        have INRSERV : jo \in served_jobs_at arr_seq sched t by apply receives_service_and_served_at_consistent.
        move: (HYP3 _ INRSERV); rewrite negb_and => /orP [LP | EQ]; last first.
        - by move: EQ; rewrite negbK => /eqP EQ; subst jo.
        - by move: (SI _ INRSERV); rewrite LP.
      Qed.

      (** Conversely, if the job is scheduled at [t] then interference is [false]. *)
      Lemma scheduled_implies_no_interference :
        receives_service_at sched j t -> ~~ interference j t.
      Proof.
        move=> RSERV. apply/negP => /orP [/orP[BL|PINV] | INT].
        - by apply/negP; first apply: no_blackout_when_service_received.
        - by apply/negP; first apply: receives_service_implies_no_service_inversion.
        - move: INT; rewrite_neg @no_ahep_interference_when_served.
          by apply: receives_service_implies_has_supply.
      Qed.

    End Abstract_Work_Conservation.

    (** Using the above two lemmas, we can prove that abstract work
        conservation always holds for these instantiations of
        interference (I) and interfering workload (W). *)
    Corollary instantiated_i_and_w_are_coherent_with_schedule :
      work_conserving_ab.
    Proof.
      move => j t1 t2 t ARR POS BUSY NEQ; split.
      - by move=> G; apply: (not_interference_implies_scheduled j ARR POS); eauto 2; apply/negP.
      - by move=> SERV; apply/negP; apply: scheduled_implies_no_interference; eauto 2.
    Qed.

    (** Next, in order to prove that these definitions of interference
        and interfering workload are consistent with sequential tasks,
        we need to assume that the policy under consideration respects
        sequential tasks. *)
    Hypothesis H_policy_respects_sequential_tasks : policy_respects_sequential_tasks JLFP.

    (** We prove that these definitions of interference and
        interfering workload are consistent with sequential tasks. *)
    Lemma instantiated_interference_and_workload_consistent_with_sequential_tasks :
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk.
    Proof.
      move => j t1 t2 ARR /eqP TSK POS BUSY.
      eapply instantiated_busy_interval_equivalent_busy_interval in BUSY => //.
      eapply all_jobs_have_completed_equiv_workload_eq_service => //.
      move => s INs /eqP TSKs.
      move: (INs) => NEQ.
      eapply in_arrivals_implies_arrived_between in NEQ => //.
      move: NEQ => /andP [_ JAs].
      move: (BUSY) => [[ _ [QT [_ /andP [JAj _]]] _]].
      apply QT => //; first exact: in_arrivals_implies_arrived.
      apply H_policy_respects_sequential_tasks; first by rewrite  TSK TSKs.
      by apply leq_trans with t1; [lia |].
    Qed.

    (** Finally, we show that cumulative interference (I) never exceeds
        cumulative interfering workload (W). *)
    Lemma instantiated_i_and_w_no_speculative_execution :
      no_speculative_execution.
    Proof.
      move=> j t1.
      rewrite cumulative_interference_split cumulative_interfering_workload_split.
      rewrite leq_add2l cumulative_i_ohep_eq_service_of_ohep //=.
      rewrite cumulative_iw_hep_eq_workload_of_ohep.
      by apply service_of_jobs_le_workload => //.
    Qed.

  End I_IW_correctness.

End JLFPInstantiation.
