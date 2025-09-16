Require Export prosa.analysis.facts.busy_interval.carry_in.
Require Export prosa.analysis.abstract.IBF.task.
Require Export prosa.analysis.facts.interference.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.
Require Export prosa.analysis.facts.model.ideal.priority_inversion.

(** * JLFP instantiation of Interference and Interfering Workload for ideal uni-processor. *)
(** In this module we instantiate functions Interference and
    Interfering Workload for ideal uni-processor schedulers with an
    arbitrary JLFP-policy that satisfies the sequential-tasks
    hypothesis. We also prove equivalence of Interference and
    Interfering Workload to the more conventional notions of service
    or workload. *)
Section JLFPInstantiation.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any ideal uni-processor schedule of this arrival
      sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after
      completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** We also assume that the policy respects sequential tasks,
      meaning that later-arrived jobs of a task don't have higher
      priority than earlier-arrived jobs of the same task. *)
  Hypothesis H_JLFP_respects_sequential_tasks :
    policy_respects_sequential_tasks JLFP.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** * Interference and Interfering Workload *)
  (** In the following, we introduce definitions of interference,
      interfering workload and a function that bounds cumulative
      interference. *)

  (** ** Instantiation of Interference *)

  (** Before we define the notion of interference, we need to recall
      the definition of priority inversion. We say that job [j] is
      incurring a priority inversion at time [t] if there exists a job
      with lower priority that executes at time [t]. In order to
      simplify things, we ignore the fact that according to this
      definition a job can incur priority inversion even before its
      release (or after completion). All such (potentially bad) cases
      do not cause problems, as each job is analyzed only within the
      corresponding busy interval where the priority inversion behaves
      in the expected way. *)

  (** We say that job [j] incurs interference at time [t] iff it
      cannot execute due to a higher-or-equal-priority job being
      scheduled, or if it incurs a priority inversion. *)
  #[local,program] Instance ideal_jlfp_interference : Interference Job :=
    {
      interference (j : Job) (t : instant) :=
        priority_inversion arr_seq sched j t
        || another_hep_job_interference arr_seq sched j t
    }.

  (** ** Instantiation of Interfering Workload *)

  (** The interfering workload, in turn, is defined as the sum of the
      priority inversion predicate and interfering workload of jobs
      with higher or equal priority. *)
  #[local,program] Instance ideal_jlfp_interfering_workload : InterferingWorkload Job :=
    {
      interfering_workload (j : Job) (t : instant) :=
        priority_inversion arr_seq sched j t
        + other_hep_jobs_interfering_workload arr_seq j t
    }.

  (** ** Equivalences *)
  (** In this section we prove useful equivalences between the
      definitions obtained by instantiation of definitions from the
      Abstract RTA module (interference and interfering workload) and
      definitions corresponding to the conventional concepts.

      Instantiated functions of interference and interfering workload
      usually do not have any useful lemmas about them. However, it is
      possible to prove their equivalence to the more conventional
      notions like service or workload. Next, we prove the equivalence
      between the instantiations and conventional notions as well as a
      few useful rewrite rules. *)
  Section Equivalences.

    (** In the following subsection, we prove properties of the
        introduced functions under the assumption that the schedule is
        idle. *)
    Section IdleSchedule.

      (** Consider a time instant [t] ... *)
      Variable t : instant.

      (** ... and assume that the schedule is idle at [t]. *)
      Hypothesis H_idle : ideal_is_idle sched t.

      (** We prove that in this case: ... *)

      (** ... there is no interference, ... *)
      Lemma no_interference_when_idle :
        forall j, ~~ interference j t.
      Proof.
        move => j; apply/negP.
        rewrite /interference /ideal_jlfp_interference => /orP [PI | HEPI].
        - have [j' schj'] : exists j' : Job, scheduled_at sched j' t
            by exact/priority_inversion_scheduled_at.
          exact: ideal_sched_implies_not_idle schj' H_idle.
        - by move: HEPI => /negPn; rewrite no_hep_job_interference_when_idle // is_idle_def //.
      Qed.

      (** ... as well as no interference for [tsk]. *)
      Lemma no_task_interference_when_idle :
        forall j, ~~ task_interference arr_seq sched j t.
      Proof.
        move=> j; rewrite /task_interference /cond_interference.
        by rewrite negb_and; apply/orP; right; apply no_interference_when_idle.
      Qed.

    End IdleSchedule.

    (** Next, we prove properties of the introduced functions under
        the assumption that the scheduler is not idle. *)
    Section ScheduledJob.

      (** Consider a job [j] of task [tsk]. In this subsection, job
          [j] is deemed to be the main job with respect to which the
          functions are computed. *)
      Variable j : Job.
      Hypothesis H_j_tsk : job_of_task tsk j.

      (** Consider a time instant [t]. *)
      Variable t : instant.

      (** In the next subsection, we consider a case when a job [j']
          from the same task (as job [j]) is scheduled. *)
      Section FromSameTask.

        (** Consider a job [j'] that comes from task [tsk] and is
            scheduled at time instant [t].  *)
        Variable j' : Job.
        Hypothesis H_j'_tsk : job_of_task tsk j'.
        Hypothesis H_j'_sched : scheduled_at sched j' t.

        (** Similarly, there is no task interference, since in order
            to incur the task interference, a job from a distinct task
            must be scheduled. *)
        Lemma task_interference_eq_false :
          ~~ task_interference arr_seq sched j t.
        Proof.
          apply/negP; move => /andP [+ _]; rewrite /nonself /task_scheduled_at.
          rewrite task_served_eq_task_scheduled //=; erewrite job_of_scheduled_task => //.
          move: H_j_tsk  H_j'_tsk; rewrite /job_of_task => /eqP -> /eqP ->.
          by rewrite eq_refl.
        Qed.

      End FromSameTask.

      (** In the next subsection, we consider a case when a job [j']
          from a task other than [j]'s task is scheduled. *)
      Section FromDifferentTask.

        (** Consider a job [j'] that _does_ _not_ comes from task
            [tsk] and is scheduled at time instant [t].  *)
        Variable j' : Job.
        Hypothesis H_j'_not_tsk : ~~ job_of_task tsk j'.
        Hypothesis H_j'_sched : scheduled_at sched j' t.

        (** Hence, if we assume that [j'] has higher-or-equal priority, ... *)
        Hypothesis H_j'_hep : hep_job j' j.

        (** Moreover, in this case, task [tsk] also incurs interference. *)
        Lemma sched_athep_implies_task_interference :
          task_interference arr_seq sched j t.
        Proof.
          apply/andP; split.
          - rewrite /nonself task_served_eq_task_scheduled => //.
            apply: job_of_other_task_scheduled => //.
            by move: H_j_tsk => /eqP -> .
          - apply/orP; right.
            apply/hasP; exists j'.
            + by apply scheduled_at_implies_in_served_at => //.
            + rewrite another_hep_job_diff_task // same_task_sym.
              exact: (diff_task tsk).
        Qed.

      End FromDifferentTask.

    End ScheduledJob.

    (** We prove that we can split cumulative interference into two
        parts: (1) cumulative priority inversion and (2) cumulative
        interference from jobs with higher or equal priority. *)
    Lemma cumulative_interference_split :
      forall j t1 t2,
        cumulative_interference j t1 t2
        = cumulative_priority_inversion arr_seq sched j t1 t2
          + cumulative_another_hep_job_interference arr_seq sched j t1 t2.
    Proof.
      rewrite /cumulative_interference /cumul_cond_interference /cond_interference /interference.
      move=> j t1 t2; rewrite -big_split //=.
      apply/eqP; rewrite eqn_leq; apply/andP; split; rewrite leq_sum//.
      { move => t _; unfold ideal_jlfp_interference.
        by destruct (priority_inversion _ _ _ _), (another_hep_job_interference arr_seq sched j t).
      }
      { move => t _; rewrite /ideal_jlfp_interference.
        destruct (ideal_proc_model_sched_case_analysis sched t) as [IDLE | [s SCHED]].
        - have -> : priority_inversion arr_seq sched j t = false
            by exact/negbTE/idle_implies_no_priority_inversion.
          by rewrite add0n.
        - destruct (hep_job s j) eqn:PRIO.
          + by erewrite sched_hep_implies_no_priority_inversion => //; rewrite add0n.
          + erewrite !sched_lp_implies_priority_inversion => //; last by rewrite PRIO.
            rewrite orTb.
            by rewrite add1n ltnS //= leqn0 eqb0; erewrite no_ahep_interference_when_scheduled_lp; last by erewrite PRIO.
      }
    Qed.

    (** Similarly, we prove that we can split cumulative interfering
        workload into two parts: (1) cumulative priority inversion and
        (2) cumulative interfering workload from jobs with higher or
        equal priority. *)
    Lemma cumulative_interfering_workload_split :
      forall j t1 t2,
        cumulative_interfering_workload j t1 t2
        = cumulative_priority_inversion arr_seq sched j t1 t2
          + cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2.
    Proof.
      rewrite /cumulative_interfering_workload
              /cumulative_priority_inversion
              /cumulative_other_hep_jobs_interfering_workload.
      by move => j t1 t2; rewrite -big_split //=.
    Qed.

    (** Let [j] be any job of task [tsk]. Then the cumulative task
        interference received by job [j] is bounded to the sum of the
        cumulative priority inversion of job [j] and the cumulative
        interference incurred by job [j] due to higher-or-equal
        priority jobs from other tasks. *)
    Lemma cumulative_task_interference_split :
      forall j t1 t2,
        arrives_in arr_seq j ->
        job_of_task tsk j ->
        ~~ completed_by sched j t2 ->
        cumul_task_interference arr_seq sched j t1 t2
        <= cumulative_priority_inversion arr_seq sched j t1 t2
          + cumulative_another_task_hep_job_interference arr_seq sched j t1 t2.
    Proof.
      move=> j t1 R ARR TSK NCOMPL.
      rewrite /cumul_task_interference /cumul_cond_interference.
      rewrite -big_split //= big_seq_cond [leqRHS]big_seq_cond.
      apply leq_sum; move => t /andP [IN _].
      rewrite /cond_interference /nonself /interference /ideal_jlfp_interference.
      have [IDLE|[s SCHEDs]] := ideal_proc_model_sched_case_analysis sched t.
      { move: (IDLE) => IIDLE; erewrite <-is_idle_def in IDLE => //.
        have ->: priority_inversion arr_seq sched j t = false
          by apply/eqP; rewrite eqbF_neg; apply: no_priority_inversion_when_idle => //.
        have ->: another_hep_job_interference arr_seq sched j t = false
          by apply/eqP; rewrite eqbF_neg; apply no_hep_job_interference_when_idle.
        have ->: another_task_hep_job_interference arr_seq sched j t = false
          by apply/eqP; rewrite eqbF_neg; apply/negP; rewrite_neg @no_hep_task_interference_when_idle.
        by rewrite andbF.
      }
      { rewrite (interference_ahep_def _ _ _ _ _ _ _ _ _ _ _ SCHEDs) //.
        rewrite (interference_athep_def _ _ _ _ _ _ _ _ _ _ _ SCHEDs) => //.
        rewrite (priority_inversion_equiv_sched_lower_priority _ _ _ _ _ _ _ _ _ SCHEDs) => //.
        rewrite task_served_eq_task_scheduled // (job_of_scheduled_task _ _ _ _ _ _ _ _ _ SCHEDs) => //.
        rewrite /another_hep_job /another_task_hep_job.
        have [EQj|NEQj] := eqVneq s j.
        { by subst; rewrite /job_of_task eq_refl H_priority_is_reflexive. }
        have [/eqP EQt|NEQt] := eqVneq (job_task s) (job_task j).
        { apply/eqP; move: (EQt) => /eqP <-.
          by rewrite /job_of_task eq_refl //= andbF addn0 eq_sym eqb0; apply/negP => LPs. }
        { by rewrite /job_of_task NEQt //= andbT; case: hep_job. }
      }
    Qed.

    (** In this section, we prove that the (abstract) cumulative
        interfering workload is equivalent to the conventional workload,
        i.e., the one defined with concrete schedule parameters. *)
    Section InstantiatedWorkloadEquivalence.

      (** Let <<[t1,t2)>> be any time interval. *)
      Variables t1 t2 : instant.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.

      (** Then for any job [j], the cumulative interfering workload is
          equal to the conventional workload. *)
      Lemma cumulative_iw_hep_eq_workload_of_ohep :
        cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2
        = workload_of_other_hep_jobs arr_seq j t1 t2.
      Proof.
        rewrite /cumulative_other_hep_jobs_interfering_workload /workload_of_other_hep_jobs.
        case NEQ: (t1 < t2); last first.
        { move: NEQ => /negP /negP; rewrite -leqNgt; move => NEQ.
          rewrite big_geq//.
          rewrite /arrivals_between /arrival_sequence.arrivals_between big_geq//.
          by rewrite /workload_of_jobs big_nil.
        }
        { unfold other_hep_jobs_interfering_workload, workload_of_jobs.
          interval_to_duration t1 t2 k.
          elim: k => [|k IHk].
          - rewrite !addn0.
            rewrite big_geq//.
            rewrite /arrivals_between /arrival_sequence.arrivals_between big_geq//.
            by rewrite /workload_of_jobs big_nil.
          - rewrite addnS big_nat_recr //=; last by rewrite leq_addr.
            rewrite IHk.
            rewrite /arrivals_between /arrival_sequence.arrivals_between big_nat_recr //=.
            + by rewrite big_cat.
            + by rewrite leq_addr.
        }
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

      (** Consider any job j of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_cost_positive : job_cost_positive j.

      (** To show the equivalence of the notions of busy intervals, we
          first show that the notions of quiet time are also
          equivalent. *)

      (** First, we show that the classical notion of quiet time
          implies the abstract notion of quiet time. *)
      Lemma quiet_time_cl_implies_quiet_time_ab :
        forall t, quiet_time_cl j t -> quiet_time_ab j t.
      Proof.
        clear H_JLFP_respects_sequential_tasks.
        have zero_is_quiet_time: forall j, quiet_time_cl j 0.
        { by move => jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0. }
        move=> t QT; apply/andP; split; last first.
        { rewrite negb_and negbK; apply/orP.
          by case ARR: (arrived_before j t); [right | left]; [apply QT | ]. }
        { erewrite cumulative_interference_split, cumulative_interfering_workload_split; rewrite eqn_add2l.
          rewrite cumulative_i_ohep_eq_service_of_ohep//.
          rewrite //= cumulative_iw_hep_eq_workload_of_ohep eq_sym; apply/eqP.
          apply all_jobs_have_completed_equiv_workload_eq_service => //.
          move => j0 IN HEP; apply QT.
          - by apply in_arrivals_implies_arrived in IN.
          - by move: HEP => /andP [H6 H7].
          - by apply in_arrivals_implies_arrived_between in IN.
        }
      Qed.

      (** And vice versa, the abstract notion of quiet time implies
          the classical notion of quiet time. *)
      Lemma quiet_time_ab_implies_quiet_time_cl :
        forall t, quiet_time_ab j t -> quiet_time_cl j t.
      Proof.
        clear H_JLFP_respects_sequential_tasks.
        have zero_is_quiet_time: forall j, quiet_time_cl j 0.
        { by move => jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0. }
        move => t /andP [T0 T1] jhp ARR HP ARB.
        eapply all_jobs_have_completed_equiv_workload_eq_service with
          (P := fun jhp => hep_job jhp j) (t1 := 0) (t2 := t) => //.
        erewrite service_of_jobs_case_on_pred with (P2 := fun j' => j' != j).
        erewrite workload_of_jobs_case_on_pred with (P' := fun j' => j' != j) => //.
        replace ((fun j0 : Job => hep_job j0 j && (j0 != j))) with (another_hep_job^~j); last by rewrite /another_hep_job.
        rewrite -/(service_of_other_hep_jobs arr_seq _ j 0 t) -cumulative_i_ohep_eq_service_of_ohep => //.
        rewrite -/(workload_of_other_hep_jobs _ j 0 t) -cumulative_iw_hep_eq_workload_of_ohep; eauto.
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
          by move => j__copy _ /eqP EQ; subst j__copy.
        }
      Qed.

      (** The equivalence trivially follows from the lemmas above. *)
      Corollary instantiated_quiet_time_equivalent_quiet_time :
        forall t,
          quiet_time_cl j t <-> quiet_time_ab j t.
      Proof.
        clear H_JLFP_respects_sequential_tasks.
        move => ?; split.
        - by apply quiet_time_cl_implies_quiet_time_ab.
        - by apply quiet_time_ab_implies_quiet_time_cl.
      Qed.

      (** Based on that, we prove that the concept of busy interval
          prefix obtained by instantiating the abstract definition of
          busy interval prefix coincides with the conventional
          definition of busy interval prefix. *)
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
    Context `{!JobReady Job (ideal.processor_state Job)}.
    Hypothesis H_work_bearing_readiness : work_bearing_readiness arr_seq sched.

    (** Assume that the schedule is valid and work-conserving. *)
    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    (** Note that we differentiate between abstract and classical
        notions of work-conserving schedule. *)
    Let work_conserving_ab := definitions.work_conserving arr_seq sched.
    Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

    Let busy_interval_prefix_ab := definitions.busy_interval_prefix sched.

    (** We assume that the schedule is a work-conserving schedule in
        the _classical_ sense, and later prove that the hypothesis
        about abstract work-conservation also holds. *)
    Hypothesis H_work_conserving : work_conserving_cl.

    (** Assume the scheduling policy under consideration is reflexive. *)
    Hypothesis H_policy_reflexive : reflexive_job_priorities JLFP.

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

      (** Let the busy interval of the job be <<[t1,t2)>>. *)
      Variable t1 t2 : instant.
      Hypothesis H_busy_interval_prefix : busy_interval_prefix_ab j t1 t2.

      (** Consider a time [t] inside the busy interval of the job. *)
      Variable t : instant.
      Hypothesis H_t_in_busy_interval : t1 <= t < t2.

      (** First, we prove that if interference is [false] at a time
          [t] then the job is scheduled. *)
      Lemma not_interference_implies_scheduled :
        ~ interference j t -> receives_service_at sched j t.
      Proof.
        move => /negP HYP; move : HYP.
        rewrite negb_or /another_hep_job_interference.
        move => /andP [HYP1 HYP2].
        have [Idle|[jo Sched_jo]] := ideal_proc_model_sched_case_analysis sched t.
        { exfalso; clear HYP1 HYP2.
          eapply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in H_busy_interval_prefix => //.
          apply: not_quiet_implies_not_idle => //.
          by rewrite is_idle_def.
        }
        { have PINV := negP HYP1.
          have: ~~ another_hep_job jo j by apply: contraNN HYP2; erewrite <-interference_ahep_def => //.
          rewrite negb_and => /orP [NHEP | EQ].
          - rewrite/receives_service_at; move_neq_up ZS; move: ZS; rewrite leqn0 => /eqP ZS.
            apply no_service_not_scheduled in ZS => //; apply: PINV.
            exact/uni_priority_inversion_P.
          - apply negbNE in EQ; move: EQ => /eqP EQ; subst jo.
            by rewrite /receives_service_at service_at_is_scheduled_at Sched_jo.
        }
      Qed.

      (** Conversely, if the job is scheduled at [t] then interference is [false]. *)
      Lemma scheduled_implies_no_interference :
        receives_service_at sched j t -> ~ interference j t.
      Proof.
        move=> RSERV /orP[PINV | INT].
        - rewrite (sched_hep_implies_no_priority_inversion _ _ _ _ _ _ _ _ j) in PINV => //.
          by rewrite /receives_service_at service_at_is_scheduled_at lt0b in RSERV.
        - rewrite /receives_service_at service_at_is_scheduled_at lt0b in RSERV.
          by move: INT; rewrite_neg @no_ahep_interference_when_scheduled.
      Qed.

    End Abstract_Work_Conservation.

    (** Using the above two lemmas, we can prove that abstract work
        conservation always holds for these instantiations of [I] and
        [IW]. *)
    Corollary instantiated_i_and_w_are_coherent_with_schedule :
      work_conserving_ab.
    Proof.
      move => j t1 t2 t ARR POS BUSY NEQ; split.
      - exact: (not_interference_implies_scheduled j ARR POS).
      - exact: scheduled_implies_no_interference.
    Qed.

    (** Next, in order to prove that these definitions of [I] and [IW]
        are consistent with sequential tasks, we need to assume that
        the policy under consideration respects sequential tasks. *)
    Hypothesis H_policy_respects_sequential_tasks : policy_respects_sequential_tasks JLFP.

    (** We prove that these definitions of [I] and [IW] are consistent
        with sequential tasks. *)
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

    (** Since interfering and interfering workload are sufficient to define the busy window,
        next, we reason about the bound on the length of the busy window. *)
    Section BusyWindowBound.

      (** Consider an arrival curve. *)
      Context `{MaxArrivals Task}.

      (** Consider a set of tasks that respects the arrival curve. *)
      Variable ts : list Task.
      Hypothesis H_taskset_respects_max_arrivals : taskset_respects_max_arrivals arr_seq ts.

      (** Assume that all jobs come from this task set. *)
      Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

      (** Consider a constant [L] such that... *)
      Variable L : duration.
      (** ... [L] is greater than [0], and... *)
      Hypothesis H_L_positive : L > 0.

      (** [L] is the fixed point of the following equation. *)
      Hypothesis H_fixed_point : L = total_request_bound_function ts L.

      (** Assume all jobs have a valid job cost. *)
      Hypothesis H_arrivals_have_valid_job_costs : arrivals_have_valid_job_costs arr_seq.

      (** Then, we prove that [L] is a bound on the length of the busy window. *)
      Lemma instantiated_busy_intervals_are_bounded :
        busy_intervals_are_bounded_by arr_seq sched tsk L.
      Proof.
        move => j ARR TSK POS.
        edestruct busy_interval_from_total_workload_bound
          with (Δ := L) as [t1 [t2 [T1 [T2 GGG]]]] => //.
        { move => t _; rewrite {3}H_fixed_point.
          have ->: blackout_during sched t (t + L) = 0.
          { apply/eqP; rewrite /blackout_during big1 // => l _.
            by rewrite /is_blackout ideal_proc_has_supply. }
          by rewrite add0n; apply total_workload_le_total_rbf. }
        exists t1, t2; split=> [//|]; split=> [//|].
        by apply instantiated_busy_interval_equivalent_busy_interval.
      Qed.

    End BusyWindowBound.

  End I_IW_correctness.

End JLFPInstantiation.


(** To preserve modularity and hide the implementation details of a
    technical definition presented in this file, we make the
    definition opaque. This way, we ensure that the system will treat
    each of these definitions as a single entity. *)
Global Opaque another_hep_job_interference
       another_task_hep_job_interference
       ideal_jlfp_interference
       ideal_jlfp_interfering_workload
       cumulative_another_hep_job_interference
       cumulative_another_task_hep_job_interference
       cumulative_other_hep_jobs_interfering_workload
       other_hep_jobs_interfering_workload.

(** We add some facts into the "Hint Database" basic_rt_facts, so Coq will be
    able to apply them automatically where needed. *)
Global Hint Resolve
       abstract_busy_interval_classic_quiet_time
       abstract_busy_interval_classic_busy_interval_prefix
  : basic_rt_facts.
