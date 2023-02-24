Require Export prosa.analysis.abstract.ideal.abstract_seq_rta.
Require Export prosa.analysis.definitions.priority_inversion.
Require Export prosa.analysis.definitions.work_bearing_readiness.
Require Export prosa.analysis.facts.busy_interval.carry_in.
Require Export prosa.analysis.abstract.iw_auxiliary.
Require Export prosa.analysis.facts.priority.classes.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.
Require Export prosa.analysis.facts.busy_interval.ideal.priority_inversion.

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

  (** Consider any valid arrival sequence with consistent arrivals... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any ideal uni-processor schedule of this arrival
      sequence... *)
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
  Hypothesis H_priority_is_reflexive : reflexive_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_priorities JLFP.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** Assume we have sequential tasks, i.e., jobs of the same task
      execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.

  (** We also assume that the policy respects sequential tasks,
      meaning that later-arrived jobs of a task don't have higher
      priority than earlier-arrived jobs of the same task. *)
  Hypothesis H_JLFP_respects_sequential_tasks : policy_respects_sequential_tasks JLFP.

  (** * Interference and Interfering Workload *)
  (** In the following, we introduce definitions of interference,
      interfering workload and a function that bounds cumulative
      interference. *)

  (** ** Instantiation of Interference *)

  (** We say that job [j] is incurring interference from another
      job with higher-or-equal priority at time [t] if there exists a
      job [jhp] (different from [j]) with a higher-or-equal priority
      that executes at time [t]. *)
  Definition another_hep_job_interference (j : Job) (t : instant) :=
    exists jhp,
      (jhp \in arrivals_up_to arr_seq t)
      /\ another_hep_job jhp j
      /\ receives_service_at sched jhp t.

  (** In order to use the above definition in aRTA, we need to define
      its computational version. *)
  Definition another_hep_job_interference_dec (j : Job) (t : instant) :=
    has (fun jhp => another_hep_job jhp j && receives_service_at sched jhp t) (arrivals_up_to arr_seq t).

  (** Note that the computational and propositional definitions are
      equivalent. *)
  Lemma another_hep_job_interference_P :
    forall j t,
      reflect (another_hep_job_interference j t) (another_hep_job_interference_dec j t).
  Proof.
    move => j t; apply/introP.
    - by move => /hasP [jhp ARR /andP [HEP SCHED]]; (exists jhp; split).
    - move => /negP T1; move => [jhp [ARR [HEP SCHED]]].
      apply: T1; apply/hasP.
      exists jhp; first by done.
      by apply/andP; split.
  Qed.

  (** Similarly, we say that job [j] is incurring interference from a
      job with higher-or-equal priority of another task at time [t]
      if there exists a job [jhp] (of a different task) with
      higher-or-equal priority that executes at time [t]. *)
  Definition another_task_hep_job_interference (j : Job) (t : instant) :=
    exists jhp,
      (jhp \in arrivals_up_to arr_seq t)
      /\ another_task_hep_job jhp j
      /\ receives_service_at sched jhp t.

  (** In order to use the above definition in aRTA, we need to define
      its computational version. *)
  Definition another_task_hep_job_interference_dec (j : Job) (t : instant) :=
    has (fun jhp => another_task_hep_job jhp j && receives_service_at sched jhp t) (arrivals_up_to arr_seq t).

  (** We also show that the computational and propositional
      definitions are equivalent. *)
  Lemma another_task_hep_job_interference_P :
    forall j t,
      reflect (another_task_hep_job_interference j t) (another_task_hep_job_interference_dec j t).
  Proof.
    move => j t; apply/introP.
    - by move => /hasP [jhp ARR /andP [HEP SCHED]]; (exists jhp; split).
    - move => /negP T1; move => [jhp [ARR [HEP SCHED]]].
      apply: T1; apply/hasP.
      exists jhp; first by done.
      by apply/andP; split.
  Qed.

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
        priority_inversion_dec arr_seq sched j t || another_hep_job_interference_dec j t
    }.

  (** ** Instantiation of Interfering Workload *)

  (** Now, we define the notion of cumulative interfering workload,
      called [other_hep_jobs_interfering_workload], that says how many
      units of workload are generated by jobs with higher-or-equal
      priority released at time [t]. *)
  Definition other_hep_jobs_interfering_workload (j : Job) (t : instant) :=
    \sum_(jhp <- arrivals_at arr_seq t | another_hep_job jhp j) job_cost jhp.

  (** The interfering workload, in turn, is defined as the sum of the
      priority inversion predicate and interfering workload of jobs
      with higher or equal priority. *)
  #[local,program] Instance ideal_jlfp_interfering_workload : InterferingWorkload Job :=
    {
      interfering_workload (j : Job) (t : instant) :=
        priority_inversion_dec arr_seq sched j t + other_hep_jobs_interfering_workload j t
    }.


  (** ** Auxiliary definitions *)
  (** For each of the concepts defined above, we introduce a
      corresponding cumulative function: *)

  (** (a) cumulative interference from other jobs with higher-or-equal priority ... *)
  Definition cumulative_another_hep_job_interference (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) another_hep_job_interference_dec j t.

  (** ... (b) and cumulative interference from jobs with higher or
      equal priority from other tasks, ... *)
  Definition cumulative_another_task_hep_job_interference (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) another_task_hep_job_interference_dec j t.

  (** ... and (c) cumulative workload from jobs with higher or equal priority. *)
  Definition cumulative_other_hep_jobs_interfering_workload (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) other_hep_jobs_interfering_workload j t.

  (** Instantiated functions usually do not come with any useful lemmas
      about them. In order to reuse existing lemmas, we need to prove
      equivalence of the instantiated functions to some conventional
      notions. The instantiations given in this file are equivalent to
      service and workload. Further, we prove these equivalences
      formally. *)

  (** Before we present the formal proofs of the equivalences, we
      recall the notion of workload of higher or equal priority
      jobs. *)
  Definition workload_of_another_hep_jobs (j : Job) (t1 t2 : instant) :=
    workload_of_jobs (fun jhp => another_hep_job jhp j) (arrivals_between arr_seq t1 t2).

  (** ... and service of all other jobs with higher or equal priority. *)
  Definition service_of_another_hep_jobs (j : Job) (t1 t2 : instant) :=
    service_of_jobs sched (fun jhp => another_hep_job jhp j) (arrivals_between arr_seq t1 t2) t1 t2.

  (** Similarly, we recall notions of service of higher or equal
      priority jobs from other tasks. *)
  Definition service_of_another_task_hep_job (j : Job) (t1 t2 : instant) :=
    service_of_jobs sched (fun jhp => another_task_hep_job jhp j) (arrivals_between arr_seq t1 t2) t1 t2.

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

    (** In the following subsection, we prove properties of the
        introduced functions under the assumption that the schedule is
        idle. *)
    Section IdleSchedule.

      (** Consider a time instant [t] ... *)
      Variable t : instant.

      (** ... and assume that the schedule is idle at [t]. *)
      Hypothesis H_idle : is_idle sched t.

      (** We prove that in this case: ... *)

      (** ... there is no interference from higher-or-equal priority
          jobs, ... *)
      Lemma idle_implies_no_hep_job_interference :
        forall j, ~ another_hep_job_interference j t.
      Proof.
        move => j [j' [ _ [ _ SERV]]].
        by rewrite /receives_service_at ideal_not_idle_implies_sched in SERV.
      Qed.

      (** ... there is no interference from higher-or-equal priority
          jobs from another task, ... *)
      Lemma idle_implies_no_hep_task_interference :
        forall j, ~ another_task_hep_job_interference j t.
      Proof.
        move => j [j' [ _ [ _ SERV]]].
        by rewrite /receives_service_at ideal_not_idle_implies_sched in SERV.
      Qed.

      (** ... there is no interference, ... *)
      Lemma idle_implies_no_interference :
        forall j, ~ interference j t.
      Proof.
        move => j.
        rewrite /interference /ideal_jlfp_interference => /orP [PI | HEPI].
        - move : PI; move => /priority_inversion_P PI; (feed_n 3 PI; rt_auto).
          move: PI => [_ [j' /andP [SCHED _]]].
          by apply ideal_sched_implies_not_idle in SCHED.
        - move: HEPI => /another_hep_job_interference_P HEPI.
          by apply idle_implies_no_hep_job_interference in HEPI.
      Qed.

      (** ... as well as no interference for [tsk]. Recall that the
          additional argument [upper_bound] is an artificial horizon
          needed needed to make task interference function
          constructive. For more details, refer to the original
          description of the function. *)
      Lemma idle_implies_no_task_interference :
        forall upper_bound, ~ task_interference_received_before arr_seq sched tsk upper_bound t.
      Proof.
        move => upp [NSCHEDT [j' [INT TSKBE]]].
        by apply idle_implies_no_interference in INT.
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

      (** First, consider a case when _some_ jobs is scheduled at time [t]. *)
      Section SomeJobIsScheduled.

        (** Consider a job [j'] (not necessarily distinct from job
            [j]) that is scheduled at time [t]. *)
        Variable j' : Job.
        Hypothesis H_sched : scheduled_at sched j' t.

        (** Under the stated assumptions, we show that the
            interference from another higher-or-equal priority job is
            equivalent to the relation [another_hep_job]. *)
        Lemma interference_ahep_equiv_ahep :
          another_hep_job_interference j t <-> another_hep_job j' j.
        Proof.
          split; [move => [jhp [IN [AHEP PSERV]]] | move => AHEP].
          - apply service_at_implies_scheduled_at in PSERV.
            by have -> := ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_sched PSERV.
          - exists j'; repeat split.
            + apply arrived_between_implies_in_arrivals; rt_eauto.
              apply/andP; split; first by done.
              by apply H_jobs_must_arrive_to_execute in H_sched; rewrite ltnS.
            + by done.
            + by rewrite /receives_service_at service_at_is_scheduled_at H_sched.
        Qed.

      End SomeJobIsScheduled.

      (** Next, consider a case when [j] itself is scheduled at [t]. *)
      Section JIsScheduled.

        (** Assume that [j] is scheduled at time [t]. *)
        Hypothesis H_j_sched : scheduled_at sched j t.

        (** Then there is no interference from higher-or-equal
            priority jobs at time [t]. *)
        Lemma interference_ahep_job_eq_false :
          ~ another_hep_job_interference j t.
        Proof.
          move => [jhp [IN [AHEP PSERV]]].
          apply service_at_implies_scheduled_at in PSERV.
          have EQ := ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_j_sched PSERV; subst jhp.
          by apply another_hep_job_antireflexive in AHEP.
        Qed.

      End JIsScheduled.

      (** In the next subsection, we consider a case when a job [j']
          from the same task (as job [j]) is scheduled. *)
      Section FromSameTask.

        (** Consider a job [j'] that comes from task [tsk] and is
            scheduled at time instant [t].  *)
        Variable j' : Job.
        Hypothesis H_j'_tsk : job_of_task tsk j'.
        Hypothesis H_j'_sched : scheduled_at sched j' t.

        (** Then we show that interference from higher-or-equal
            priority jobs from another task is false. *)
        Lemma interference_athep_eq_false :
          ~ another_task_hep_job_interference j t.
        Proof.
          move => [jhp [IN [AHEP PSERV]]].
          apply service_at_implies_scheduled_at in PSERV.
          have EQ := ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_j'_sched PSERV; subst jhp.
          by eapply another_task_hep_job_taskwise_antireflexive in AHEP; rt_eauto.
        Qed.

        (** Similarly, there is no task interference, since in order
            to incur the task interference, a job from a distinct task
            must be scheduled. *)
        Lemma task_interference_eq_false :
          forall upper_bound, ~ task_interference_received_before arr_seq sched tsk upper_bound t.
        Proof.
          move => upp [TNSCHED [j'' [INT ARR]]].
          unfold interference, ideal_jlfp_interference in *.
          apply:TNSCHED; rewrite /task_scheduled_at.
          by move: (H_j'_sched); rewrite scheduled_at_def => /eqP->.
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

        (** We prove that then [j] incurs higher-or-equal priority
            interference from another task iff [j'] has
            higher-or-equal priority than [j]. *)
        Lemma sched_at_implies_interference_athep_eq_hep :
          another_task_hep_job_interference j t <-> hep_job j' j.
        Proof.
          split; [move=> [j'' [IN [/andP [AHEP FF] RSERV]]] | move => HEP].
          - apply service_at_implies_scheduled_at in RSERV.
            by have EQ := ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_j'_sched RSERV; subst j''.
          - exists j'; repeat split.
            + apply arrived_between_implies_in_arrivals; rt_eauto.
              apply/andP; split; first by done.
              by apply H_jobs_must_arrive_to_execute in H_j'_sched; rewrite ltnS.
            + apply/andP; split; first by done.
              apply/negP => /eqP EQ.
              by move: (H_j'_not_tsk) => /negP T; apply: T; rewrite /job_of_task EQ.
            + by rewrite /receives_service_at service_at_is_scheduled_at H_j'_sched.
        Qed.

        (** Hence, if we assume that [j'] has higher-or-equal priority, ... *)
        Hypothesis H_j'_hep : hep_job j' j.

        (** ... we are able to show that [j] incurs higher-or-equal
            priority interference from another task. *)
        Lemma sched_athep_implies_interference_athep :
          another_task_hep_job_interference j t.
        Proof.
          by apply sched_at_implies_interference_athep_eq_hep.
        Qed.

        (** Moreover, in this case, task [tsk] also incurs interference. *)
        Lemma sched_athep_implies_task_interference :
          forall upper_bound,
            (j \in arrivals_between arr_seq 0 upper_bound) ->
            task_interference_received_before arr_seq sched tsk upper_bound t.
        Proof.
          move => upp IN.
          split.
          - by move: (H_j'_sched); rewrite /task_scheduled_at scheduled_at_def => /eqP ->; apply/negP.
          - exists j; split.
            + apply/orP; right.
              apply/another_hep_job_interference_P; exists j'; repeat split.
              * apply arrived_between_implies_in_arrivals; rt_eauto.
                apply/andP; split; first by done.
                by apply H_jobs_must_arrive_to_execute in H_j'_sched; rewrite ltnS.
              * apply/andP; split; first by done.
                apply/negP; move => /eqP EQ; subst.
                by move: (H_j'_not_tsk); rewrite H_j_tsk.
              * by rewrite /receives_service_at service_at_is_scheduled_at lt0b.
            + rewrite mem_filter; apply/andP; split; last by done.
              by rewrite H_j_tsk.
        Qed.

      End FromDifferentTask.

      (** In the last subsection, we consider a case when the
          scheduled job [j'] has lower priority than job [j]. *)
      Section LowerPriority.

        (** Consider a job [j'] that has lower priority than job [j]
            and is scheduled at time instant [t].  *)
        Variable j' : Job.
        Hypothesis H_j'_sched : scheduled_at sched j' t.
        Hypothesis H_j'_lp : ~~ hep_job j' j.

        Lemma sched_alp_implies_interference_ahep_false :
          ~ another_hep_job_interference j t.
        Proof.
          move=> [jlp [IN [AHEP RSERV]]].
          apply service_at_implies_scheduled_at in RSERV.
          have EQ := ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_j'_sched RSERV; subst j'.
          by move: (H_j'_lp) AHEP => LP /andP [HEP A]; rewrite HEP in LP.
        Qed.

      End LowerPriority.

    End ScheduledJob.

    (** We prove that we can split cumulative interference into two
        parts: (1) cumulative priority inversion and (2) cumulative
        interference from jobs with higher or equal priority. *)
    Lemma cumulative_interference_split :
      forall j t1 t2,
        cumulative_interference j t1 t2
        = cumulative_priority_inversion arr_seq sched j t1 t2
          + cumulative_another_hep_job_interference j t1 t2.
    Proof.
      rewrite /cumulative_interference /interference => j t1 t2; rewrite -big_split //=.
      apply/eqP; rewrite eqn_leq; apply/andP; split; rewrite leq_sum; try done.
      { move => t _; unfold ideal_jlfp_interference.
        by destruct (priority_inversion_dec _ _ _ _), (another_hep_job_interference_dec j t).
      }
      { move => t _; rewrite /ideal_jlfp_interference.
        destruct (ideal_proc_model_sched_case_analysis sched t) as [IDLE | [s SCHED]].
        - by rewrite idle_implies_no_priority_inversion // add0n.
        - destruct (hep_job s j) eqn:PRIO.
          + by erewrite sched_hep_implies_no_priority_inversion; rt_eauto; rewrite add0n.
          + erewrite !sched_lp_implies_priority_inversion; rt_eauto; last by rewrite PRIO.
            rewrite orTb.
            destruct (another_hep_job_interference_dec j t) eqn:IAHEP; [exfalso | by done].
            move: IAHEP => /another_hep_job_interference_P IAHEP.
            eapply sched_alp_implies_interference_ahep_false; rt_eauto.
            by rewrite PRIO.
      }
    Qed.

    (** Similarly, we prove that we can split cumulative interfering
        workload into two parts: (1) cumulative priority inversion and
        (2) cumulative interfering workload from jobs with higher or
        equal priority. *)
    Lemma cumulative_interfering_workload_split :
      forall j t1 t2,
        cumulative_interfering_workload j t1 t2 =
          cumulative_priority_inversion arr_seq sched j t1 t2
          + cumulative_other_hep_jobs_interfering_workload j t1 t2.
    Proof.
      rewrite /cumulative_interfering_workload
              /cumulative_priority_inversion
              /cumulative_other_hep_jobs_interfering_workload.
      by move => j t1 t2; rewrite -big_split //=.
    Qed.

    (** Before we prove a lemma about the task's interference split,
        we show that any job [j] of task [tsk] experiences _either_
        priority inversion or task interference if two properties are
        satisfied: (1) task [tsk] is not scheduled at a time instant
        [t] and (2) there is a job [jo] that experiences interference
        at a time [t]. *)
    Remark priority_inversion_xor_atask_hep_job_interference :
      forall j t,
        job_of_task tsk j ->
        ~ task_scheduled_at sched tsk t ->
        forall jo,
          interference jo t ->
          (~~ priority_inversion_dec arr_seq sched j t && another_task_hep_job_interference_dec j t)
          || (priority_inversion_dec arr_seq sched j t && ~~ another_task_hep_job_interference_dec j t).
    Proof.
      move => j t TSK TNSCHED jo INT.
      destruct priority_inversion_dec eqn:PI; simpl.
      - move: PI => /priority_inversion_negP PI; feed_n 3 PI; rt_eauto.
        apply/negP; move => /another_task_hep_job_interference_P [jhp [IN__jhp [/andP [ATHEP__hp BB] RS__jhp]]].
        apply: PI; move => [_ [jlp /andP [SCHED__jlp LEP__jlp]]].
        enough (EQ: jlp = jhp); first by (subst; rewrite ATHEP__hp in LEP__jlp).
        eapply ideal_proc_model_is_a_uniprocessor_model; rt_eauto; move: RS__jhp.
        by rewrite /receives_service_at service_at_is_scheduled_at lt0b.
      - destruct another_task_hep_job_interference_dec eqn:IATHEP; try done; exfalso.
        have L1: interference jo t -> exists jt, scheduled_at sched jt t.
        { clear PI IATHEP; move => /orP [/priority_inversion_P PI| ].
          { by feed_n 3 PI; rt_auto; move: PI => [NSCHED [jt /andP [SCHED _]]]; exists jt. }
          { move => /another_hep_job_interference_P [jt [_ [_ RSERV]]].
            by exists jt; move: RSERV; rewrite /receives_service_at service_at_is_scheduled_at lt0b. }
        }
        apply L1 in INT; destruct INT as [jt SCHED]; clear L1.
        move: PI => /eqP; rewrite eqbF_neg => /priority_inversion_negP PI; feed_n 3 PI; rt_eauto; apply: PI.
        move: IATHEP => /eqP; rewrite eqbF_neg => /hasPn OH.
        specialize (OH jt); feed OH.
        { apply arrived_between_implies_in_arrivals => //; rt_eauto.
          by apply/andP; split; last (rewrite ltnS //; apply H_jobs_must_arrive_to_execute).
        }
        rewrite //= negb_and negb_and in OH.
        move: OH => /orP [/orP [OH11 | OH22] | OH2].
        + split; last by (exists jt; apply/andP; split).
          apply/negP => SCHEDj; move: OH11.
          rewrite (ideal_proc_model_is_a_uniprocessor_model _ _ _ _ SCHEDj SCHED).
          by move => /negP E; apply: E; eapply H_priority_is_reflexive with (t := 0).
        + exfalso; apply: TNSCHED.
          move: SCHED; rewrite /task_scheduled_at scheduled_at_def => /eqP ->.
          by move: OH22; rewrite Bool.negb_involutive => /eqP ->.
        + exfalso; move: OH2 => /negP OH2; apply: OH2.
          by rewrite /receives_service_at service_at_is_scheduled_at lt0b.
    Qed.

    (** Let [j] be any job of task [tsk], and let [upper_bound] be any
        time instant after job [j]'s arrival. Then for any time
        interval lying before [upper_bound], the cumulative
        interference received by [tsk] is equal to the sum of the
        cumulative priority inversion of job [j] and the cumulative
        interference incurred by task [tsk] due to other tasks. *)
    Lemma cumulative_task_interference_split :
      forall j t1 t2 upper_bound,
        arrives_in arr_seq j ->
        job_of_task tsk j ->
        j \in arrivals_before arr_seq upper_bound ->
        ~~ completed_by sched j t2 ->
        cumul_task_interference arr_seq sched tsk upper_bound t1 t2 =
          cumulative_priority_inversion arr_seq sched j t1 t2
          + cumulative_another_task_hep_job_interference j t1 t2.
    Proof.
      move=> j t1 R upp ARRin TSK ARR NCOMPL; rewrite /cumul_task_interference.
      rewrite -big_split //= big_seq_cond [in X in _ = X]big_seq_cond; apply eq_bigr; move => t /andP [IN _].
      have BinFact: forall (a b c : bool), (a -> (~~ b && c) || (b && ~~c)) -> (b \/ c -> a) -> nat_of_bool a = nat_of_bool b + nat_of_bool c.
      { by clear; move => [] [] []; try compute; firstorder; inversion H; inversion H0. }
      apply: BinFact;
        [move=> /task_interference_received_before_P [TNSCHED [jo [INT TIN]]]
        | move=> [/priority_inversion_P PRIO | /another_task_hep_job_interference_P [jo [INjo [ATHEP RSERV]]]]].
      { by eapply priority_inversion_xor_atask_hep_job_interference; rt_eauto. }
      { feed_n 3 PRIO; rt_auto; move: PRIO => [NSCHED [j' /andP [SCHED NHEP]]].
        apply/task_interference_received_before_P; split.
        - move => TSCHED.
          have TSKj' : job_of_task tsk j'.
          { move: TSCHED; rewrite /task_scheduled_at.
            by move: SCHED; rewrite scheduled_at_def => /eqP ->.
          } clear TSCHED.
          have ARRj': job_arrival j < job_arrival j'.
          { by move: NHEP; rewrite ltnNge; apply contra, H_JLFP_respects_sequential_tasks; move: TSK => /eqP ->. }
          eapply H_sequential_tasks in ARRj'; rt_eauto; last by rewrite /same_task; move: TSKj' => /eqP ->.
          apply ARRj' in SCHED; clear ARRj'.
          move: NCOMPL => /negP NCOMPL; apply: NCOMPL.
          apply completion_monotonic with t; rt_auto.
          by move: IN; rewrite mem_iota; clear; lia.
        - exists j; split.
          + apply/orP; left; apply /priority_inversion_P; rt_auto.
            by split; last (exists j'; apply/andP; split; rt_eauto).
          + by rewrite mem_filter; apply/andP; split.
      }
      { apply/task_interference_received_before_P; split.
        { move => TSCHED; move: ATHEP => /andP [_ /negP EQ]; apply: EQ.
          move: TSCHED; rewrite /task_scheduled_at; move: RSERV.
          rewrite /receives_service_at service_at_is_scheduled_at lt0b scheduled_at_def => /eqP -> => /eqP ->.
          by rewrite eq_sym.
        }
        exists j; split.
        - apply/orP; right; apply/another_hep_job_interference_P.
          exists jo; split; first (by done); split; last by done.
          move: ATHEP => /andP [A B]; apply/andP; split; first by done.
          by apply/negP; move => /eqP EQ; subst jo; rewrite eq_refl in B.
        - by rewrite mem_filter; apply/andP; split. }
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
        cumulative_other_hep_jobs_interfering_workload j t1 t2
        = workload_of_another_hep_jobs j t1 t2.
      Proof.
        rewrite /cumulative_other_hep_jobs_interfering_workload /workload_of_another_hep_jobs.
        case NEQ: (t1 < t2); last first.
        { move: NEQ => /negP /negP; rewrite -leqNgt; move => NEQ.
          rewrite big_geq; last by done.
          rewrite /arrivals_between /arrival_sequence.arrivals_between big_geq; last by done.
            by rewrite /workload_of_jobs big_nil.
        }
        { unfold other_hep_jobs_interfering_workload, workload_of_jobs.
          interval_to_duration t1 t2 k.
          induction k.
          - rewrite !addn0.
            rewrite big_geq; last by done.
            rewrite /arrivals_between /arrival_sequence.arrivals_between big_geq; last by done.
              by rewrite /workload_of_jobs big_nil.
          - rewrite addnS big_nat_recr //=; last by rewrite leq_addr.
            rewrite IHk.
            rewrite /arrivals_between /arrival_sequence.arrivals_between big_nat_recr //=;
                    last by rewrite leq_addr.
              by rewrite big_cat //=.
        }
      Qed.

    End InstantiatedWorkloadEquivalence.

    (** In this section, we prove that the (abstract) cumulative
        interference of jobs with higher or equal priority is equal to
        total service of jobs with higher or equal priority. *)
    Section InstantiatedServiceEquivalences.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.

      (** We consider an arbitrary time interval <<[t1, t)>> that
          starts with a quiet time. *)
      Variable t1 t : instant.
      Hypothesis H_quiet_time : busy_interval.quiet_time arr_seq sched j t1.

      (** Then for job [j], the (abstract) instantiated function of
          interference is equal to the total service of any subset of jobs
          with higher or equal priority. *)
      Lemma cumulative_pred_eq_service (P : pred Job) :
        (forall j', P j' -> hep_job j' j) ->
          \sum_(t1 <= t' < t)
            has (fun j' => P j' && receives_service_at sched j' t')
                (arrivals_up_to arr_seq t')
          = service_of_jobs sched P (arrivals_between arr_seq t1 t) t1 t.
      Proof.
        move=> Phep; clear H_job_of_tsk.
        rewrite [RHS]exchange_big /=; apply: eq_big_nat => x /andP[t1lex xltt].
        rewrite /another_hep_job_interference_dec.
        ideal_proc_model_sched_case_analysis_eq sched x jo => [|{EqSched_jo}].
        { rewrite (@eq_has _ _ pred0) ?has_pred0 ?big1 // => [j' _ | j'].
          + exact: ideal_not_idle_implies_sched.
          + rewrite /receives_service_at ideal_not_idle_implies_sched //.
            by rewrite andbF. }
        have arr_jo : arrives_in arr_seq jo.
        { exact: H_jobs_come_from_arrival_sequence Sched_jo. }
        have arr_jo_x : job_arrival jo <= x.
        { exact: H_jobs_must_arrive_to_execute Sched_jo. }
        have [jo_hep_j|PRIO] := boolP (P jo).
        - transitivity true.
          { congr nat_of_bool; apply/hasP; exists jo.
            - by apply: arrived_between_implies_in_arrivals; rt_eauto.
            - rewrite jo_hep_j /receives_service_at service_at_is_scheduled_at.
              by rewrite Sched_jo. }
          apply/esym/eqP; rewrite eqn_leq; apply/andP; split.
          + by apply: service_of_jobs_le_1; rt_eauto.
          + rewrite sum_nat_gt0; apply/hasP; exists jo; last first.
            { by rewrite service_at_is_scheduled_at Sched_jo. }
            rewrite mem_filter jo_hep_j /=.
            apply: arrived_between_implies_in_arrivals; rt_eauto.
            apply/negPn; rewrite negb_and -ltnNge -leqNgt.
            apply/negP => /orP[arr_jo_t1|]; last by lia.
            move: Sched_jo; apply/negP.
            apply: completed_implies_not_scheduled => //.
            apply: completion_monotonic t1lex _.
            by apply: H_quiet_time => //; apply: Phep jo_hep_j.
        - rewrite (@eq_in_has _ _ pred0) ?has_pred0 ?big1// => [j' AHEP|j' IN].
          + apply/eqP; rewrite service_at_is_scheduled_at eqb0; apply/negP.
            move=> SCHED; move: AHEP PRIO; suff -> : jo = j' by move=> ->.
            by apply: ideal_proc_model_is_a_uniprocessor_model; rt_eauto.
          + apply/eqP; rewrite eqbF_neg negb_and orbC -implyNb negbK.
            apply/implyP.
            rewrite /receives_service_at service_at_is_scheduled_at lt0b.
            move=> SCHED; suff <- : jo = j' by [].
            by apply: ideal_proc_model_is_a_uniprocessor_model; rt_eauto.
      Qed.

      (** The above is in particular true for the jobs other
          than [j] with higher or equal priority... *)
      Lemma  cumulative_i_ohep_eq_service_of_ohep :
        cumulative_another_hep_job_interference j t1 t
        = service_of_another_hep_jobs j t1 t.
      Proof. by apply: cumulative_pred_eq_service => ? /andP[]. Qed.

      (** ...and for jobs from other tasks than [j] with higher
          or equal priority. *)
      Lemma cumulative_i_thep_eq_service_of_othep :
        cumulative_another_task_hep_job_interference j t1 t
        = service_of_another_task_hep_job j t1 t.
      Proof. by apply: cumulative_pred_eq_service => ? /andP[]. Qed.

    End InstantiatedServiceEquivalences.

    (** In this section we prove that the abstract definition of busy
        interval is equivalent to the conventional, concrete
        definition of busy interval for JLFP scheduling. *)
    Section BusyIntervalEquivalence.

      (** In order to avoid confusion, we denote the notion of a quiet
          time in the _classical_ sense as [quiet_time_cl], and the
          notion of quiet time in the _abstract_ sense as
          [quiet_time_ab]. *)
      Let quiet_time_cl := busy_interval.quiet_time arr_seq sched.
      Let quiet_time_ab := definitions.quiet_time sched.

      (** Same for the two notions of a busy interval prefix ... *)
      Let busy_interval_prefix_cl := busy_interval.busy_interval_prefix arr_seq sched.
      Let busy_interval_prefix_ab := definitions.busy_interval_prefix sched.

      (** ... and the two notions of a busy interval. *)
      Let busy_interval_cl := busy_interval.busy_interval arr_seq sched.
      Let busy_interval_ab := definitions.busy_interval sched.

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
        move=> t QT; split; last first.
        { rewrite negb_and Bool.negb_involutive; apply/orP.
          case ARR: (arrived_before j t); [right | left]; [apply QT | ]; eauto.
          by apply H_priority_is_reflexive with (t := 0).
        }
        { erewrite cumulative_interference_split, cumulative_interfering_workload_split; apply/eqP; rewrite eqn_add2l.
          rewrite cumulative_i_ohep_eq_service_of_ohep; rt_eauto; first last.
          { by move => ? _ _ ; unfold arrived_before; lia. }
          rewrite //= cumulative_iw_hep_eq_workload_of_ohep eq_sym; apply/eqP.
          apply all_jobs_have_completed_equiv_workload_eq_service; rt_eauto.
          move => j0 IN HEP; apply QT.
          - by apply in_arrivals_implies_arrived in IN.
          - by move: HEP => /andP [H6 H7].
          - by apply in_arrivals_implies_arrived_between in IN; rt_eauto.
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
        move => t [T0 T1] jhp ARR HP ARB.
        eapply all_jobs_have_completed_equiv_workload_eq_service with
          (P := fun jhp => hep_job jhp j) (t1 := 0) (t2 := t); rt_eauto.
        erewrite service_of_jobs_case_on_pred with (P2 := fun j' => j' != j); rt_eauto.
        erewrite workload_of_jobs_case_on_pred with (P' := fun j' => j' != j); rt_eauto.
        replace ((fun j0 : Job => hep_job j0 j && (j0 != j))) with (another_hep_job^~j); last by rewrite /another_hep_job.
        rewrite -/(service_of_another_hep_jobs j 0 t) -cumulative_i_ohep_eq_service_of_ohep; eauto.
        rewrite -/(workload_of_another_hep_jobs j 0 t) -cumulative_iw_hep_eq_workload_of_ohep; eauto.
        move: T1; rewrite negb_and => /orP [NA | /negPn COMP].
        { have PRED__eq: {in arrivals_between arr_seq 0 t, (fun j__copy : Job => hep_job j__copy j && ~~ (j__copy != j)) =1 pred0}.
          { move => j__copy IN; apply negbTE.
            rewrite negb_and; apply/orP; right; apply/negPn/eqP => EQ; subst j__copy.
            move: NA => /negP CONTR; apply: CONTR.
            by apply in_arrivals_implies_arrived_between in IN; rt_eauto. }
          erewrite service_of_jobs_equiv_pred with (P2 := pred0); last by done.
          erewrite workload_of_jobs_equiv_pred with (P' := pred0); last by done.
          move: T0; erewrite cumulative_interference_split, cumulative_interfering_workload_split => /eqP; rewrite eqn_add2l => /eqP EQ.
          rewrite EQ; clear EQ; apply/eqP; rewrite eqn_add2l.
          by erewrite workload_of_jobs_pred0, service_of_jobs_pred0.
        }
        { have PRED__eq: {in arrivals_between arr_seq 0 t, (fun j0 : Job => hep_job j0 j && ~~ (j0 != j)) =1 eq_op j}.
          { move => j__copy IN.
            replace (~~ (j__copy != j)) with (j__copy == j); last by case: (j__copy == j).
            rewrite eq_sym; destruct (j == j__copy) eqn:EQ; last by rewrite Bool.andb_false_r.
            move: EQ => /eqP EQ; rewrite Bool.andb_true_r; apply/eqP; rewrite eqb_id; subst.
            by eapply (H_priority_is_reflexive 0). }
          erewrite service_of_jobs_equiv_pred with (P2 := eq_op j); last by done.
          erewrite workload_of_jobs_equiv_pred with (P' := eq_op j); last by done.
          move: T0; erewrite cumulative_interference_split, cumulative_interfering_workload_split => /eqP; rewrite eqn_add2l => /eqP EQ.
          rewrite EQ; clear EQ; apply/eqP; rewrite eqn_add2l.
          apply/eqP; eapply all_jobs_have_completed_equiv_workload_eq_service with
            (P := eq_op j) (t1 := 0) (t2 := t); rt_eauto.
          by move => j__copy _ /eqP EQ; subst j__copy.
        }
        move => ? _ _ ; unfold arrived_before; lia.
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
          split; [ |split].
          - by done.
          - by apply instantiated_quiet_time_equivalent_quiet_time in QTt1.
          - by move => t NE QT; eapply NQT; eauto 2; apply instantiated_quiet_time_equivalent_quiet_time.
        }
        { move => [/andP [NEQ1 NEQ2] [QTt1 NQT]].
          split; [ | split; [ |split] ].
          - by apply leq_ltn_trans with (job_arrival j).
          - by eapply instantiated_quiet_time_equivalent_quiet_time; rt_eauto.
          - by move => t NEQ QT; eapply NQT; eauto 2; eapply instantiated_quiet_time_equivalent_quiet_time in QT; rt_eauto.
          - by apply/andP; split.
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
          - by eapply instantiated_quiet_time_equivalent_quiet_time; rt_eauto.
        }
      Qed.

    End BusyIntervalEquivalence.

  End Equivalences.

  (** In this section we prove some properties about the interference
      and interfering workload as defined in this file. *)
  Section I_IW_correctness.

    (** Consider work-bearing readiness. *)
    Context `{@JobReady Job (ideal.processor_state Job) _ _}.
    Hypothesis H_work_bearing_readiness : work_bearing_readiness arr_seq sched.

    (** Assume that the schedule is valid and work-conserving. *)
    Hypothesis H_sched_valid : @valid_schedule Job (ideal.processor_state Job) sched _ _ _ arr_seq.

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
    Hypothesis policy_reflexive : reflexive_priorities JLFP.

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
        ideal_proc_model_sched_case_analysis_eq sched t jo.
        { exfalso; clear HYP1 HYP2.
          eapply instantiated_busy_interval_prefix_equivalent_busy_interval_prefix in H_busy_interval_prefix; rt_eauto.
          by eapply not_quiet_implies_not_idle; rt_eauto.
        }
        { move: HYP1 => /priority_inversion_negP PINV; feed_n 3 PINV; rt_auto.
          have /another_hep_job_interference_P INT := HYP2.
          eapply iffLRn in INT; last apply interference_ahep_equiv_ahep; rt_eauto.
          move: INT => /negP. rewrite negb_and => /orP [NHEP | EQ].
          - rewrite/receives_service_at; move_neq_up ZS; move: ZS; rewrite leqn0 => /eqP ZS.
            apply no_service_not_scheduled in ZS; rt_auto; apply: PINV.
            by split; rt_auto; exists jo; apply/andP; split; rt_eauto.
          - apply negbNE in EQ; move: EQ => /eqP EQ; subst jo.
            by rewrite /receives_service_at service_at_is_scheduled_at Sched_jo.
        }
      Qed.

      (** Conversely, if the job is scheduled at [t] then interference is [false]. *)
      Lemma scheduled_implies_no_interference :
        receives_service_at sched j t -> ~ interference j t.
      Proof.
        move => RSERV /orP [PINV|/another_hep_job_interference_P INT].
        - rewrite (sched_hep_implies_no_priority_inversion _ _ _ _ j) in PINV; rt_eauto.
          by rewrite /receives_service_at service_at_is_scheduled_at lt0b in RSERV.
        - rewrite /receives_service_at service_at_is_scheduled_at lt0b in RSERV.
          by apply interference_ahep_job_eq_false in RSERV.
      Qed.

    End Abstract_Work_Conservation.

    (** Using the above two lemmas, we can prove that abstract work
        conservation always holds for these instantiations of [I] and
        [IW]. *)
    Corollary instantiated_i_and_w_are_coherent_with_schedule :
      work_conserving_ab.
    Proof.
      move => j t1 t2 t ARR POS BUSY NEQ; split.
      - by eapply (not_interference_implies_scheduled j ARR POS); rt_eauto.
      - by apply (scheduled_implies_no_interference j t ).
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
      eapply instantiated_busy_interval_equivalent_busy_interval in BUSY; rt_eauto.
      eapply all_jobs_have_completed_equiv_workload_eq_service; rt_eauto.
      move => s INs /eqP TSKs.
      move: (INs) => NEQ.
      eapply in_arrivals_implies_arrived_between in NEQ; rt_eauto.
      move: NEQ => /andP [_ JAs].
      move: (BUSY) => [[ _ [QT [_ /andP [JAj _]]] _]].
      apply QT; try done; first by eapply in_arrivals_implies_arrived; eauto 2.
      apply H_policy_respects_sequential_tasks; first by rewrite  TSK TSKs.
      by apply leq_trans with t1; [lia | done].
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
      Lemma instantiated_busy_intervals_are_bounded:
        busy_intervals_are_bounded_by arr_seq sched tsk L.
      Proof.
        move => j ARR TSK POS.
        edestruct exists_busy_interval_from_total_workload_bound
          with (Δ := L) as [t1 [t2 [T1 [T2 GGG]]]]; rt_eauto.
        { move => t; rewrite {2}H_fixed_point; apply total_workload_le_total_rbf; try by done. }
        exists t1, t2; split; first by done.
        split; first by done.
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
       another_hep_job_interference_dec
       another_task_hep_job_interference
       another_task_hep_job_interference_dec
       ideal_jlfp_interference
       ideal_jlfp_interfering_workload
       cumulative_another_hep_job_interference
       cumulative_another_task_hep_job_interference
       cumulative_other_hep_jobs_interfering_workload
       other_hep_jobs_interfering_workload.
