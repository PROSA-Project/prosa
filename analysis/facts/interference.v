Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.definitions.interference.
Require Export prosa.analysis.definitions.priority.classes.
Require Export prosa.analysis.facts.model.service_of_jobs.

(** * Auxiliary Lemmas about Interference *)

(** If there is a priority policy in the context, one can
    differentiate between interference (interfering workload) that
    comes from jobs with higher or lower priority from other sources
    of interference (interfering workload).

    Unfortunately, instantiated functions usually do not come with any
    useful lemmas about them. In order to reuse existing lemmas, we
    need to prove equivalence of the instantiated functions to some
    conventional notions. *)

(** First, we prove several lemmas about interference in the context
    of priority policies involving both FP and JLFP relations. *)
Section InterferenceProperties.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType} {jt : JobTask Job Task}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Consider a reflexive FP-policy and a JLFP policy compatible with it. *)
  Context {FP : FP_policy Task} {JLFP : JLFP_policy Job}.
  Hypothesis H_compatible : JLFP_FP_compatible JLFP FP.
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.

  (** We observe that any higher-priority job must come from a task with
      either higher or equal priority. *)
  Lemma another_task_hep_job_split_hp_ep :
    forall j1 j2,
      another_task_hep_job j1 j2
      = hp_task_hep_job j1 j2 || other_ep_task_hep_job j1 j2.
  Proof.
    move=> j1 j2; rewrite -[X in _ || X]andbA -andb_orr /another_task_hep_job.
    have [hepj1j2/=|//] := boolP (hep_job j1 j2).
    rewrite -[hp_task _ _](@andb_idr _ (job_task j1 != job_task j2)).
    - by rewrite -andb_orl -hep_hp_ep_task hep_job_implies_hep_task.
    - by apply: contraTN => /eqP->; rewrite hp_task_irrefl.
  Qed.

  (** We establish a higher-or-equal job of another task causing interference,
      can be due to a higher priority task or an equal priority task. *)
  Lemma hep_interference_another_task_split :
    forall j t,
      another_task_hep_job_interference arr_seq sched j t
      = hep_job_from_hp_task_interference arr_seq sched j t
        || hep_job_from_other_ep_task_interference arr_seq sched j t.
  Proof.
    move => j t; rewrite -has_predU; apply: eq_in_has => j' _ /=.
    exact: another_task_hep_job_split_hp_ep.
  Qed.

  (** Now, assuming a uniprocessor model,... *)
  Hypothesis H_uniproc : uniprocessor_model PState.

  (** ...the previous lemma allows us to establish that the cumulative interference incurred by a job
      is equal to the sum of the cumulative interference from higher-or-equal-priority jobs belonging to
      strictly higher-priority tasks (FP) and the cumulative interference from higher-or-equal-priority
      jobs belonging to equal-priority tasks (GEL). *)
  Lemma cumulative_hep_interference_split_tasks_new :
    forall j t1 Δ,
    cumulative_another_task_hep_job_interference arr_seq  sched j t1 (t1 + Δ)
    = cumulative_interference_from_hep_jobs_from_hp_tasks arr_seq sched j t1 (t1 + Δ)
      + cumulative_interference_from_hep_jobs_from_other_ep_tasks arr_seq sched j t1 (t1 + Δ).
  Proof.
    move => j t1 Δ.
    rewrite -big_split //=; apply: eq_big_seq => t IN.
    rewrite hep_interference_another_task_split.
    have: forall a b, ~~ (a && b) -> (a || b) = a + b :> nat by case; case.
    apply; apply/negP => /andP[/hasP[j' + hp] /hasP[j'' + ep]].
    rewrite !mem_filter => /andP[sj' _] /andP[sj'' _].
    move: hp ep; have ->: j'' = j' by exact: only_one_job_receives_service_at_uni.
    move=> /andP[_ /andP[_ +]] /andP[/andP[_ +] _].
    by rewrite hep_hp_ep_task negb_or ep_task_sym => /andP[_ /negbTE].
  Qed.

End InterferenceProperties.

(** In the following section, we prove a few properties of
    interference under a JLFP policy. *)
Section InterferencePropertiesJLFP.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of fully supply-consuming uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider any valid arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any uni-processor schedule of this arrival
      sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after
      completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** In the following, consider a JLFP-policy that indicates a
      higher-or-equal priority relation, and assume that this relation
      is reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** First, we prove a few rewriting rules under the assumption that
      there is no supply. *)
  Section NoSupply.

    (** Consider a time instant [t] ... *)
    Variable t : instant.

    (** ... and assume that there is no supply at [t]. *)
    Hypothesis H_no_supply : ~~ has_supply sched t.

    (** Then, there is no interference from higher-or-equal priority
        jobs ... *)
    Lemma no_hep_job_interference_without_supply :
      forall j, ~~ another_hep_job_interference arr_seq sched j t.
    Proof.
      move=> j; apply/hasPn => [s IN]; exfalso.
      move: IN; rewrite mem_filter => /andP [SERV _].
      move: (H_no_supply) => /negP NSUP; apply: NSUP.
      by apply: receives_service_implies_has_supply.
    Qed.

    (** ... and that there is no interference from higher-or-equal
        priority jobs from other tasks. *)
    Lemma no_hep_task_interference_without_supply :
      forall j, ~~ another_task_hep_job_interference arr_seq sched j t.
    Proof.
      move=> j; apply/hasPn => [s IN]; exfalso.
      move: IN; rewrite mem_filter => /andP [SERV _].
      move: (H_no_supply) => /negP NSUP; apply: NSUP.
      by apply: receives_service_implies_has_supply.
    Qed.

  End NoSupply.

  (** In the following subsection, we prove properties of the
      introduced functions under the assumption that the schedule is
      idle. *)
  Section Idle.

    (** Consider a time instant [t] ... *)
    Variable t : instant.

    (** ... and assume that the schedule is idle at [t]. *)
    Hypothesis H_idle : is_idle arr_seq sched t.

    (** We prove that in this case: ... *)

    (** ... there is no interference from higher-or-equal priority
        jobs ... *)
    Lemma no_hep_job_interference_when_idle :
      forall j, ~~ another_hep_job_interference arr_seq sched j t.
    Proof.
      move=> j; apply/hasPn=> jo SERV; exfalso.
      rewrite mem_filter in SERV; move: SERV => /andP [SERV _].
      by apply/negP; first apply: no_service_received_when_idle => //. 
    Qed.

    (** ... and that there is no interference from higher-or-equal
        priority jobs from other tasks. *)
    Lemma no_hep_task_interference_when_idle :
      forall j, ~~ another_task_hep_job_interference arr_seq sched j t.
    Proof.
      move=> j; apply/hasPn=> jo SERV; exfalso.
      rewrite mem_filter in SERV; move: SERV => /andP [SERV _].
      by apply/negP; first apply: no_service_received_when_idle => //. 
    Qed.

  End Idle.

  (** Next, we prove properties of the introduced functions under the
      assumption that there is supply and the scheduler is not
      idle. *)
  Section SupplyAndScheduledJob.

    (** Consider a job [j] of task [tsk]. In this subsection, job [j]
        is deemed to be the main job with respect to which the
        functions are computed. *)
    Variable j : Job.
    Hypothesis H_j_tsk : job_of_task tsk j.

    (** Consider a time instant [t] ... *)
    Variable t : instant.

    (** ... and assume that there is supply at [t]. *)
    Hypothesis H_supply : has_supply sched t.

    (** First, consider a case when _some_ job is scheduled at time [t]. *)
    Section SomeJobIsScheduled.

      (** Consider a job [j'] (not necessarily distinct from job [j])
          that is scheduled at time [t]. *)
      Variable j' : Job.
      Hypothesis H_sched : scheduled_at sched j' t.

      (** Under the stated assumptions, we show that the interference
          from another higher-or-equal priority job is equivalent to
          the relation [another_hep_job]. *)
      Lemma interference_ahep_def :
        another_hep_job_interference arr_seq sched j t = another_hep_job j' j.
      Proof.
        clear H_j_tsk.
        apply/idP/idP => [/hasP[jhp /[!mem_filter]/andP[PSERV IN] AHEP] | AHEP].
        { apply service_at_implies_scheduled_at in PSERV.
          have EQ: jhp = j' by apply: H_uniprocessor_proc_model.
          by subst j'. }
        { apply/hasP; exists j' => //.
          by apply receives_service_and_served_at_consistent, ideal_progress_inside_supplies. }
      Qed.

      (** Similarly, we show that the interference from another
          higher-or-equal priority job from another task is equivalent
          to the relation [another_task_hep_job]. *)
      Lemma interference_athep_def :
        another_task_hep_job_interference arr_seq sched j t = another_task_hep_job j' j.
      Proof.
        apply/idP/idP => [/hasP[jhp /[!mem_filter]/andP[PSERV IN] AHEP] | AHEP].
        - apply service_at_implies_scheduled_at in PSERV.
          have EQ: jhp = j' by apply: H_uniprocessor_proc_model.
          by subst.
        - apply/hasP; exists j' => //; rewrite mem_filter; apply/andP; split.
          + by apply: progress_inside_supplies => //.
          + by apply: arrivals_up_to_scheduled_at.
      Qed.

    End SomeJobIsScheduled.

    (** Next, consider a case when [j] itself is scheduled at [t]. *)
    Section JIsScheduled.

      (** Assume that [j] is scheduled at time [t]. *)
      Hypothesis H_j_sched : scheduled_at sched j t.

      (** Then there is no interference from higher-or-equal priority
          jobs at time [t]. *)
      Lemma no_ahep_interference_when_scheduled :
        ~~ another_hep_job_interference arr_seq sched j t.
      Proof.
        apply/negP; move=> /hasP[jhp /[!mem_filter]/andP[PSERV IN] AHEP].
        apply service_at_implies_scheduled_at in PSERV.
        have EQ: jhp = j; [by apply: H_uniprocessor_proc_model | subst jhp].
        by apply another_hep_job_antireflexive in AHEP.
      Qed.

    End JIsScheduled.

    (** Next, consider a case when [j] receives service at [t]. *)
    Section JIsServed.

      (** Assume that [j] receives service at time [t]. *)
      Hypothesis H_j_served : receives_service_at sched j t.

      (** Then there is no interference from higher-or-equal priority
          jobs at time [t]. *)
      Lemma no_ahep_interference_when_served :
        ~~ another_hep_job_interference arr_seq sched j t.
      Proof.
        apply/negP => INT.
        rewrite (interference_ahep_def j) in INT => //; first last.
        - by apply service_at_implies_scheduled_at.
        - by move: INT => /andP [_ ]; rewrite eq_refl.
      Qed.

    End JIsServed.

    (** In the next subsection, we consider a case when a job [j']
        from the same task (as job [j]) is scheduled. *)
    Section FromSameTask.

      (** Consider a job [j'] that comes from task [tsk] and is
          scheduled at time instant [t].  *)
      Variable j' : Job.
      Hypothesis H_j'_tsk : job_of_task tsk j'.
      Hypothesis H_j'_sched : scheduled_at sched j' t.

      (** Then we show that there is no interference from
          higher-or-equal priority jobs of another task. *)
      Lemma no_athep_interference_when_scheduled :
        ~~ another_task_hep_job_interference arr_seq sched j t.
      Proof.
        apply/negP; move=> /hasP[jhp /[!mem_filter]/andP[PSERV IN] AHEP].
        apply service_at_implies_scheduled_at in PSERV.
        have EQ: jhp = j'; [by apply: H_uniprocessor_proc_model | subst jhp].
        by eapply another_task_hep_job_taskwise_antireflexive in AHEP.
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
          interference from another task iff [j'] has higher-or-equal
          priority than [j]. *)
      Lemma athep_interference_iff :
        another_task_hep_job_interference arr_seq sched j t = hep_job j' j.
      Proof.
        apply/idP/idP => [/hasP[j'' /[!mem_filter]/andP[RSERV IN] AHEP] | HEP].
        - apply service_at_implies_scheduled_at in RSERV.
          have EQ: j' = j''; [by apply: H_uniprocessor_proc_model | subst j''].
          by move: AHEP => /andP[].
        - apply/hasP; exists j'; [rewrite !mem_filter|]; apply/andP; split => //.
          + by apply ideal_progress_inside_supplies => //.
          + apply: arrived_between_implies_in_arrivals => //.
            apply/andP; split=> [//|].
            by apply H_jobs_must_arrive_to_execute in H_j'_sched; rewrite ltnS.
          + by apply: contraNN H_j'_not_tsk => /eqP; rewrite /job_of_task => ->.
      Qed.

      (** Hence, if we assume that [j'] has higher-or-equal priority, ... *)
      Hypothesis H_j'_hep : hep_job j' j.

      (** ... we are able to show that [j] incurs higher-or-equal
          priority interference from another task. *)
      Lemma athep_interference_if :
        another_task_hep_job_interference arr_seq sched j t.
      Proof.
        by rewrite athep_interference_iff.
      Qed.

    End FromDifferentTask.

    (** In the last subsection, we consider a case when the scheduled
        job [j'] has lower priority than job [j]. *)
    Section LowerPriority.

      (** Consider a job [j'] that has lower priority than job [j]
            and is scheduled at time instant [t].  *)
      Variable j' : Job.
      Hypothesis H_j'_sched : scheduled_at sched j' t.
      Hypothesis H_j'_lp : ~~ hep_job j' j.

      (** We prove that, in this case, there is no interference from
          higher-or-equal priority jobs at time [t]. *)
      Lemma no_ahep_interference_when_scheduled_lp :
        ~~ another_hep_job_interference arr_seq sched j t.
      Proof.
        apply/negP; move/hasP => [jlp /[!mem_filter]/andP[+ IN] AHEP].
        move/service_at_implies_scheduled_at => RSERV.
        have EQ: j' = jlp; [by apply: H_uniprocessor_proc_model | subst j'].
        by move: (H_j'_lp) AHEP => LP /andP [HEP A]; rewrite HEP in LP.
      Qed.

    End LowerPriority.

  End SupplyAndScheduledJob.

  (** In this section, we prove that the (abstract) cumulative
      interference of jobs with higher or equal priority is equal to
      total service of jobs with higher or equal priority. *)
  Section InstantiatedServiceEquivalences.

    (** First, let us assume that the introduced processor model is
          unit-service. *)
    Hypothesis H_unit_service : unit_service_proc_model PState.

    (** Consider any job [j] of [tsk]. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.

    (** We consider an arbitrary time interval <<[t1, t)>> that starts
        with a (classic) quiet time. *)
    Variable t1 t : instant.
    Hypothesis H_quiet_time : classical.quiet_time arr_seq sched j t1.

    (** As follows from lemma [cumulative_pred_served_eq_service], the
        (abstract) instantiated function of interference is equal to
        the total service of any subset of jobs with higher or equal
        priority. *)

    (** The above is in particular true for the jobs other than [j]
        with higher or equal priority... *)
    Lemma  cumulative_i_ohep_eq_service_of_ohep :
      cumulative_another_hep_job_interference arr_seq sched j t1 t
      = service_of_other_hep_jobs arr_seq sched j t1 t.
    Proof.
      apply: cumulative_pred_served_eq_service => //.
      - by move => ? /andP[].
    Qed.

    (** ...and for jobs from other tasks than [j] with higher
        or equal priority. *)
    Lemma cumulative_i_thep_eq_service_of_othep :
      cumulative_another_task_hep_job_interference arr_seq sched j t1 t
      = service_of_other_task_hep_jobs arr_seq sched j t1 t.
    Proof.
      apply: cumulative_pred_served_eq_service => //.
      by move => ? /andP[].
    Qed.

  End InstantiatedServiceEquivalences.

End InterferencePropertiesJLFP.
