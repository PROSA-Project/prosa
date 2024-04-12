Require Export prosa.analysis.definitions.interference.
Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.abstract.restricted_supply.busy_prefix.
Require Export prosa.model.aggregate.service_of_jobs.
Require Export prosa.analysis.facts.model.service_of_jobs.


(** * Auxiliary Lemmas About Interference and Interfering Workload. *)

(** In this file we provide a set of auxiliary lemmas about generic
    properties of Interference and Interfering Workload. *)
Section InterferenceAndInterferingWorkloadAuxiliary.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

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

  (** For convenience, we define a function that "folds" cumulative
      conditional interference with a predicate [fun _ _ => true] to
      cumulative (unconditional) interference. *)
  Lemma fold_cumul_interference :
    forall j t1 t2,
      cumul_cond_interference (fun _ _ => true) j t1 t2
      = cumulative_interference j t1 t2.
  Proof. by rewrite /cumulative_interference. Qed.

  (** In this section, we prove a few basic properties of conditional
      interference w.r.t. a generic predicate [P]. *)
  Section CondInterferencePredicate.

    (** In the following, consider a predicate [P]. *)
    Variable P : Job -> instant -> bool.

    (** First, we show that the cumulative conditional interference
        within a time interval <<[t1, t2)>> can be rewritten as a sum
        over all time instances satisfying [P j]. *)
    Lemma cumul_cond_interference_alt :
      forall j t1 t2,
        cumul_cond_interference P j t1 t2 = \sum_(t1 <= t < t2 | P j t) interference j t.
    Proof.
      move=> j t1 t2; rewrite [RHS]big_mkcond //=; apply eq_big_nat => t _.
      by rewrite /cond_interference; case: (P j t).
    Qed.

    (** Next, we show that cumulative interference on an interval
        <<[al, ar)>> is bounded by the cumulative interference on an
        interval <<[bl,br)>> if <<[al,ar)>> ⊆ <<[bl,br)>>. *)
    Lemma cumulative_interference_sub :
      forall (j : Job) (al ar bl br : instant),
        bl <= al ->
        ar <= br ->
        cumul_cond_interference P j al ar <= cumul_cond_interference P j bl br.
    Proof.
      move => j al ar bl br LE1 LE2.
      rewrite !cumul_cond_interference_alt.
      case: (leqP al ar) => [LEQ|LT]; last by rewrite big_geq.
      rewrite [leqRHS](@big_cat_nat _ _ _ al) //=; last by lia.
      by rewrite [in X in _ <= _ + X](@big_cat_nat _ _ _ ar) //=; lia.
    Qed.

    (** We show that the cumulative interference of a job can be split
        into disjoint intervals. *)
    Lemma cumulative_interference_cat :
      forall j t t1 t2,
        t1 <= t <= t2 ->
        cumul_cond_interference P j t1 t2
        = cumul_cond_interference P j t1 t + cumul_cond_interference P j t t2.
    Proof.
      move => j t t1 t2 /andP [LE1 LE2].
      by rewrite !cumul_cond_interference_alt {1}(@big_cat_nat _ _ _ t) //=.
    Qed.

  End CondInterferencePredicate.

  (** Next, we show a few relations between interference functions
      conditioned on different predicates. *)
  Section CondInterferenceRelation.

    (** Consider predicates [P1, P2]. *)
    Variables P1 P2 : Job -> instant -> bool.

    (** We introduce a lemma (similar to ssreflect's [bigID] lemma)
        that allows us to split the cumulative conditional
        interference w.r.t predicate [P1] into a sum of two cumulative
        conditional interference w.r.t. predicates [P1 && P2] and [P1
        && ~~ P2], respectively. *)
    Lemma cumul_cond_interference_ID :
      forall j t1 t2,
        cumul_cond_interference P1 j t1 t2
        = cumul_cond_interference (fun j t => P1 j t && P2 j t) j t1 t2
          + cumul_cond_interference (fun j t => P1 j t && ~~ P2 j t) j t1 t2.
    Proof.
      move=> j t1 t2.
      rewrite -big_split //=; apply eq_bigr => t _.
      rewrite /cond_interference.
      by case (P1 _ _), (P2 _ _ ), (interference _ _).
    Qed.

    (** If two predicates [P1] and [P2] are equivalent, then they can
        be used interchangeably with [cumul_cond_interference]. *)
    Lemma cumul_cond_interference_pred_eq :
      forall (j : Job) (t1 t2 : instant),
        (forall j t, P1 j t <-> P2 j t) ->
        cumul_cond_interference P1 j t1 t2
        = cumul_cond_interference P2 j t1 t2.
    Proof.
      move=> j t1 t2 EQU.
      apply eq_bigr => t _; rewrite /cond_interference.
      move: (EQU j t).
      by case (P1 j t), (P2 j t), (interference _ _); move=> CONTR => //=; exfalso; apply notF, CONTR.
    Qed.

  End CondInterferenceRelation.

  (** In the following, consider a JLFP-policy that indicates a
      higher-or-equal priority relation, and assume that this relation
      is reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** If there is a priority policy in the context, one can
      differentiate between interference (interfering workload) that
      comes from jobs with higher or lower priority from other sources
      of interference (interfering workload).

      Unfortunately, instantiated functions usually do not come with
      any useful lemmas about them. In order to reuse existing lemmas,
      we need to prove equivalence of the instantiated functions to
      some conventional notions.

      Next, we prove these equivalences formally. *)
  Section Equivalences.

    (** First, we prove a few rewriting rules under the assumption
        that there is no supply. *)
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

    (** Next, we prove properties of the introduced functions under
        the assumption that there is supply and the scheduler is not
        idle. *)
    Section SupplyAndScheduledJob.

      (** Consider a job [j] of task [tsk]. In this subsection, job
          [j] is deemed to be the main job with respect to which the
          functions are computed. *)
      Variable j : Job.
      Hypothesis H_j_tsk : job_of_task tsk j.

      (** Consider a time instant [t] ... *)
      Variable t : instant.

      (** ... and assume that there is supply at [t]. *)
      Hypothesis H_supply : has_supply sched t.

      (** First, consider a case when _some_ job is scheduled at time [t]. *)
      Section SomeJobIsScheduled.

        (** Consider a job [j'] (not necessarily distinct from job
            [j]) that is scheduled at time [t]. *)
        Variable j' : Job.
        Hypothesis H_sched : scheduled_at sched j' t.

        (** Under the stated assumptions, we show that the
            interference from another higher-or-equal priority job is
            equivalent to the relation [another_hep_job]. *)
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
            higher-or-equal priority job from another task is
            equivalent to the relation [another_task_hep_job]. *)
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

        (** Then there is no interference from higher-or-equal
            priority jobs at time [t]. *)
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

        (** Then there is no interference from higher-or-equal
            priority jobs at time [t]. *)
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
            interference from another task iff [j'] has
            higher-or-equal priority than [j]. *)
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

      (** In the last subsection, we consider a case when the
          scheduled job [j'] has lower priority than job [j]. *)
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

      (** We consider an arbitrary time interval <<[t1, t)>> that
          starts with a (classic) quiet time. *)
      Variable t1 t : instant.
      Hypothesis H_quiet_time : classical.quiet_time arr_seq sched j t1.

      (** As follows from lemma [cumulative_pred_served_eq_service],
          the (abstract) instantiated function of interference is
          equal to the total service of any subset of jobs with higher
          or equal priority. *)

      (** The above is in particular true for the jobs other
          than [j] with higher or equal priority... *)
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


  End Equivalences.

End InterferenceAndInterferingWorkloadAuxiliary.
