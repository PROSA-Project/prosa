Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.analysis.abstract.search_space.
Require Export prosa.analysis.abstract.lower_bound_on_service.

(** * Abstract Response-Time Analysis *)
(** In this module, we propose the general framework for response-time
    analysis (RTA) of uni-processor scheduling of real-time tasks with
    arbitrary arrival models. *)
(** We prove that the maximum (with respect to the set of offsets)
    among the solutions of the response-time bound recurrence is a
    response-time bound for the task under analysis. *)
Section Abstract_RTA.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context {jc : JobCost Job}.

  (** Consider _any_ kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival and any schedule of this arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Variable sched : schedule PState.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Consider a task set [ts]... *)
  Variable ts : list Task.

  (** ... and a task [tsk] of [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** We assume that the scheduler is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Let [L] be a constant that bounds the length of any busy interval of task [tsk]. *)
  Variable L : duration.
  Hypothesis H_bounded_busy_interval_exists :
    busy_intervals_are_bounded_by arr_seq sched tsk L.

  (** Note that response-time analyses are static analyses and by
      definition have no access to dynamic information of an
      individual execution of a system. However, oftentimes some
      dynamic information can improve the tightness of a response-time
      bound. For example, in case of a model with sequential tasks,
      information about relative arrival time of a job can be used to
      bound the maximum self-interference. *)

  (** To gain access to some dynamic information for a response-time
      recurrence, one can _assume_ that an execution of a system
      satisfies a statically defined predicate. Then a response-time
      bound can be calculated by considering a family of inputs to the
      predicate that covers all the relevant dynamic scenarios.

      To give a concrete example, one can (1) assume that any job [j]
      of a task [tsk] arrives exactly [A] time units after the
      beginning of [j]'s busy interval, (2) calculate the
      response-time bound of [tsk] as if the assumption of step (1)
      was satisfied, and (3) try all the possible [A]s. That results
      in a "relative-arrival"-aware analysis. *)

  (** The idea we will employ in this file is that one can use more
      sophisticated dynamic information in a response-time recurrence.
      In the following, we consider a case when information about (1)
      relative arrival time of a job and (2) relative time when any
      job of task [tsk] receives at least [task_rtc tsk] units of
      service is used in the response-time recurrence. *)

  (** Next, the response-time analysis will proceed in a sequence of
      stages. A stage defines the set of sources of interference that
      can postpone the execution of a job. Note that this separation
      is mostly a design question. And for different models there might be
      a varying number of stages with different meanings. *)

  (** For our purposes, we consider two stages. *)

  (** First stage: A job [j] can be (1) preempted because of the
      presence of higher-or-equal priority workload and (2) make no
      progress due to some other reason (spinning, lack of supply, and
      so on). To bound all this interference we introduce an
      interference bound function [IBF_P]. Note that [IBF_P] (1)
      counts any job with higher-or-equal priority as interference and
      (2) depends on the relative arrival time of a job. To bound time
      that [j] spends in the first stage, we need to find a fixpoint
      of equation [F : task_rtc tsk + IBF_P tsk A F ≤ F]. *)

  (** To formalize the dependency of [IBF_P] on the relative arrival
      time in Coq, we introduce a predicate that tests whether a job
      [j] arrives exactly [A] time units after the beginning of its
      busy interval, which is unique (if it exists). *)
  Definition relative_arrival_time_of_job_is_A (j : Job) (A : duration) :=
    forall (t1 t2 : instant),
      busy_interval sched j t1 t2 ->
      A = job_arrival j - t1.

  (** Next, consider a valid interference bound function [IBF_P] that
      can use information about relative time arrival of a job of task
      [tsk]. Recall that an interference bound function gives a bound on
      the cumulative interference incurred by jobs of task [tsk]. *)
  Variable IBF_P : Task -> (* A *) duration -> (* Δ *) duration -> duration.
  Hypothesis H_job_interference_is_bounded_IBFP :
    job_interference_is_bounded_by
      arr_seq sched tsk IBF_P relative_arrival_time_of_job_is_A.

  (** Second stage: Job [j] reaches its run-to-completion
      threshold. After this point the job cannot be preempted by a
      high-or-equal priority job (so we can forget about any
      task-generated workload). At this stage, the only reason why the
      job cannot make progress is due to lack of supply or similar. To
      bound time that [j] spends in the second stage we use
      [IBF_NP]. Note that the amount of interference may depend on the
      relative time when job [j] receives [task_rtc tsk] units of
      service; hence, [IBF_NP] depends on this parameter. Also, notice
      that [IBF_NP] still bounds interference starting from the
      beginning of the busy window, even though it can use the
      solution of the first fixpoint equation. *)

  (** To formalize the dependency of [IBF_NP] on the relative time
      when job [j] receives [task_rtc tsk] units of service in Coq, we
      introduce a predicate that tests whether a job [j] has more than
      [task_rtc tsk] units of service at a time instant [t1 + F],
      where [t1] is the beginning of [j]'s busy interval. The first
      conjunct of the proposition is needed to derive a fact that by
      time [t1 + F] job [j] does not receive any interference from
      higher-or-equal priority jobs. *)
  Definition relative_time_to_reach_rtct (j : Job) (F : duration) :=
    forall (t1 t2 : instant),
      busy_interval sched j t1 t2 ->
      task_rtct tsk + IBF_P tsk (job_arrival j - t1) F <= F /\
      task_rtct tsk <= service sched j (t1 + F).

  (** Next, consider a valid interference bound function [IBF_NP] that
      can use information about the relative time when any given job of task
      [tsk] receives at least [task_rtc tsk] units of service. *)
  Variable IBF_NP : Task -> (* F *) duration -> (* Δ *) duration -> duration.
  Hypothesis H_job_interference_is_bounded_IBFNP:
    job_interference_is_bounded_by
      arr_seq sched tsk IBF_NP relative_time_to_reach_rtct.

  (** In addition, we assume that [IBF_NP] indeed takes into account
      information received in the first stage. Specifically, we assume
      that the sum of [tsk]'s cost and [IBF_NP tsk F Δ] is never smaller
      than [F]. This intuitively means that the second stage cannot
      have a solution that is smaller than the solution to the first
      stage. *)
  Hypothesis H_IBF_NP_ge_param : forall F Δ, F <= task_cost tsk + IBF_NP tsk F Δ.


  (** Given [IBF_P] and [IBF_NP] we construct a response-time recurrence. *)

  (** For clarity, let's define a local name for the search space. *)
  Let is_in_search_space A := is_in_search_space tsk L IBF_P A.

  (** We use the following equation to bound the response-time of a
      job of task [tsk]. Consider any value [R] that upper-bounds the
      solution of each response-time recurrence, i.e., for any
      relative arrival time [A] in the search space, there exists a
      corresponding solution [F] such that [task_rtc tsk + IBF_P tsk A
      F ≤ F] and [task_cost tsk + IBF_NP tsk F (A + R) ≤ A + R]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum :
    forall (A : duration),
      is_in_search_space A ->
      exists (F : duration),
        task_rtct tsk + IBF_P tsk A F <= F /\
        task_cost tsk + IBF_NP tsk F (A + R) <= A + R.

  (** * Proof of the Theorem *)
  (** In the next section we show a detailed proof of the main theorem
      that establishes that [R] is indeed a response-time bound of
      task [tsk]. *)
  Section ProofOfTheorem.

    (** Consider any job [j] of [tsk] with a positive cost. Note that
        the assumption about positive job cost is needed to apply
        hypothesis [H_bounded_busy_interval_exists]. Later, we
        consider the case when [job_cost j = 0] as well. This way, we
        ensure that this assumption does not propagate further. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Assume we have a busy interval <<[t1, t2)>> of job [j]. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_interval : busy_interval sched j t1 t2.

    (** Let's define [A] as a relative arrival time of job
        [j] (with respect to time [t1]). *)
    Let A := job_arrival j - t1.

    (** First, note that [job_arrival j] is equal to [t1 + A]. *)
    Fact job_arrival_eq_t1_plus_A : job_arrival j = t1 + A.
    Proof. by move: H_busy_interval => [[/andP [GT LT] _] _]; rewrite /A subnKC. Qed.

    (** Since the length of the busy interval is bounded by [L], the
        relative arrival time [A] of job [j] is less than [L]. *)
    Fact relative_arrival_is_bounded : A < L.
    Proof.
      move: (H_job_of_tsk) => /eqP TSK.
      edestruct H_bounded_busy_interval_exists as [t1' [t2' [_ [BOUND BUSY]]]] => //.
      edestruct busy_interval_is_unique; [exact H_busy_interval | exact BUSY| ].
      subst t1' t2'; clear BUSY.
      apply leq_trans with (t2 - t1); last by rewrite leq_subLR.
      move: (H_busy_interval)=> [[/andP [T1 T3] [_ _]] _].
        by apply ltn_sub2r; first apply leq_ltn_trans with (job_arrival j).
    Qed.

    (** In order to prove that [R] is a response-time bound of job
        [j], we use hypothesis [H_R_is_maximum]. Note that the
        relative arrival time [A] does not necessarily belong to the
        search space. However, earlier (see file
        [abstract.search_space]) we have proven that for any [A] there
        exists another [A_sp] from the search space that shares the
        same [IBF_P] value.

        Moreover, since the function [IBF_P(A, ⋅)] is equivalent to
        the function [IBF_P(A_sp, ⋅)], a solution [F] for [task_rtc
        tsk + IBF_P tsk A_sp F ≤ F] also is a solution for [task_rtc
        tsk + IBF_P tsk A F ≤ F]. Thus, despite the fact that the
        relative arrival time may not lie in the search space, we can
        still use the assumption [H_R_is_maximum]. *)

    (** More formally, consider any [A_sp] such that: *)
    Variable A_sp : duration.

    (** (a) [A_sp] is less than or equal to [A]. *)
    Hypothesis H_Asp_le_A : A_sp <= A.

    (** (b) [IBF_P A x] is equal to [IBF_P A_sp x] for all [x] less than [L]. *)
    Hypothesis H_equivalent :
      are_equivalent_at_values_less_than (IBF_P tsk A) (IBF_P tsk A_sp) L.

    (** (c) [A_sp] is in the search space. *)
    Hypothesis H_Asp_is_in_search_space : is_in_search_space A_sp.

    (** (d) [F] such that ...  *)
    Variable F : duration.

    (** ... [F] is a solution of the response-time recurrence. *)
    Hypothesis H_F_fixpoint : task_rtct tsk + IBF_P tsk A_sp F <= F.

    (** And finally, (e) [task_cost tsk + IBF_NP tsk F (A_sp + R)] is
        no greater than [A_sp + R]. *)
    Hypothesis H_Asp_R_fixpoint :
      task_cost tsk + IBF_NP tsk F (A_sp + R) <= A_sp + R.

    (** ** Case 1 *)

    (** First, we consider the case where the solution [F] is so large
        that the value of [t1 + F] goes beyond the busy
        interval. Depending on the pessimism of [IBF_P] and [IBP_NP]
        this might be either possible or impossible. Regardless, the
        response-time bound can be easily proven, since any job that
        completes by the end of the busy interval remains
        completed. *)
    Section FixpointOutsideBusyInterval1.

      (** By assumption, suppose that [t2] is less than or equal to [t1 + F]. *)
      Hypothesis H_big_fixpoint_solution : t2 <= t1 + F.

      (** Then we prove that [job_arrival j + R] is no less than [t2]. *)
      Lemma t2_le_arrival_plus_R_1 :
        t2 <= job_arrival j + R.
      Proof.
        move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
        apply leq_trans with (t1 + F) => [//|].
        rewrite job_arrival_eq_t1_plus_A -addnA leq_add2l.
        rewrite -(leqRW H_Asp_le_A) -(leqRW H_Asp_R_fixpoint).
        by apply H_IBF_NP_ge_param.
      Qed.

      (** But since we know that the job is completed by the end of
          its busy interval, we can show that job [j] is completed by
          [job arrival j + R]. *)
      Lemma job_completed_by_arrival_plus_R_1 :
        completed_by sched j (job_arrival j + R).
      Proof.
        move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
        apply completion_monotonic with t2 => //.
        exact: t2_le_arrival_plus_R_1.
      Qed.

    End FixpointOutsideBusyInterval1.

    (** ** Case 2 *)
    (** Next, we consider the case where the solution of the first
        recurrence is small ([t1 + F < t2]), but the solution of the
        second fixpoint goes beyond the busy interval. Although this
        case may be (also) impossible, the response-time bound can be
        easily proven, since any job that completes by the end of the
        busy interval remains completed. *)
    Section FixpointOutsideBusyInterval2.

      (** Assume that [t1 + F] is less than [t2], ... *)
      Hypothesis H_small_fixpoint_solution : t1 + F < t2.

      (** ... but [t1 + (A_sp + R)] is at least [t2]. *)
      Hypothesis H_big_fixpoint_solution : t2 <= t1 + (A_sp + R).

      (** Then we prove that [job_arrival j + R] is no less than [t2]. *)
      Lemma t2_le_arrival_plus_R_2 :
        t2 <= job_arrival j + R.
      Proof.
        move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
        apply leq_trans with (t1 + (A_sp + R)) => [//|].
        by rewrite job_arrival_eq_t1_plus_A -addnA leq_add2l leq_add2r.
      Qed.

      (** But since we know that the job is completed by the end of
          its busy interval, we can show that job [j] is completed by
          [job arrival j + R]. *)
      Lemma job_completed_by_arrival_plus_R_2 :
        completed_by sched j (job_arrival j + R).
      Proof.
        move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
        apply completion_monotonic with t2.
        - exact: t2_le_arrival_plus_R_2.
        - exact: job_completes_within_busy_interval.
      Qed.

    End FixpointOutsideBusyInterval2.

    (** ** Case 3 *)
    (** Next, we consider the case when both solutions are smaller
        than the length of the busy interval. *)
    Section FixpointsInsideBusyInterval.

      (** So, assume that [t1 + F] and [t1 + (A_sp + R)] are both
          smaller than [t2]. *)
      Hypothesis H_small_fixpoint_solution1 : t1 + F < t2.
      Hypothesis H_small_fixpoint_solution2 : t1 + (A_sp + R) < t2.

      (** First note that [F] is indeed less than [L]. *)
      Lemma relative_rtc_time_is_bounded : F < L.
      Proof.
        edestruct H_bounded_busy_interval_exists as [t1' [t2' [_ [BOUND BUSY]]]]; eauto 2.
        edestruct busy_interval_is_unique; [exact H_busy_interval | exact BUSY| ].
        subst t1' t2'; clear BUSY.
        apply leq_trans with (t2 - t1); last by rewrite leq_subLR.
        by rewrite ltn_subRL.
      Qed.

      (** Next we consider two sub-cases. *)

      (** *** Case 3.1 *)
      (** The cost of job [j] is smaller than or equal to the
          run-to-completion threshold of task [tsk]. *)
      Section JobCostIsSmall.

        (** We assume that [job_cost j <= task_rtc tsk]. *)
        Hypothesis H_job_cost_is_small : job_cost j <= task_rtct tsk.

        (** Then we apply lemma [j_receives_enough_service] with
            parameters [progress_of_job := job_cost j] and [delta :=
            F] to obtain the fact that the service of [j] by time [t1
            + F] is no less than [job_cost j] (that is, the job is
            completed). *)
        Lemma job_receives_enough_service_1 :
          job_cost j <= service sched j (t1 + F).
        Proof.
          move_neq_up T; move: (T) => NC; move_neq_down T.
          eapply j_receives_enough_service; eauto 2;
            rewrite /definitions.cumulative_interference.
          rewrite -{2}(leqRW H_F_fixpoint).
          rewrite leq_add //.
          rewrite -H_equivalent; [ | apply relative_rtc_time_is_bounded].
          eapply H_job_interference_is_bounded_IBFP with t2 => //.
          + by rewrite -ltnNge.
          + move => t1' t2' BUSY.
            edestruct busy_interval_is_unique; [exact H_busy_interval | exact BUSY| ].
            by subst t1' t2'; rewrite job_arrival_eq_t1_plus_A; lia.
        Qed.

      End JobCostIsSmall.

      (** *** Case 3.2 *)
      (** The cost of job [j] is greater than or equal to
          the run-to-completion threshold of task [tsk ]. *)
      Section JobCostIsBig.

        (** We assume that [task_rtc tsk <= job_cost j]. *)
        Hypothesis H_job_cost_is_big : task_rtct tsk <= job_cost j.

        (** We apply lemma [j_receives_enough_service] with parameters
            [progress_of_job := task_rtc tsk] and [delta := F] to
            obtain the fact that the service of [j] by time [t1 + F]
            is no less than [task_rtc tsk]. *)
        Lemma job_receives_enough_service_2 :
          task_rtct tsk <= service sched j (t1 + F).
        Proof.
          move_neq_up T; move: (T) (H_job_of_tsk) => NC /eqP TSK; move_neq_down T.
          eapply j_receives_enough_service => //.
          rewrite /definitions.cumulative_interference.
          erewrite leq_trans; last apply H_F_fixpoint; auto.
          rewrite leq_add //.
          rewrite -H_equivalent; [ | apply relative_rtc_time_is_bounded].
          eapply H_job_interference_is_bounded_IBFP with t2 => //.
          + by rewrite -ltnNge (leqRW NC).
          + intros t0 t3 BUSY.
            edestruct busy_interval_is_unique; [exact H_busy_interval | exact BUSY| ].
            subst t0 t3; clear BUSY.
            by rewrite job_arrival_eq_t1_plus_A; lia.
        Qed.

        (** Next, we again apply lemma [j_receives_enough_service]
            with parameters [progress_of_job := job_cost j] and [delta
            := A_sp + R] to obtain the fact that the service of [j] by
            time [t1 + (A_sp + R)] is no less than [job_cost j]. *)
        Lemma job_receives_enough_service_3 :
          job_cost j <= service sched j (t1 + (A_sp + R)).
        Proof.
          move: (H_job_of_tsk) => /eqP TSK.
          apply/negPn/negP; intros NC; move: NC => /negP NC; apply NC; move: NC => /negP NC.
          apply: j_receives_enough_service => //.
          erewrite leq_trans; [ | | apply H_Asp_R_fixpoint]; auto.
          apply leq_add; [by rewrite -TSK; apply H_valid_job_cost | ].
          eapply H_job_interference_is_bounded_IBFNP with (t2 := t2); eauto 2.
          intros t0 t3 BUSY.
          edestruct busy_interval_is_unique; [exact H_busy_interval | exact BUSY| ].
          subst t0 t3; clear BUSY; split.
          - by rewrite H_equivalent //; apply relative_rtc_time_is_bounded.
          - by rewrite -(leqRW job_receives_enough_service_2).
        Qed.

      End JobCostIsBig.

      (** Either way, job [j] is completed by time [job_arrival j + R]. *)
      Lemma job_is_completed_by_arrival_plus_R :
        completed_by sched j (job_arrival j + R).
      Proof.
        edestruct (leqP (job_cost j) (task_rtct tsk)) as [LE|LE].
        - eapply completion_monotonic; [ | eapply job_receives_enough_service_1; auto].
          apply leq_trans with (t1 + (A_sp + R));
            [ rewrite leq_add2l; eapply leq_trans; [ | apply H_Asp_R_fixpoint]; eauto
            | by rewrite job_arrival_eq_t1_plus_A -addnA leq_add2l leq_add2r].
        - eapply completion_monotonic; [ | eapply job_receives_enough_service_3; auto].
          by rewrite addnA leq_add2r job_arrival_eq_t1_plus_A leq_add2l.
      Qed.

    End FixpointsInsideBusyInterval.

  End ProofOfTheorem.

  (** * Response-Time Bound *)

  (** Using the lemmas above, we prove that [R] is a response-time bound. *)
  Theorem uniprocessor_response_time_bound:
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => j ARR JOBtsk; unfold job_response_time_bound.
    move: (posnP (@job_cost _ jc j)) => [ZERO|POS].
    { by rewrite /completed_by ZERO. }
    move: (H_bounded_busy_interval_exists  _ ARR JOBtsk POS) => [t1 [t2 [NEQ [T2 BUSY]]]].
    move: (relative_arrival_is_bounded _ ARR JOBtsk POS _ _ BUSY) => AltL.
    move: (representative_exists tsk _ IBF_P _ AltL) => [A__sp [ALEA2 [EQΦ INSP]]].
    set (A := job_arrival j - t1) in *.
    move: (H_R_is_maximum _ INSP) => [F [FIX1 FIX2]].
    edestruct (leqP t2 (t1 + F)) as [LE1|LE1];
      [ | edestruct (leqP t2 (t1 + (A__sp + R))) as [LE2|LE2]].
    - by eapply job_completed_by_arrival_plus_R_1; eauto.
    - by eapply job_completed_by_arrival_plus_R_2; eauto.
    - by eapply job_is_completed_by_arrival_plus_R with (A_sp := A__sp); eauto 2.
  Qed.

End Abstract_RTA.
