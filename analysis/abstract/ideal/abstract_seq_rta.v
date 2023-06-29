Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.model.task_arrivals.
Require Export prosa.analysis.facts.model.task_schedule.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.abstract.ideal.abstract_rta.
Require Export prosa.analysis.abstract.IBF.task.

(** * Abstract Response-Time Analysis with sequential tasks *)
(** In this section we propose the general framework for response-time
    analysis (RTA) of uni-processor scheduling of real-time tasks with
    arbitrary arrival models and sequential tasks. *)

(** We prove that the maximum among the solutions of the response-time
    bound recurrence for some set of parameters is a response-time
    bound for [tsk].  Note that in this section we _do_ rely on the
    hypothesis about task sequentiality. This allows us to provide a
    more precise response-time bound function, since jobs of the same
    task will be executed strictly in the order they arrive. *)
Section Sequential_Abstract_RTA.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context {jc : JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any kind of ideal uni-processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.
  Hypothesis H_ideal_progress_proc_model : ideal_progress_proc_model PState.

  (** Consider any valid arrival sequence with consistent, non-duplicate arrivals...*)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any ideal schedule of this arrival sequence. *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Consider an arbitrary task set. *)
  Variable ts : list Task.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model ... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
      is, [task_rtct tsk] is (1) no bigger than [tsk]'s cost, (2) for
      any job of task [tsk] [job_rtct] is bounded by [task_rtct]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e.,
      for any task [tsk] in [ts], [max_arrival tsk] is (1) an arrival
      bound of [tsk], and (2) it is a monotonic function that equals
      [0] for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let arrivals_between := arrivals_between arr_seq.

  (** When assuming sequential tasks, we need to introduce an
      additional hypothesis to ensure that the values of interference
      and workload remain consistent with the priority policy.

      To understand why, let us consider a case where the sequential
      task assumption does _not_ hold, and then work
      backwards. Consider a fully preemptive policy that assigns the
      highest priority to the job that was released _last_. Then, if
      there is a pending job [j] of a task [tsk], it is not a part of
      a busy interval of the next job [j'] of the same task. In this
      case, both the interference and the interfering workload of job
      [j'] will simply ignore job [j]. Thus, it is possible to have a
      quiet time (for [j']) even though [j] is pending.

      Now, assuming that our priority policy ensures that tasks are
      sequential, the situation described above is impossible (job [j]
      will always have a higher-or-equal priority than job [j']).
      Hence, we need to rule our interference and interfering workload
      instantiations that do not conform to the sequential tasks
      assumption.

      We ensure the consistency by assuming that, when a busy interval
      of a job [j] of task [tsk] starts, both the cumulative task
      workload and the task service must be equal within the interval
      <<[0, t1)>>. This implies that a busy interval for job [j]
      cannot start if there is another pending job of the same task
      [tsk].*)
  Definition interference_and_workload_consistent_with_sequential_tasks :=
    forall (j : Job) (t1 t2 : instant),
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost j > 0 ->
      busy_interval sched j t1 t2 ->
      task_workload_between arr_seq tsk 0 t1
      = task_service_of_jobs_in sched tsk (arrivals_between 0 t1) 0 t1.

  (** In this section, we prove that the maximum among the solutions
      of the response-time bound recurrence is a response-time bound
      for [tsk]. *)
  Section ResponseTimeBound.

    (** We assume that the schedule is work-conserving. *)
    Hypothesis H_work_conserving : work_conserving arr_seq sched.

    (** Unlike the previous theorem
        [uniprocessor_response_time_bound_ideal], we assume that (1)
        tasks are sequential, moreover (2) functions interference and
        interfering_workload are consistent with the hypothesis of
        sequential tasks. *)
    Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.
    Hypothesis H_interference_and_workload_consistent_with_sequential_tasks :
      interference_and_workload_consistent_with_sequential_tasks.

    (** Assume we have a constant [L] that bounds the busy interval of
        any of [tsk]'s jobs. *)
    Variable L : duration.
    Hypothesis H_busy_interval_exists:
      busy_intervals_are_bounded_by arr_seq sched tsk L.

    (** Next, we assume that [task_IBF] is a
        bound on interference incurred by the task. *)
    Variable task_IBF : Task -> duration -> duration -> duration.
    Hypothesis H_task_interference_is_bounded :
      task_interference_is_bounded_by arr_seq sched tsk task_IBF.

    (** Given any job [j] of task [tsk] that arrives exactly [A] units
        after the beginning of the busy interval, the bound on the
        total interference incurred by [j] within an interval of
        length [Δ] is no greater than [task_rbf (A + ε) - task_cost
        tsk + task's IBF Δ]. Note that in case of sequential tasks the
        bound consists of two parts: (1) the part that bounds the
        interference received from other jobs of task [tsk] --
        [task_rbf (A + ε) - task_cost tsk] and (2) any other
        interference that is bounded by [task_IBF(tsk, A, Δ)]. *)
    Let total_interference_bound (tsk : Task) (A Δ : duration) :=
      task_rbf (A + ε) - task_cost tsk + task_IBF tsk A Δ.

    (** Note that since we consider the modified interference bound
        function, the search space has also changed. One can see that
        the new search space is guaranteed to include any A for which
        [task_rbf (A) ≠ task_rbf (A + ε)], since this implies the fact
        that [total_interference_bound (tsk, A, Δ) ≠
        total_interference_bound (tsk, A + ε, Δ)]. *)
    Let is_in_search_space_seq := is_in_search_space tsk L total_interference_bound.

    (** Consider any value [R], and assume that for any relative
        arrival time [A] from the search space there is a solution [F]
        of the response-time recurrence that is bounded by [R]. In
        contrast to the formula in "non-sequential" Abstract RTA,
        assuming that tasks are sequential leads to a more precise
        response-time bound. Now we can explicitly express the
        interference caused by other jobs of the task under
        consideration.

        To understand the right part of the fix-point in the equation,
        it is helpful to note that the bound on the total interference
        ([bound_of_total_interference]) is equal to [task_rbf (A + ε)
        - task_cost tsk + task_IBF tsk A Δ]. Besides, a job must
        receive enough service to become non-preemptive
        [task_lock_in_service tsk]. The sum of these two quantities is
        exactly the right-hand side of the equation. *)
    Variable R : duration.
    Hypothesis H_R_is_maximum_seq :
      forall (A : duration),
        is_in_search_space_seq A ->
        exists (F : duration),
          A + F >= (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk)) + task_IBF tsk A (A + F) /\
          R >= F + (task_cost tsk - task_rtct tsk).

    (** In this section we prove a few simple lemmas about the
        completion of jobs from the task considering the busy interval
        of the job under consideration. *)
    Section CompletionOfJobsFromSameTask.

      (** Consider any two jobs [j1] [j2] of [tsk]. *)
      Variable j1 j2 : Job.
      Hypothesis H_j1_arrives : arrives_in arr_seq j1.
      Hypothesis H_j2_arrives : arrives_in arr_seq j2.
      Hypothesis H_j1_from_tsk : job_of_task tsk j1.
      Hypothesis H_j2_from_tsk : job_of_task tsk j2.
      Hypothesis H_j1_cost_positive : job_cost_positive j1.

      (** Consider the busy interval <<[t1, t2)>> of job j1. *)
      Variable t1 t2 : instant.
      Hypothesis H_busy_interval : busy_interval sched j1 t1 t2.

      (** We prove that if a job from task [tsk] arrived before the beginning of the busy
         interval, then it must be completed before the beginning of the busy interval *)
      Lemma completed_before_beginning_of_busy_interval:
        job_arrival j2 < t1 ->
        completed_by sched j2 t1.
      Proof.
        move => JA; move: (H_j2_from_tsk) => /eqP TSK2eq.
        move: (posnP (@job_cost _ jc j2)) => [ZERO|POS].
        { by rewrite /completed_by /service.completed_by ZERO. }
        move: (H_interference_and_workload_consistent_with_sequential_tasks
                 j1 t1 t2 H_j1_arrives H_j1_from_tsk H_j1_cost_positive H_busy_interval) => SWEQ.
        by eapply all_jobs_have_completed_equiv_workload_eq_service with (j := j2) in SWEQ.
      Qed.

      (** Next we prove that if a job is pending after the beginning
          of the busy interval <<[t1, t2)>> then it arrives after
          [t1]. *)
      Lemma arrives_after_beginning_of_busy_interval:
        forall t,
          t1 <= t ->
          pending sched j2 t ->
          arrived_between j2 t1 t.+1.
      Proof.
        move => t GE PEND.
        rewrite /arrived_between; apply/andP; split; last first.
        { by move: PEND => /andP [ARR _]; rewrite ltnS. }
        rewrite leqNgt; apply/negP; move => LT.
        move: (H_busy_interval) => [[/andP [AFR1 AFR2] [QT _]] _].
        have L12 := completed_before_beginning_of_busy_interval LT.
        apply completion_monotonic with (t' := t) in L12 => //.
        by move: PEND => /andP [_ /negP T2].
      Qed.

    End CompletionOfJobsFromSameTask.

    (** Since we are going to use the
        [uniprocessor_response_time_bound_ideal] theorem to prove the
        theorem of this section, we have to show that all the
        hypotheses are satisfied. Namely, we need to show that
        hypotheses [H_sequential_tasks, H_i_w_are_task_consistent and
        H_task_interference_is_bounded_by] imply
        [H_job_interference_is_bounded], and the fact that
        [H_R_is_maximum_seq] implies [H_R_is_maximum]. *)

    (** In this section we show that there exists a bound for
        cumulative interference for any job of task [tsk], i.e., the
        hypothesis [H_job_interference_is_bounded] holds. *)
    Section BoundOfCumulativeJobInterference.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      Hypothesis H_job_cost_positive : job_cost_positive j.

      (** Consider the busy interval <<[t1, t2)>> of job [j]. *)
      Variable t1 t2 : instant.
      Hypothesis H_busy_interval : busy_interval sched j t1 t2.

      (** Let's define [A] as a relative arrival time of job [j] (with
          respect to time [t1]). *)
      Let A : duration := job_arrival j - t1.

      (** Consider an arbitrary time [x] ... *)
      Variable x : duration.

      (** ... such that [t1 + x] is inside the busy interval... *)
      Hypothesis H_inside_busy_interval : t1 + x < t2.

      (** ... and job [j] is not completed by time [t1 + x]. *)
      Hypothesis H_job_j_is_not_completed : ~~ completed_by sched j (t1 + x).

      (** In this section, we show that the cumulative interference of
          job [j] in the interval <<[t1, t1 + x)>> is bounded by the sum
          of the task workload in the interval [t1, t1 + A + ε) and
          the cumulative interference of [j]'s task in the interval
          [t1, t1 + x). Note that the task workload is computed only
          on the interval [t1, t1 + A + ε). Thanks to the hypothesis
          about sequential tasks, jobs of task [tsk] that arrive after
          [t1 + A + ε] cannot interfere with [j]. *)
      Section TaskInterferenceBoundsInterference.

        (** We start by proving a simpler analog of the lemma that
            states that at any time instant <<t ∈ [t1, t1 + x)>> the
            sum of [interference j t] and [scheduled_at j t] is no
            larger than the sum of [the service received by jobs of
            task tsk at time t] and [task_iterference tsk t]. *)

        (** Next we consider 4 cases. *)
        Section CaseAnalysis.

          (** Consider an arbitrary time instant [t] ∈ <<[t1, t1 + x)>>. *)
          Variable t : instant.
          Hypothesis H_t_in_interval : t1 <= t < t1 + x.

          Section Case1.

            (** Assume the processor is idle at time [t]. *)
            Hypothesis H_idle : is_idle arr_seq sched t.

            (** In case when the processor is idle, one can show that
                [interference j t = 1, scheduled_at j t = 0]. But
                since interference doesn't come from a job of task
                [tsk] [task_interference tsk = 1]. Which reduces to [1
                ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_idle :
              interference j t + scheduled_at sched j t
              <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t
                + task_interference arr_seq sched j t.
            Proof.
              move: (H_busy_interval) => [[/andP [BUS LT] _] _].
              replace (service_of_jobs_at _ _ _ _) with 0; last first.
              { symmetry; rewrite /service_of_jobs_at /=.
                eapply big1; move => j' _.
                apply not_scheduled_implies_no_service.
                by apply: not_scheduled_when_idle => //. }
              have ->: scheduled_at sched j t = false.
              { have F : forall b, (~~ b) -> (b = false) by move => [].
                by apply: F; apply: not_scheduled_when_idle => //.
              }
              rewrite addn0 add0n /task_interference /cond_interference.
              case INT: (interference j t) => [|//].
              rewrite //= lt0b // andbT.
              by apply: idle_implies_no_task_scheduled => //.
            Qed.

          End Case1.

          Section Case2.

            (** Assume a job [j'] from another task is scheduled at time [t]. *)
            Variable j' : Job.
            Hypothesis H_sched : scheduled_at sched j' t.
            Hypothesis H_not_job_of_tsk : ~~ job_of_task tsk j'.

            (** If a job [j'] from another task is scheduled at time
                [t], then [interference j t = 1, scheduled_at j t =
                0]. But since interference doesn't come from a job of
                task [tsk] [task_interference tsk = 1]. Which reduces
                to [1 ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_task:
              interference j t + scheduled_at sched j t
              <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t
                + task_interference arr_seq sched j t.
            Proof.
              move: (H_busy_interval) => [[/andP [BUS LT] _] _].
              have ARRs : arrives_in arr_seq j'.
              { by apply H_jobs_come_from_arrival_sequence with t. }
              rewrite /task_interference /cond_interference.
              have -> : scheduled_at sched j t = false.
              { apply negbTE; apply/negP => SCHED.
                have EQ : j' = j by eapply H_uniprocessor_proc_model.
                by subst; move: H_not_job_of_tsk; rewrite H_job_of_tsk.
              }
              case INT: (interference j t) => [|//].
              rewrite andbT.
              have ->: non_self arr_seq sched j t.
              { eapply job_of_task_scheduled_implies_task_scheduled' => //.
                by move: (H_job_of_tsk) => /eqP ->; apply: H_not_job_of_tsk.
              }
              by clear; lia.
            Qed.

          End Case2.

          Section Case3.

            (** Assume a job [j'] (different from j) of task [tsk] is scheduled at time [t]. *)
            Variable j' : Job.
            Hypothesis H_sched : scheduled_at sched j' t.
            Hypothesis H_not_job_of_tsk : job_of_task tsk j'.
            Hypothesis H_j_neq_j' : j != j'.

            (** If a job [j'] (different from [j]) of task [tsk] is
                scheduled at time [t], then [interference j t = 1,
                scheduled_at j t = 0]. Moreover, since interference
                comes from a job of the same task [task_interference
                tsk = 0]. However, in this case [service_of_jobs of
                tsk = 1]. Which reduces to [1 ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_job:
              interference j t + scheduled_at sched j t
              <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t
                + task_interference arr_seq sched j t.
            Proof.
              move: (H_busy_interval) => [[/andP [BUS LT] _] _].
              rewrite /task_interference /cond_interference.
              have -> : scheduled_at sched j t = false.
              { apply negbTE; apply/negP => SCHED.
                have EQ : j' = j by eapply H_uniprocessor_proc_model.
                by move: (H_j_neq_j') => /eqP EQj; apply: EQj. }
              have ->: interference j t = true.
              { have NEQT: t1 <= t < t2
                  by move: H_t_in_interval => /andP [NEQ1 NEQ2]; apply/andP; split; last apply ltn_trans with (t1 + x).
                move: (H_work_conserving j t1 t2 t H_j_arrives H_job_cost_positive (fst H_busy_interval) NEQT) => [Hn _].
                apply/negPn/negP; move => CONTR; move: CONTR => /negP CONTR.
                apply Hn, service_at_implies_scheduled_at in CONTR.
                move: H_j_neq_j' => /negP JJ; apply: JJ.
                by apply /eqP; eapply H_uniprocessor_proc_model. }
              have /eqP-> : non_self arr_seq sched j t == false.
              { rewrite eqbF_neg; apply/negPn.
                apply: job_of_task_scheduled_implies_task_scheduled => //.
                by rewrite (eqP H_job_of_tsk); apply: H_not_job_of_tsk. }
              rewrite  addn0 addn0 //= [service_of_jobs_at _ _ _ _]big_mkcond sum_nat_gt0.
              apply/hasP. exists j'; last first.
              { move: H_not_job_of_tsk => /eqP TSK.
                by rewrite H_not_job_of_tsk; apply H_ideal_progress_proc_model. }
              { have ARR:= arrives_after_beginning_of_busy_interval j j' _ _ _ _ _ t1 t2 _ t.
                feed_n 8 ARR => //.
                { by move: H_t_in_interval => /andP [T1 T2]. }
                { by move: H_sched => /eqP SCHEDt; apply scheduled_implies_pending. }
                case_eq (job_arrival j' <= job_arrival j) => ARRNEQ.
                { move: ARR => /andP [РР _].
                  rewrite mem_filter; apply/andP; split=> [//|].
                  apply: arrived_between_implies_in_arrivals => //.
                  by apply/andP; split; last rewrite /A subnKC // addn1 ltnS. }
                { exfalso.
                  apply negbT in ARRNEQ; rewrite -ltnNge in ARRNEQ.
                  move: (H_sequential_tasks j j' t) => CONTR.
                  feed_n 5 CONTR => //.
                  { by rewrite /same_task eq_sym; move: (H_job_of_tsk) => /eqP ->. }
                  move: H_job_j_is_not_completed => /negP T; apply: T.
                  apply completion_monotonic with t => //.
                  by apply: ltnW; move: H_t_in_interval => /andP [_]. } }
            Qed.

          End Case3.

          Section Case4.

            (** Assume that job [j] is scheduled at time [t]. *)
            Hypothesis H_sched : scheduled_at sched j t.

            (** If job [j] is scheduled at time [t], then
                [interference = 0, scheduled_at = 1], but note that
                [service_of_jobs of tsk = 1], therefore inequality
                reduces to [1 ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_j:
              interference j t + scheduled_at sched j t
              <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t
                + task_interference arr_seq sched j t.
            Proof.
              have j_is_in_arrivals_between: j \in arrivals_between t1 (t1 + A + ε).
              { eapply arrived_between_implies_in_arrivals => //.
                move: (H_busy_interval) => [[/andP [GE _] [_ _]] _].
                by apply/andP; split; last rewrite /A subnKC // addn1. }
              rewrite /task_interference /cond_interference H_sched => //.
              have ->: non_self arr_seq sched j t = false.
              { apply/eqP; rewrite eqbF_neg; apply/negPn.
                eapply job_of_task_scheduled_implies_task_scheduled => //.
                by move: (H_job_of_tsk) => /eqP ->. }
              move: (H_job_of_tsk) => /eqP TSK.
              move: (H_work_conserving j _ _ t H_j_arrives  H_job_cost_positive (fst H_busy_interval)) => WORK.
              feed WORK.
              { move: H_t_in_interval => /andP [NEQ1 NEQ2].
                by apply/andP; split; last apply ltn_trans with (t1 + x). }
              move: WORK => [_ ZIJT].
              feed ZIJT; first by apply H_ideal_progress_proc_model.
              move: ZIJT => /negP /eqP; rewrite eqb_negLR //= => /eqP ZIJT; rewrite ZIJT //= add0n.
              rewrite addn0 /service_of_jobs_at big_mkcond sum_nat_gt0.
              rewrite filter_predT; apply/hasP.
              exists j; first by apply j_is_in_arrivals_between.
              by rewrite H_job_of_tsk.
            Qed.

          End Case4.

          (** We use the above case analysis to prove that any time
              instant <<t ∈ [t1, t1 + x)>> the sum of [interference j
              t] and [scheduled_at j t] is no larger than the sum of
              [the service received by jobs of task tsk at time t] and
              [task_iterference tsk t]. *)
          Lemma interference_plus_sched_le_serv_of_task_plus_task_interference:
            interference j t + scheduled_at sched j t
            <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t
              + task_interference arr_seq sched j t.
          Proof.
            move: (H_busy_interval) => [[/andP [BUS LT] _] _].
            have [IDLE|SCHED] := boolP (is_idle arr_seq sched t).
            { by apply interference_plus_sched_le_serv_of_task_plus_task_interference_idle. }
            { apply is_nonidle_iff in SCHED; move: SCHED => // => [[s SCHEDs]].
              have ARRs: arrives_in arr_seq s by done.
              case_eq (job_task s == tsk) => TSK; last first.
              { by apply: interference_plus_sched_le_serv_of_task_plus_task_interference_task => //; apply/negbT. }
              { case EQ: (j == s); [move: EQ => /eqP EQ; subst s | ];
                  first by apply interference_plus_sched_le_serv_of_task_plus_task_interference_j.
                eapply interference_plus_sched_le_serv_of_task_plus_task_interference_job => //.
                by move: EQ => /eqP EQ; apply/eqP.
              }
            }
          Qed.

        End CaseAnalysis.

        (** Next we prove cumulative version of the lemma above. *)
        Lemma cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference:
          cumulative_interference j t1 (t1 + x)
          <= (task_service_of_jobs_in sched tsk (arrivals_between t1 (t1 + A + ε)) t1 (t1 + x)
             - service_during sched j t1 (t1 + x)) + cumul_task_interference arr_seq sched j t1 (t1 + x).
        Proof.
          have j_is_in_arrivals_between: j \in arrivals_between t1 (t1 + A + ε).
          { eapply arrived_between_implies_in_arrivals => //.
            move: (H_busy_interval) => [[/andP [GE _] [_ _]] _].
            by apply/andP; split; last rewrite /A subnKC // addn1.
          }
          rewrite /task_service_of_jobs_in /service_of_jobs.task_service_of_jobs_in /service_of_jobs exchange_big //=.
          rewrite -(leq_add2r (\sum_(t1 <= t < (t1 + x)) service_at sched j t)).
          rewrite [X in _ <= X]addnC addnA subnKC; last first.
          { rewrite (exchange_big _ _ (arrivals_between _ _)) /= (big_rem j) //=.
            by rewrite H_job_of_tsk leq_addr. }
          rewrite -big_split -big_split //=.
          rewrite big_nat_cond [X in _ <= X]big_nat_cond leq_sum //; move => t /andP [NEQ _].
          rewrite -(leqRW (interference_plus_sched_le_serv_of_task_plus_task_interference _ _)) => //.
          rewrite /cond_interference andTb leq_add2l.
          have [-> | SER] := service_is_zero_or_one H_unit_service_proc_model sched j t => //.
          by rewrite SER lt0b; apply service_at_implies_scheduled_at; rewrite SER.
        Qed.

        (** On the other hand, the service terms in the inequality
            above can be upper-bound by the workload terms. *)
        Lemma serv_of_task_le_workload_of_task_plus:
          task_service_of_jobs_in sched tsk (arrivals_between t1 (t1 + A + ε)) t1 (t1 + x)
          - service_during sched j t1 (t1 + x) + cumul_task_interference arr_seq sched j t1 (t1 + x)
          <= (task_workload_between arr_seq tsk t1 (t1 + A + ε) - job_cost j)
            + cumul_task_interference arr_seq sched j t1 (t1 + x).
        Proof.
          have j_is_in_arrivals_between: j \in arrivals_between t1 (t1 + A + ε).
          { eapply arrived_between_implies_in_arrivals => //.
            move: (H_busy_interval) => [[/andP [GE _] [_ _]] _].
            by apply/andP; split; last rewrite /A subnKC // addn1.
          }
          rewrite leq_add2r.
          rewrite /task_workload /task_service_of_jobs_in
                  /service_of_jobs.task_service_of_jobs_in/service_of_jobs /workload_of_jobs.
          rewrite (big_rem j) ?[X in _ <= X - _](big_rem j) //=; auto using j_is_in_arrivals_between.
          rewrite H_job_of_tsk addnC -addnBA// [X in _ <= X - _]addnC -addnBA//.
          rewrite !subnn !addn0.
          exact: service_of_jobs_le_workload.
        Qed.

        (** Finally, we show that the cumulative interference of job
            [j] in the interval <<[t1, t1 + x)>> is bounded by the sum
            of the task workload in the interval [t1, t1 + A + ε) and
            the cumulative interference of [j]'s task in the interval
            <<[t1, t1 + x)>>. *)
        Lemma cumulative_job_interference_le_task_interference_bound:
          cumulative_interference j t1 (t1 + x)
          <= (task_workload_between arr_seq tsk t1 (t1 + A + ε) - job_cost j)
            + cumul_task_interference arr_seq sched j t1 (t1 + x).
        Proof.
          by apply leq_trans with
              (task_service_of_jobs_in sched tsk (arrivals_between t1 (t1 + A + ε)) t1 (t1 + x)
               - service_during sched j t1 (t1 + x)
               + cumul_task_interference arr_seq sched j t1 (t1 + x));
            [ apply cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference
            | apply serv_of_task_le_workload_of_task_plus].
          Qed.

      End TaskInterferenceBoundsInterference.

      (** In order to obtain a more convenient bound on the cumulative
          interference, we need to abandon the actual workload in
          favor of a bound that depends on task parameters only. So,
          we show that the actual workload of the task excluding workload
          of any job [j] is no greater than the bound on the workload
          excluding the cost of job [j]'s task. *)
      Lemma task_rbf_excl_tsk_bounds_task_workload_excl_j:
        task_workload_between arr_seq tsk t1 (t1 + A + ε) - job_cost j <= task_rbf (A + ε) - task_cost tsk.
      Proof.
        move: H_j_arrives H_job_of_tsk H_busy_interval => ARR TSK [[/andP [JAGET1 JALTT2] _] _].
        apply leq_trans with
            (task_cost tsk * number_of_task_arrivals arr_seq tsk t1 (t1 + A + ε) - task_cost tsk); last first.
        { rewrite leq_sub2r // leq_mul2l; apply/orP; right.
          rewrite -addnA -{2}[(A+1)](addKn t1).
          by apply H_is_arrival_curve; auto using leq_addr. }
        have Fact6: j \in arrivals_between (t1 + A) (t1 + A + ε).
        { apply arrived_between_implies_in_arrivals => //.
          apply/andP; split; rewrite /A subnKC //.
          by rewrite addn1 ltnSn //. }
        have Fact4: j \in arrivals_at arr_seq (t1 + A).
        { have CONSISTENT : consistent_arrival_times arr_seq by [].
          by move: ARR => [t ARR]; rewrite subnKC //; feed (CONSISTENT j t); try (subst t).
        }
        have Fact1: 1 <= number_of_task_arrivals arr_seq tsk (t1 + A) (t1 + A + ε).
        { rewrite /number_of_task_arrivals /task_arrivals_between /arrival_sequence.arrivals_between.
          by rewrite size_filter -has_count; apply/hasP; exists j; last rewrite TSK.
        }
        rewrite (@num_arrivals_of_task_cat _ _ _ _ _ (t1 + A)); last by apply/andP; split; rewrite leq_addr //.
        rewrite mulnDr.
        have Step1: task_workload_between arr_seq tsk t1 (t1 + A + ε)
                    = task_workload_between arr_seq tsk t1 (t1 + A) + task_workload_between arr_seq tsk (t1 + A) (t1 + A + ε).
        { by apply workload_of_jobs_cat; apply/andP; split; rewrite leq_addr. } rewrite Step1; clear Step1.
        rewrite -!addnBA; first last.
        { by rewrite /task_workload_between /workload.task_workload_between /task_workload
             /workload_of_jobs (big_rem j) //= TSK leq_addr. }
        { apply leq_trans with (task_cost tsk) => [//|].
          by rewrite -{1}[task_cost tsk]muln1 leq_mul2l; apply/orP; right. }
        rewrite leq_add//; first exact: task_workload_le_num_of_arrivals_times_cost.
        rewrite /task_workload_between /workload.task_workload_between /task_workload /workload_of_jobs
                /arrival_sequence.arrivals_between /number_of_task_arrivals /task_arrivals_between
                /arrival_sequence.arrivals_between.
        rewrite {1}addn1 big_nat1 addn1 big_nat1.
        rewrite (big_rem j) //= TSK //= addnC -addnBA // subnn addn0.
        rewrite (filter_size_rem j)//.
        rewrite mulnDr mulnC muln1 -addnBA // subnn addn0 mulnC.
        apply sum_majorant_constant.
        move => j' ARR' /eqP TSK2.
        by rewrite -TSK2; apply H_valid_job_cost; exists (t1 + A); apply rem_in in ARR'.
      Qed.

      (** Finally, we use the lemmas above to obtain the bound on
          [interference] in terms of [task_rbf] and
          [task_interference]. *)
      Lemma cumulative_job_interference_bound:
        cumulative_interference j t1 (t1 + x)
        <= (task_rbf (A + ε) - task_cost tsk) + cumul_task_interference arr_seq sched j t1 (t1 + x).
      Proof.
        set (y := t1 + x) in *.
        have IN: j \in arrivals_between t1 (t1 + A + ε).
        { apply: arrived_between_implies_in_arrivals => //.
          move: (H_busy_interval) => [[/andP [GE _] _] _].
          by apply/andP; split; last rewrite /A subnKC // addn1.
        }
        apply leq_trans with (task_workload_between arr_seq tsk t1 (t1+A+ε) - job_cost j + cumul_task_interference arr_seq sched j t1 y).
        - by apply cumulative_job_interference_le_task_interference_bound.
        - rewrite leq_add2r.
          by eapply task_rbf_excl_tsk_bounds_task_workload_excl_j; eauto 2.
      Qed.

    End BoundOfCumulativeJobInterference.

    (** In this section, we prove that [H_R_is_maximum_seq] implies [H_R_is_maximum]. *)
    Section MaxInSeqHypothesisImpMaxInNonseqHypothesis.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.

      (** For simplicity, let's define a local name for the search space. *)
      Let is_in_search_space A :=
        is_in_search_space tsk L total_interference_bound A.

      (** We prove that [H_R_is_maximum] holds. *)
      Lemma max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis:
        forall (A : duration),
          is_in_search_space A ->
          exists (F : duration),
            A + F >= task_rtct tsk +
                    (task_rbf (A + ε) - task_cost tsk + task_IBF tsk A (A + F)) /\
            R >= F + (task_cost tsk - task_rtct tsk).
      Proof.
        move: H_valid_run_to_completion_threshold => [PRT1 PRT2]; move => A INSP.
        clear H_sequential_tasks H_interference_and_workload_consistent_with_sequential_tasks.
        move: (H_R_is_maximum_seq _ INSP) => [F [FIX LE]].
        exists F; split=> [|//].
        rewrite -{2}(leqRW FIX).
        rewrite addnA leq_add2r.
        rewrite addnBA; last first.
        { apply leq_trans with (task_rbf 1).
          apply: task_rbf_1_ge_task_cost => //.
          eapply task_rbf_monotone; eauto 2.
          by rewrite addn1.
        }
        by rewrite subnBA; auto; rewrite addnC.
      Qed.

    End MaxInSeqHypothesisImpMaxInNonseqHypothesis.

    (** Finally, we apply the [uniprocessor_response_time_bound]
        theorem, and using the lemmas above, we prove that all the
        requirements are satisfied. So, [R] is a response-time bound. *)
    Theorem uniprocessor_response_time_bound_seq :
      task_response_time_bound arr_seq sched tsk R.
    Proof.
      move => j ARR TSK.
      eapply uniprocessor_response_time_bound_ideal with
          (interference_bound_function :=
             fun tsk A R => task_rbf (A + ε) - task_cost tsk + task_IBF tsk A R); eauto 2.
      { clear ARR TSK H_R_is_maximum_seq R j.
        move => t1 t2 R j ARR TSK BUSY NEQ COMPL.
        move: (posnP (@job_cost _ jc j)) => [ZERO|POS].
        { exfalso; move: COMPL => /negP COMPL; apply: COMPL.
          by rewrite /service.completed_by /completed_by ZERO.
        }
        move => A LE; specialize (LE _ _ BUSY).
        apply leq_trans with (task_rbf (A + ε) - task_cost tsk + cumul_task_interference arr_seq sched j t1 (t1 + R)).
        - rewrite -/cumulative_interference.
          eapply leq_trans; first by eapply cumulative_job_interference_bound; eauto 2.
          by rewrite LE; replace (t1 + A - t1) with A by lia.
        - rewrite leq_add2l; eapply leq_trans; last by apply:leqnn.
          rewrite /cumul_task_interference.
          apply (H_task_interference_is_bounded t1 t2 R) => //.
          have EQ : job_arrival j - t1 = A by lia.
          subst A.
          rewrite /relative_arrival_time_of_job_is_A => t1' t2' BUSY'.
          have [EQ1 E2] := busy_interval_is_unique _ _ _ _ _ _ BUSY BUSY'.
          by subst.
      }
      { by eapply max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis; eauto. }
    Qed.

  End ResponseTimeBound.

End Sequential_Abstract_RTA.
