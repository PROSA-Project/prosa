Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.model.task_schedule.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.abstract.abstract_rta.

(** In this section, we define a notion of _task_ interference-bound
    function [task_IBF]. Function [task_IBF] bounds interference that
    excludes interference due to self-interference. *)
Section TaskInterferenceBound.

  (** Consider any type of job associated with any type of tasks... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs. *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk : Task.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Next we introduce the notion of _task_ interference.
      Intuitively, task [tsk] incurs interference when some of the
      jobs of task [tsk] incur interference. As a result, [tsk] cannot
      make any progress.

      More formally, consider a job [j] of task [tsk]. The task
      experiences interference at time [t] if job [j] experiences
      interference ([interference j t = true]) and task [tsk] is not
      scheduled at time [t]. *)

  (** Let us define a predicate stating that the task of a job [j] is
      _not_ scheduled at a time instant [t]. *)
  Definition nonself (j : Job) (t : instant) :=
    ~~ task_served_at arr_seq sched (job_task j) t.

  (** We define task interference as conditional interference where
      [nonself] is used as the predicate. This way, [task_interference
      j t] is [false] if the interference experienced by a job [j] is
      caused by a job of the same task. *)
  Definition task_interference (j : Job) (t : instant) :=
    cond_interference nonself j t.

  (** Next, we define the cumulative task interference. *)
  Definition cumul_task_interference j t1 t2 :=
    cumul_cond_interference nonself j t1 t2.

  (** Consider an interference bound function [task_IBF]. *)
  Variable task_IBF : duration -> duration -> work.

  (** We say that task interference is bounded by [task_IBF] iff for
      any job [j] of task [tsk] cumulative _task_ interference within
      the interval <<[t1, t1 + R)>> is bounded by function [task_IBF(tsk, A, R)]. *)
  Definition task_interference_is_bounded_by :=
    cond_interference_is_bounded_by
      arr_seq sched tsk task_IBF (relative_arrival_time_of_job_is_A sched) nonself.

End TaskInterferenceBound.

(** In the following section, we prove that, under certain assumptions
    defined next, the fact that a function [task_IBF tsk A R]
    satisfies hypothesis [task_interference_is_bounded_by] implies
    that a function [(task_rbf (A + ε) - task_cost tsk) + task_IBF tsk
    A R] satisfies [job_interference_is_bounded_by]. In other words,
    the self-interference can be bounded by the term [(task_rbf (A +
    ε) - task_cost tsk)], where [A] is the relative arrival time of a
    job under analysis. *)
Section TaskIBFtoJobIBF.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context {jc : JobCost Job}.

  (** Consider any kind of ideal uni-processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

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

  (** We assume that the schedule is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Let us abbreviate task [tsk]'s RBF for clarity. *)
  Let task_rbf := task_request_bound_function tsk.

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
      = task_service_of_jobs_in sched tsk (arrivals_between arr_seq 0 t1) 0 t1.

  (** To prove the reduction from [task_IBF] to [job_IBF], we need to
      ensure that the scheduling policy, interference, and interfering
      workload all respect the sequential tasks hypothesis. For this,
      we assume that (1) tasks are sequential and (2) functions
      interference and interfering_workload are consistent with the
      hypothesis of sequential tasks. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.
  Hypothesis H_interference_and_workload_consistent_with_sequential_tasks :
    interference_and_workload_consistent_with_sequential_tasks.

  (** Next, we assume that [task_IBF] is a bound on interference
      incurred by the task. *)
  Variable task_IBF : duration -> duration -> duration.
  Hypothesis H_task_interference_is_bounded :
    task_interference_is_bounded_by arr_seq sched tsk task_IBF.

  (** Before proceed to the main proof, we first show a few simple
      lemmas about the completion of jobs from the task considering
      the busy interval of the job under consideration. *)
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

    (** We prove that if a job from task [tsk] arrived before the
        beginning of the busy interval, then it must be completed
        before the beginning of the busy interval *)
    Lemma completed_before_beginning_of_busy_interval :
      job_arrival j2 < t1 ->
      completed_by sched j2 t1.
    Proof.
      move => JA; have /eqP TSK2eq := H_j2_from_tsk.
      have [ZERO|POS] := posnP (@job_cost _ jc j2).
      { by rewrite /completed_by /service.completed_by ZERO. }
      { by eapply all_jobs_have_completed_equiv_workload_eq_service => //. }
    Qed.

    (** Next we prove that if a job is pending after the beginning of
        the busy interval <<[t1, t2)>> then it arrives after [t1]. *)
    Lemma arrives_after_beginning_of_busy_interval :
      forall t,
        t1 <= t ->
        pending sched j2 t ->
        arrived_between j2 t1 t.+1.
    Proof.
      move => t GE PEND.
      apply/andP; split; last first.
      { by move: PEND => /andP [ARR _]; rewrite ltnS. }
      rewrite leqNgt; apply/negP => LT.
      have L12 := completed_before_beginning_of_busy_interval LT.
      apply completion_monotonic with (t' := t) in L12 => //.
      by move: PEND => /andP [_ /negP T2].
    Qed.

  End CompletionOfJobsFromSameTask.

  (** In this section we show that there exists a bound for cumulative
      interference for any job of task [tsk]. *)
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

    (** ... such that [t1 + x] is inside the busy interval ... *)
    Hypothesis H_inside_busy_interval : t1 + x < t2.

    (** ... and job [j] is not completed by time [t1 + x]. *)
    Hypothesis H_job_j_is_not_completed : ~~ completed_by sched j (t1 + x).

    (** In this section, we show that the cumulative interference of
        job [j] in the interval <<[t1, t1 + x)>> is bounded by the sum
        of the task workload in the interval <<[t1, t1 + A + ε)>> and
        the cumulative interference of [j]'s task in the interval
        <<[t1, t1 + x)>>. Note that the task workload is computed only
        on the interval <<[t1, t1 + A + ε)>>. Thanks to the hypothesis
        about sequential tasks, jobs of task [tsk] that arrive after
        [t1 + A + ε] cannot interfere with [j]. *)
    Section TaskInterferenceBoundsInterference.

      (** We start by proving a simpler analog of the lemma that
          states that at any time instant <<t ∈ [t1, t1 + x)>> the sum
          of [interference j t] and [scheduled_at j t] is no larger
          than the sum of [the service received by jobs of task tsk at
          time t] and [task_iterference tsk t]. *)

      (** Next we consider 4 cases. *)
      Section CaseAnalysis.

        (** Consider an arbitrary time instant [t] ∈ <<[t1, t1 + x)>>. *)
        Variable t : instant.
        Hypothesis H_t_in_interval : t1 <= t < t1 + x.

        Section Case1.

          (** Assume the processor is idle at time [t]. *)
          Hypothesis H_idle : is_idle arr_seq sched t.

          (** In case when the processor is idle, one can show that
              [interference j t = 1, service_at j t = 0]. But since
              interference doesn't come from a job of task [tsk]
              [task_interference tsk = 1]. Which reduces to [1 ≤
              1]. *)
          Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_idle :
            interference j t + service_at sched j t
            <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between arr_seq t1 (t1 + A + ε)) t
              + task_interference arr_seq sched j t.
          Proof.
            replace (service_of_jobs_at _ _ _ _) with 0; last first.
            { symmetry; rewrite /service_of_jobs_at /=.
              eapply big1; move => j' _.
              apply not_scheduled_implies_no_service.
              exact: not_scheduled_when_idle. }
            have ->: service_at sched j t = 0.
            { apply: not_scheduled_implies_no_service.
              exact: not_scheduled_when_idle. }
            rewrite addn0 add0n /task_interference /cond_interference.
            case INT: (interference j t) => [|//].
            rewrite //= lt0b // andbT.
            exact: no_task_served_when_idle.
          Qed.

        End Case1.

        Section Case2.

          (** Assume a job [j'] from another task is scheduled at time [t]. *)
          Variable j' : Job.
          Hypothesis H_sched : scheduled_at sched j' t.
          Hypothesis H_not_job_of_tsk : ~~ job_of_task tsk j'.

          (** If a job [j'] from another task is scheduled at time
              [t], then [interference j t = 1, served_at j t = 0]. But
              since interference doesn't come from a job of task [tsk]
              [task_interference tsk = 1]. Which reduces to [1 ≤
              1]. *)
          Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_task:
            interference j t + service_at sched j t
            <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between arr_seq t1 (t1 + A + ε)) t
              + task_interference arr_seq sched j t.
          Proof.
            have ARRs : arrives_in arr_seq j'.
            { by apply H_jobs_come_from_arrival_sequence with t. }
            rewrite /task_interference /cond_interference.
            have ->: service_at sched j t = 0.
            { apply: not_scheduled_implies_no_service; apply/negP => SCHED.
              have EQ : j' = j by eapply H_uniprocessor_proc_model.
              by subst; move: H_not_job_of_tsk; rewrite H_job_of_tsk. }
            case INT: (interference j t) => [|//].
            rewrite andbT.
            have ->: nonself arr_seq sched j t.
            { eapply job_of_other_task_scheduled' => //.
              by move: (H_job_of_tsk) => /eqP ->; apply: H_not_job_of_tsk. }
            by clear; lia.
          Qed.

        End Case2.

        Section Case3.

          (** Assume a job [j'] of task [tsk] is scheduled at time [t]
              but receives no service. *)
          Variable j' : Job.
          Hypothesis H_sched : scheduled_at sched j' t.
          Hypothesis H_not_job_of_tsk : job_of_task tsk j'.
          Hypothesis H_serv : service_at sched j' t = 0.

          (** If a job [j'] of task [tsk] is scheduled at time [t],
              then [interference j t = 1, service_at j t =
              0]. Moreover, since interference comes from a job of the
              same task [task_interference tsk = 0]. However, in this
              case [service_of_jobs of tsk = 1]. Which reduces to [1 ≤
              1]. *)
          Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_job :
            interference j t + service_at sched j t
            <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between arr_seq t1 (t1 + A + ε)) t
              + task_interference arr_seq sched j t.
          Proof.
            rewrite /task_interference /cond_interference.
            have SERVj: service_at sched j t = 0; last rewrite SERVj.
            { have [] := service_is_zero_or_one _ sched j t => // => SERVj.
              apply: not_scheduled_implies_no_service; apply/negP => SCHED.
              have EQ : j' = j by eapply H_uniprocessor_proc_model.
              by subst j';  move: H_serv SERVj => ->.
            }
            have ->: interference j t = true.
            { have NEQT: t1 <= t < t2
                by move: H_t_in_interval => /andP [NEQ1 NEQ2]; apply/andP; split; last apply ltn_trans with (t1 + x).
              move: (H_work_conserving j t1 t2 t H_j_arrives H_job_cost_positive (fst H_busy_interval) NEQT) => [Hn _].
              apply/negPn/negP; move => CONTR; move: CONTR => /negP CONTR.
              by apply Hn in CONTR; move: CONTR; rewrite /receives_service_at SERVj.
            }
            have /eqP-> : nonself arr_seq sched j t == true.
            { rewrite eqb_id.
              apply: job_of_task_not_served => //.
              by move: H_job_of_tsk => /eqP ->.
            }
            by rewrite addnC leq_add => //.
          Qed.

        End Case3.

        Section Case4.

          (** Before proceeding to the last case, let us note that the
              sum of interference and the service of [j] at [t] always
              equals to [1]. *)
          Fact interference_and_service_eq_1 :
            interference j t + service_at sched j t = 1.
          Proof.
            have NEQT: t1 <= t < t2
              by move: H_t_in_interval => /andP [NEQ1 NEQ2]; apply/andP; split; last apply ltn_trans with (t1 + x).
            have [] := service_is_zero_or_one _ sched j t => // => SERVj.
            { rewrite SERVj.
              have ->: interference j t = true; last by done.
              { move: (H_work_conserving j t1 t2 t H_j_arrives H_job_cost_positive (fst H_busy_interval) NEQT) => [Hn _].
                apply/negPn/negP; move => CONTR; move: CONTR => /negP CONTR.
                by apply Hn in CONTR; move: CONTR; rewrite /receives_service_at SERVj.
              }
            }
            { rewrite SERVj.
              have ->: interference j t = false; last by done.
              { move: (H_work_conserving j t1 t2 t H_j_arrives H_job_cost_positive (fst H_busy_interval) NEQT) => [_ Hs].
                apply/negP; apply: Hs.
                by rewrite /receives_service_at SERVj.
              }
            }
          Qed.

          (** Assume that a job [j'] is scheduled at time [t] and receives service. *)
          Variable j' : Job.
          Hypothesis H_sched : scheduled_at sched j' t.
          Hypothesis H_not_job_of_tsk : job_of_task tsk j'.
          Hypothesis H_serv : service_at sched j' t = 1.

          (** If job [j'] is served at time [t], then [service_of_jobs
              of tsk = 1]. With the fact that [interference +
              service_at = 1], we get the inequality to [1 ≤ 1]. *)
          Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_j :
            interference j t + service_at sched j t
            <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between arr_seq t1 (t1 + A + ε)) t
              + task_interference arr_seq sched j t.
          Proof.
            rewrite interference_and_service_eq_1 -addn1 addnC leq_add //.
            rewrite /service_of_jobs_at big_mkcond sum_nat_gt0 filter_predT; apply/hasP.
            exists j'; last by rewrite H_not_job_of_tsk.
            eapply arrived_between_implies_in_arrivals => //.
            apply/andP; split.
            - move_neq_up CONTR.
              eapply completed_before_beginning_of_busy_interval in CONTR => //.
              apply scheduled_implies_not_completed in H_sched => //.
              move: H_sched => /negP T; apply: T.
              by apply (completion_monotonic _ _ t1) => //; move: (H_t_in_interval); clear; lia.
            - rewrite -addn1 leq_add2r /A subnKC //.
              have NCOMPL : ~~ completed_by sched j t.
              { by apply: (incompletion_monotonic _ _ _ (t1 + x)) => //; move: (H_t_in_interval); clear; lia. }
              clear H_job_j_is_not_completed; apply: scheduler_executes_job_with_earliest_arrival => //.
              by rewrite /same_task; move: (H_job_of_tsk) (H_not_job_of_tsk) => /eqP -> /eqP ->.
          Qed.

        End Case4.

        (** We use the above case analysis to prove that any time
            instant <<t ∈ [t1, t1 + x)>> the sum of [interference j t]
            and [scheduled_at j t] is no larger than the sum of [the
            service received by jobs of task tsk at time t] and
            [task_iterference tsk t]. *)
        Lemma interference_plus_sched_le_serv_of_task_plus_task_interference:
          interference j t + service_at sched j t
          <= service_of_jobs_at sched (job_of_task tsk) (arrivals_between arr_seq t1 (t1 + A + ε)) t
            + task_interference arr_seq sched j t.
        Proof.
          rewrite /task_interference /cond_interference.
          have [IDLE|SCHED] := boolP (is_idle arr_seq sched t).
          { by apply interference_plus_sched_le_serv_of_task_plus_task_interference_idle. }
          { apply is_nonidle_iff in SCHED; move: SCHED => // => [[s SCHEDs]].
            have ARRs: arrives_in arr_seq s by done.
            have [TSKEQ|TSKNEQ] := boolP (job_of_task tsk s); last first.
            { exact: interference_plus_sched_le_serv_of_task_plus_task_interference_task. }
            { have [] := service_is_zero_or_one _ sched s t => // => SERVj.
              { exact: interference_plus_sched_le_serv_of_task_plus_task_interference_job. }
              { exact: interference_plus_sched_le_serv_of_task_plus_task_interference_j. }
            }
          }
        Qed.

      End CaseAnalysis.

      (** Next we prove cumulative version of the lemma above. *)
      Lemma cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference:
        cumulative_interference j t1 (t1 + x)
        <= (task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + A + ε)) t1 (t1 + x)
           - service_during sched j t1 (t1 + x)) + cumul_task_interference arr_seq sched j t1 (t1 + x).
      Proof.
        have j_is_in_arrivals_between: j \in arrivals_between arr_seq t1 (t1 + A + ε).
        { eapply arrived_between_implies_in_arrivals => //.
          by apply/andP; split; last rewrite /A subnKC // addn1.
        }
        rewrite /task_service_of_jobs_in /service_of_jobs.task_service_of_jobs_in /service_of_jobs exchange_big //=.
        rewrite -(leq_add2r (\sum_(t1 <= t < (t1 + x)) service_at sched j t)).
        rewrite [X in _ <= X]addnC addnA subnKC; last first.
        { rewrite (exchange_big _ _ (arrivals_between _ _ _)) /= (big_rem j) //=.
          by rewrite H_job_of_tsk leq_addr. }
        rewrite -big_split -big_split //=.
        rewrite big_nat_cond [X in _ <= X]big_nat_cond leq_sum //; move => t /andP [NEQ _].
        rewrite -(leqRW (interference_plus_sched_le_serv_of_task_plus_task_interference _ _ )) => //.
      Qed.

      (** As the next step, the service terms in the inequality above
          can be upper-bound by the workload terms. *)
      Lemma serv_of_task_le_workload_of_task_plus:
        task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + A + ε)) t1 (t1 + x)
        - service_during sched j t1 (t1 + x) + cumul_task_interference arr_seq sched j t1 (t1 + x)
        <= (task_workload_between arr_seq tsk t1 (t1 + A + ε) - job_cost j)
          + cumul_task_interference arr_seq sched j t1 (t1 + x).
      Proof.
        have j_is_in_arrivals_between: j \in arrivals_between arr_seq t1 (t1 + A + ε).
        { eapply arrived_between_implies_in_arrivals => //.
          by apply/andP; split; last rewrite /A subnKC // addn1. }
        rewrite leq_add2r.
        rewrite /task_workload_between/task_service_of_jobs_in/task_service_of_jobs_in/service_of_jobs.
        rewrite (big_rem j) ?[X in _ <= X - _](big_rem j) //=; auto using j_is_in_arrivals_between.
        rewrite H_job_of_tsk addnC -addnBA// [X in _ <= X - _]addnC -addnBA//.
        rewrite !subnn !addn0.
        exact: service_of_jobs_le_workload.
      Qed.

      (** Finally, we show that the cumulative interference of job [j]
          in the interval <<[t1, t1 + x)>> is bounded by the sum of
          the task workload in the interval [t1, t1 + A + ε) and the
          cumulative interference of [j]'s task in the interval <<[t1,
          t1 + x)>>. *)
      Lemma cumulative_job_interference_le_task_interference_bound:
        cumulative_interference j t1 (t1 + x)
        <= (task_workload_between arr_seq tsk t1 (t1 + A + ε) - job_cost j)
          + cumul_task_interference arr_seq sched j t1 (t1 + x).
      Proof.
        by apply leq_trans with
          (task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + A + ε)) t1 (t1 + x)
           - service_during sched j t1 (t1 + x)
           + cumul_task_interference arr_seq sched j t1 (t1 + x));
        [ apply cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference
        | apply serv_of_task_le_workload_of_task_plus].
      Qed.

    End TaskInterferenceBoundsInterference.

    (** We use the lemmas above to obtain the bound on [interference]
        in terms of [task_rbf] and [task_interference]. *)
    Lemma cumulative_job_interference_bound :
      cumulative_interference j t1 (t1 + x)
      <= (task_rbf (A + ε) - task_cost tsk) + cumul_task_interference arr_seq sched j t1 (t1 + x).
    Proof.
      set (y := t1 + x) in *.
      have IN: j \in arrivals_between arr_seq t1 (t1 + A + ε).
      { apply: arrived_between_implies_in_arrivals => //.
        by apply/andP; split; last rewrite /A subnKC // addn1. }
      apply leq_trans with (
          task_workload_between arr_seq tsk t1 (t1+A+ε) - job_cost j + cumul_task_interference arr_seq sched j t1 y
        ).
      - by apply cumulative_job_interference_le_task_interference_bound.
      - rewrite leq_add2r /A.
        have -> : (t1 + (job_arrival j - t1) + ε) = (t1 + (job_arrival j - t1 + ε)) by lia.
        apply: task_rbf_without_job_under_analysis => //=.
        by move: IN => /[!job_arrival_in_bounds] // -[]; lia.
    Qed.

  End BoundOfCumulativeJobInterference.

  (** Finally, we show that one can construct a job IBF from the given task IBF. *)
  Lemma task_IBF_implies_job_IBF :
    job_interference_is_bounded_by
      arr_seq sched tsk
      (fun A R => (task_rbf (A + ε) - task_cost tsk) + task_IBF A R)
      (relative_arrival_time_of_job_is_A sched).
  Proof.
    move => t1 t2 R j ARR TSK BUSY NEQ COMPL.
    have [ZERO|POS] := posnP (@job_cost _ jc j).
    { exfalso; move: COMPL => /negP COMPL; apply: COMPL.
      by rewrite /service.completed_by ZERO. }
    move => A LE; specialize (LE _ _ BUSY).
    apply leq_trans with (task_rbf (A + ε) - task_cost tsk + cumul_task_interference arr_seq sched j t1 (t1 + R)).
    - rewrite -/cumulative_interference.
      eapply leq_trans; first by eapply cumulative_job_interference_bound; eauto 2.
      by rewrite LE; replace (t1 + A - t1) with A by lia.
    - rewrite leq_add2l; eapply leq_trans; last exact:leqnn.
      rewrite /cumul_task_interference.
      apply (H_task_interference_is_bounded t1 t2 R) => //.
      have EQ : job_arrival j - t1 = A by lia.
      subst A.
      rewrite /relative_arrival_time_of_job_is_A => t1' t2' BUSY'.
      have [EQ1 E2] := busy_interval_is_unique _ _ _ _ _ _ BUSY BUSY'.
      by subst.
  Qed.

End TaskIBFtoJobIBF.
