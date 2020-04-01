Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.model.task_arrivals.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.abstract.abstract_rta.

(** * Abstract Response-Time Analysis with sequential tasks *)
(** In this section we propose the general framework for response-time analysis (RTA)
    of uni-processor scheduling of real-time tasks with arbitrary arrival models
    and sequential tasks. *)

  (** We prove that the maximum among the solutions of the response-time bound
     recurrence for some set of parameters is a response-time bound for [tsk].
     Note that in this section we _do_ rely on the hypothesis about task
     sequentiality. This allows us to provide a more precise response-time
     bound function, since jobs of the same task will be executed strictly
     in the order they arrive. *)
Section Sequential_Abstract_RTA.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** Next, consider any ideal uniprocessor schedule of this arrival sequence...*)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Consider an arbitrary task set. *)
  Variable ts : list Task.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That is,
     [task_run_to_completion_threshold tsk] is (1) no bigger than [tsk]'s
     cost, (2) for any job of task [tsk] [job_run_to_completion_threshold]
     is bounded by [task_run_to_completion_threshold]. *)
  Hypothesis H_valid_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task [tsk] in ts
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) it is a monotonic function
     that equals [0] for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Assume we are provided with abstract functions for interference and interfering workload. *)
  Variable interference : Job -> instant -> bool.
  Variable interfering_workload : Job -> instant -> duration.

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let busy_interval := busy_interval sched interference interfering_workload.
  Let arrivals_between := arrivals_between arr_seq.
  Let service_of_jobs_at := service_of_jobs_at sched.
  Let task_workload_between := task_workload_between arr_seq tsk.
  Let task_service_of_jobs_in := task_service_of_jobs_in sched tsk.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.

  (** In this section, we introduce a few new definitions to make it easier
     to express the new bound of the worst-case execution time. *)
  Section Definitions.

    (** When assuming sequential tasks, we can introduce an additional hypothesis that
       ensures that the values of interference and workload remain consistent. It states
       that any of [tsk]'s job, that arrived before the busy interval, should be
       completed by the beginning of the busy interval. *)
    Definition interference_and_workload_consistent_with_sequential_tasks :=
      forall (j : Job) (t1 t2 : instant),
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_cost j > 0 ->
          busy_interval j t1 t2 ->
          task_workload_between 0 t1 = task_service_of_jobs_in (arrivals_between 0 t1) 0 t1.

    (** Next we introduce the notion of task interference. Intuitively, task [tsk] incurs
       interference when some of the jobs of task [tsk] incur interference. As a result,
       [tsk] cannot make any progress. More formally, task [tsk] experiences interference at
       a time instant time [t], if at time t task [tsk] is not scheduled and there exists
       a job of [tsk] that (1) experiences interference and (2) has arrived before some
       time instant [upper_bound].

       It is important to note two subtle points: according to our semantics of the
       interference function, jobs from the same task can cause interference to each other.
       In the definition of interference of a task we want to avoid such situations. That
       is why we use the term [~~ task_scheduled_at tsk t].

       Moreover, in order to make the definition constructive, we introduce an upper bound
       on the arrival time of jobs from task [tsk]. As a result, we need to consider only a
       finite number of jobs. For the function to produce the correct values it is enough
       to specify a sufficiently large upper_bound. Usually as upper_bound one can use the
       end of the corresponding busy interval. *)
    Definition task_interference_received_before (tsk : Task) (upper_bound : instant) (t : instant) :=
      (~~ task_scheduled_at sched tsk t)
        && has (fun j => interference j t) (task_arrivals_before arr_seq tsk upper_bound).

    (** Next we define the cumulative task interference. *)
    Definition cumul_task_interference tsk upper_bound t1 t2 :=
      \sum_(t1 <= t < t2) task_interference_received_before tsk upper_bound t.

    (** We say that task interference is bounded by task_interference_bound_function ([tIBF])
       iff for any job [j] of task [tsk] cumulative _task_ interference within the interval
       [t1, t1 + R) is bounded by function [tIBF(tsk, A, R)].
       Note that this definition is almost the same as the definition of job_interference_is_bounded_by
       from the non-necessary-sequential case. However, in this case we ignore the
       interference that comes from jobs from the same task. *)
    Definition task_interference_is_bounded_by
               (task_interference_bound_function : Task -> duration -> duration -> duration) :=
      forall j R t1 t2,
        arrives_in arr_seq j ->
        job_task j = tsk ->
        t1 + R < t2 ->
        ~~ completed_by sched j (t1 + R) ->
        busy_interval j t1 t2 ->
        let offset := job_arrival j - t1 in
        cumul_task_interference tsk t2 t1 (t1 + R) <= task_interference_bound_function tsk offset R.

  End Definitions.

  (** In this section, we prove that the maximum among the solutions of the
     response-time bound recurrence is a response-time bound for [tsk]. *)
  Section ResponseTimeBound.

    (** For simplicity, let's define some local names. *)
    Let cumul_interference := cumul_interference interference.
    Let cumul_workload := cumul_interfering_workload interfering_workload.
    Let cumul_task_interference := cumul_task_interference tsk.

    (** We assume that the schedule is work-conserving. *)
    Hypothesis H_work_conserving:
      work_conserving arr_seq sched tsk interference interfering_workload.

    (** Unlike the previous theorem [uniprocessor_response_time_bound], we assume
       that (1) tasks are sequential, moreover (2) functions interference and
       interfering_workload are consistent with the hypothesis of sequential tasks. *)
    Hypothesis H_sequential_tasks : sequential_tasks sched.
    Hypothesis H_interference_and_workload_consistent_with_sequential_tasks:
      interference_and_workload_consistent_with_sequential_tasks.

    (** Assume we have a constant L which bounds the busy interval of any of [tsk]'s jobs. *)
    Variable L : duration.
    Hypothesis H_busy_interval_exists:
      busy_intervals_are_bounded_by arr_seq sched tsk interference interfering_workload L.

    (** Next, we assume that task_interference_bound_function is a bound on interference incurred by the task. *)
    Variable task_interference_bound_function : Task -> duration -> duration -> duration.
    Hypothesis H_task_interference_is_bounded:
      task_interference_is_bounded_by task_interference_bound_function.

    (** Given any job [j] of task [tsk] that arrives exactly [A] units after the beginning of the busy
       interval, the bound on the total interference incurred by [j] within an interval of length [Δ]
       is no greater than [task_rbf (A + ε) - task_cost tsk + task's IBF Δ]. Note that in case of
       sequential tasks the bound consists of two parts: (1) the part that bounds the interference
       received from other jobs of task [tsk] -- [task_rbf (A + ε) - task_cost tsk] and (2) any other
       interference that is bounded by [task_IBF(tsk, A, Δ)]. *)
    Let total_interference_bound (tsk : Task) (A Δ : duration) :=
      task_rbf (A + ε) - task_cost tsk + task_interference_bound_function tsk A Δ.

    (** Note that since we consider the modified interference bound function, the search space has
       also changed. One can see that the new search space is guaranteed to include any A for which
       [task_rbf (A) ≠ task_rbf (A + ε)], since this implies the fact that
       [total_interference_bound (tsk, A, Δ) ≠ total_interference_bound (tsk, A + ε, Δ)]. *)
    Let is_in_search_space_seq := is_in_search_space tsk L total_interference_bound.

    (** Consider any value [R], and assume that for any relative arrival time [A] from the search
       space there is a solution [F] of the response-time recurrence that is bounded by [R]. In
       contrast to the formula in "non-sequential" Abstract RTA, assuming that tasks are
       sequential leads to a more precise response-time bound. Now we can explicitly express
       the interference caused by other jobs of the task under consideration.

       To understand the right part of the fix-point in the equation it is helpful to note
       that the bound on the total interference ([bound_of_total_interference]) is equal to
       [task_rbf (A + ε) - task_cost tsk + tIBF tsk A Δ]. Besides, a job must receive
       enough service to become non-preemptive [task_lock_in_service tsk]. The sum of
       these two quantities is exactly the right-hand side of the equation. *)
    Variable R : nat.
    Hypothesis H_R_is_maximum_seq:
      forall (A : duration),
        is_in_search_space_seq A ->
        exists (F : duration),
          A + F = (task_rbf (A + ε) - (task_cost tsk - task_run_to_completion_threshold tsk))
                  + task_interference_bound_function tsk A (A + F) /\
          F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.

    (** In this section we prove a few simple lemmas about the completion of jobs from the task
       considering the busy interval of the job under consideration. *)
    Section CompletionOfJobsFromSameTask.

      (** Consider any two jobs [j1] [j2] of [tsk]. *)
      Variable j1 j2 : Job.
      Hypothesis H_j1_arrives: arrives_in arr_seq j1.
      Hypothesis H_j2_arrives: arrives_in arr_seq j2.
      Hypothesis H_j1_from_tsk: job_task j1 = tsk.
      Hypothesis H_j2_from_tsk: job_task j2 = tsk.
      Hypothesis H_j1_cost_positive: job_cost_positive j1.

      (** Consider the busy interval <<[t1, t2)>> of job j1. *)
      Variable t1 t2 : instant.
      Hypothesis H_busy_interval : busy_interval j1 t1 t2.

      (** We prove that if a job from task [tsk] arrived before the beginning of the busy
         interval, then it must be completed before the beginning of the busy interval *)
      Lemma completed_before_beginning_of_busy_interval:
        job_arrival j2 < t1 ->
        completed_by sched j2 t1.
      Proof.
        move => JA; move: (H_j2_from_tsk) => /eqP TSK2eq.
        move: (posnP (@job_cost _ H3 j2)) => [ZERO|POS].
        { by rewrite /completed_by /service.completed_by ZERO. }
        move: (H_interference_and_workload_consistent_with_sequential_tasks
                 j1 t1 t2 H_j1_arrives H_j1_from_tsk H_j1_cost_positive H_busy_interval) => SWEQ.
        eapply all_jobs_have_completed_equiv_workload_eq_service
          with (j := j2) in SWEQ; eauto 2; try done.
          by apply arrived_between_implies_in_arrivals.
      Qed.

      (** Next we prove that if a job is pending after the beginning
         of the busy interval <<[t1, t2)>> then it arrives after t1. *)
      Lemma arrives_after_beginning_of_busy_interval:
        forall t,
          t1 <= t ->
          pending sched j2 t ->
          arrived_between j2 t1 t.+1.
      Proof.
        intros t GE PEND.
        rewrite /arrived_between; apply/andP; split; last first.
        { by move: PEND => /andP [ARR _]; rewrite ltnS. }
        rewrite leqNgt; apply/negP; intros LT.
        move: (H_busy_interval) => [[/andP [AFR1 AFR2] [QT _]] _].
        have L12 := completed_before_beginning_of_busy_interval LT.
        apply completion_monotonic with (t' := t) in L12; try done.
          by move: PEND => /andP [_ /negP T2].
      Qed.

    End CompletionOfJobsFromSameTask.

    (** Since we are going to use the [uniprocessor_response_time_bound] theorem to prove
       the theorem of this section, we have to show that all the hypotheses are satisfied.
       Namely, we need to show that hypotheses [H_sequential_tasks, H_i_w_are_task_consistent
       and H_task_interference_is_bounded_by] imply [H_job_interference_is_bounded], and the
       fact that [H_R_is_maximum_seq] implies [H_R_is_maximum]. *)

    (** In this section we show that there exists a bound for cumulative interference for any
       job of task [tsk], i.e., the hypothesis [H_job_interference_is_bounded] holds. *)
    Section BoundOfCumulativeJobInterference.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_task j = tsk.
      Hypothesis H_job_cost_positive : job_cost_positive j.

      (** Consider the busy interval <<[t1, t2)>> of job j. *)
      Variable t1 t2 : instant.
      Hypothesis H_busy_interval : busy_interval j t1 t2.

      (** Let's define A as a relative arrival time of job j (with respect to time t1). *)
      Let A : duration := job_arrival j - t1.

      (** Consider an arbitrary time x ... *)
      Variable x : duration.
      (** ... such that (t1 + x) is inside the busy interval... *)
      Hypothesis H_inside_busy_interval : t1 + x < t2.
      (** ... and job j is not completed by time (t1 + x). *)
      Hypothesis H_job_j_is_not_completed : ~~ completed_by sched j (t1 + x).

      (** In this section, we show that the cumulative interference of job j in the interval <<[t1, t1 + x)>>
         is bounded by the sum of the task workload in the interval [t1, t1 + A + ε) and the cumulative
         interference of [j]'s task in the interval [t1, t1 + x). Note that the task workload is computed
         only on the interval [t1, t1 + A + ε). Thanks to the hypothesis about sequential tasks, jobs of
         task [tsk] that arrive after [t1 + A + ε] cannot interfere with j. *)
      Section TaskInterferenceBoundsInterference.

        (** We start by proving a simpler analog of the lemma which states that at
           any time instant t ∈ <<[t1, t1 + x)>> the sum of [interference j t] and
           [scheduled_at j t] is no larger than the sum of [the service received
           by jobs of task tsk at time t] and [task_iterference tsk t]. *)

        (** Next we consider 4 cases. *)
        Section CaseAnalysis.

          (** Consider an arbitrary time instant t ∈ <<[t1, t1 + x)>>. *)
          Variable t : instant.
          Hypothesis H_t_in_interval : t1 <= t < t1 + x.

          Section Case1.

            (** Assume the processor is idle at time [t]. *)
            Hypothesis H_idle : sched t = None.

            (** In case when the processor is idle, one can show that
               [interference j t = 1, scheduled_at j t = 0]. But since
               interference doesn't come from a job of task [tsk]
               [task_interference tsk = 1]. Which reduces to [1 ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_idle:
              interference j t + scheduled_at sched j t <=
              service_of_jobs_at (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t +
              task_interference_received_before tsk t2 t.
            Proof.
              move: (H_busy_interval) => [[/andP [BUS LT] _] _].
              rewrite /cumul_task_interference /definitions.cumul_interference
                      /Sequential_Abstract_RTA.cumul_task_interference /task_interference_received_before
                      /task_scheduled_at /task_schedule.task_scheduled_at /service_of_jobs_at
                      /service_of_jobs.service_of_jobs_at/= scheduled_at_def.
              rewrite !H_idle/=.
              rewrite big1_eq addn0 add0n.
              case INT: (interference j t); last by done.
              simpl; rewrite lt0b.
              apply/hasP; exists j; last by done.
                by rewrite mem_filter; apply/andP; split;
                  [rewrite H_job_of_tsk | eapply arrived_between_implies_in_arrivals; eassumption].
            Qed.

          End Case1.

          Section Case2.

            (** Assume a job [j'] from another task is scheduled at time [t]. *)
            Variable j' : Job.
            Hypothesis H_sched :  sched t = Some j'.
            Hypothesis H_not_job_of_tsk : job_task j' != tsk.

            (** If a job [j]' from another task is scheduled at time [t],
               then [interference j t = 1, scheduled_at j t = 0]. But
               since interference doesn't come from a job of task [tsk]
               [task_interference tsk = 1]. Which reduces to [1 ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_task:
              interference j t + scheduled_at sched j t <=
              service_of_jobs_at (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t +
              task_interference_received_before tsk t2 t.
            Proof.
              move: (H_busy_interval) => [[/andP [BUS LT] _] _].
              rewrite /cumul_task_interference /definitions.cumul_interference
                      /Sequential_Abstract_RTA.cumul_task_interference /task_interference_received_before
                      /task_scheduled_at /task_schedule.task_scheduled_at /service_of_jobs_at
                      /service_of_jobs.service_of_jobs_at scheduled_at_def/=.
              have ARRs: arrives_in arr_seq j'; first by apply H_jobs_come_from_arrival_sequence with t; rewrite scheduled_at_def; apply/eqP.
              rewrite H_sched H_not_job_of_tsk; simpl.
              rewrite (negbTE (option_inj_neq (neqprop_to_neqbool
                                                 (diseq (fun j => job_task j = tsk) _ _
                                                        (neqbool_to_neqprop H_not_job_of_tsk) H_job_of_tsk)))) addn0.
              have ZERO: \sum_(i <- arrivals_between t1 (t1 + A + ε) | job_task i == tsk) (Some j' == Some i) = 0.
              { apply big1; move => j2 /eqP TSK2; apply/eqP; rewrite eqb0.
                apply option_inj_neq, neqprop_to_neqbool, (diseq (fun j => job_task j = tsk) _ _
                                                                 (neqbool_to_neqprop H_not_job_of_tsk) TSK2).
              } rewrite ZERO ?addn0 add0n; simpl; clear ZERO.
              case INT: (interference j t); last by done.
              simpl; rewrite lt0b.
              apply/hasP; exists j; last by done.
                by rewrite  mem_filter; apply/andP; split;
                  [rewrite H_job_of_tsk | eapply arrived_between_implies_in_arrivals; eassumption].
            Qed.

          End Case2.

          Section Case3.

            (** Assume a job [j'] (different from j) of task [tsk] is scheduled at time [t]. *)
            Variable j' : Job.
            Hypothesis H_sched :  sched t = Some j'.
            Hypothesis H_not_job_of_tsk : job_task j' == tsk.
            Hypothesis H_j_neq_j' : j != j'.

            (** If a job [j'] (different from [j]) of task [tsk] is scheduled at time [t], then
               [interference j t = 1, scheduled_at j t = 0]. Moreover, since interference
               comes from a job of the same task [task_interference tsk = 0]. However,
               in this case [service_of_jobs of tsk = 1]. Which reduces to [1 ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_job:
              interference j t + scheduled_at sched j t <=
              service_of_jobs_at (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t +
              task_interference_received_before tsk t2 t.
            Proof.
              move: (H_busy_interval) => [[/andP [BUS LT] _] _].
              rewrite /cumul_task_interference /definitions.cumul_interference
                      /Sequential_Abstract_RTA.cumul_task_interference /task_interference_received_before
                      /task_scheduled_at /task_schedule.task_scheduled_at /service_of_jobs_at
                      /service_of_jobs.service_of_jobs_at scheduled_at_def/=.
              have ARRs: arrives_in arr_seq j'; first by apply H_jobs_come_from_arrival_sequence with t; rewrite scheduled_at_def; apply/eqP.
              rewrite H_sched H_not_job_of_tsk addn0; simpl;
                rewrite [Some j' == Some j](negbTE (option_inj_neq (neq_sym H_j_neq_j'))) addn0.
              replace (interference j t) with true; last first.
              { have NEQT: t1 <= t < t2.
                { by move: H_t_in_interval => /andP [NEQ1 NEQ2]; apply/andP; split; last apply ltn_trans with (t1 + x). }
                move: (H_work_conserving j t1 t2 t H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval NEQT) => [Hn _].
                apply/eqP;rewrite eq_sym eqb_id; apply/negPn/negP; intros CONTR; move: CONTR => /negP CONTR.
                apply Hn in CONTR; rewrite scheduled_at_def in CONTR; simpl in CONTR.
                  by rewrite H_sched [Some j' == Some j](negbTE (option_inj_neq (neq_sym H_j_neq_j'))) in CONTR.
              }
              rewrite big_mkcond; apply/sum_seq_gt0P; exists j'; split; last first.
              { by move: H_not_job_of_tsk => /eqP TSK; rewrite /job_of_task TSK eq_refl eq_refl. }
              { intros. have ARR:= arrives_after_beginning_of_busy_interval j j' _ _ _ _ _ t1 t2 _ t.
                feed_n 8 ARR; try (done || by move: H_t_in_interval => /andP [T1 T2]).
                { by move: H_not_job_of_tsk => /eqP TSK; rewrite TSK. }
                { move: H_sched => /eqP SCHEDt.
                  apply scheduled_implies_pending;
                  auto using ideal_proc_model_ensures_ideal_progress.
                  by rewrite scheduled_at_def. }
                case_eq (job_arrival j' <= job_arrival j) => ARRNEQ.
                { move: ARR => /andP [РР _].
                  eapply arrived_between_implies_in_arrivals; eauto 2.
                    by apply/andP; split; last rewrite /A subnKC // addn1 ltnS. }
                { exfalso.
                  apply negbT in ARRNEQ; rewrite -ltnNge in ARRNEQ.
                  move: (H_sequential_tasks j j' t) => CONTR.
                  feed_n 3 CONTR; try done.
                  { by rewrite /same_task eq_sym H_job_of_tsk. }
                  { by move: H_sched => /eqP SCHEDt; rewrite scheduled_at_def. }
                  move: H_job_j_is_not_completed => /negP T; apply: T.
                  apply completion_monotonic with t; try done.
                    by apply ltnW; move: H_t_in_interval => /andP [_ NEQ]. }
              }
            Qed.

          End Case3.

          Section Case4.

            (** Assume that job [j] is scheduled at time [t]. *)
            Hypothesis H_sched : sched t = Some j.

            (** If job [j] is scheduled at time [t], then [interference = 0, scheduled_at = 1], but
             note that [service_of_jobs of tsk = 1], therefore inequality reduces to [1 ≤ 1]. *)
            Lemma interference_plus_sched_le_serv_of_task_plus_task_interference_j:
              interference j t + scheduled_at sched j t <=
              service_of_jobs_at (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t +
              task_interference_received_before tsk t2 t.
            Proof.
              have j_is_in_arrivals_between: j \in arrivals_between t1 (t1 + A + ε).
              { eapply arrived_between_implies_in_arrivals; eauto 2.
                move: (H_busy_interval) => [[/andP [GE _] [_ _]] _].
                  by apply/andP; split; last rewrite /A subnKC // addn1.
              } intros.
              rewrite /cumul_task_interference /definitions.cumul_interference
                      /Sequential_Abstract_RTA.cumul_task_interference /task_interference_received_before
                      /task_scheduled_at /task_schedule.task_scheduled_at /service_of_jobs_at
                      /service_of_jobs.service_of_jobs_at scheduled_at_def.
              rewrite H_sched H_job_of_tsk neq_antirefl addn0; simpl.
              move: (H_work_conserving j _ _ t H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval) => WORK.
              feed WORK.
              { move: H_t_in_interval => /andP [NEQ1 NEQ2].
                  by apply/andP; split; last apply ltn_trans with (t1 + x). }
              move: WORK => [_ ZIJT].
              feed ZIJT; first by rewrite scheduled_at_def H_sched; simpl.
              move: ZIJT => /negP /eqP; rewrite eqb_negLR; simpl; move => /eqP ZIJT; rewrite ZIJT; simpl; rewrite add0n.
              rewrite !eq_refl; simpl; rewrite big_mkcond //=; apply/sum_seq_gt0P.
                by exists j; split; [apply j_is_in_arrivals_between | rewrite /job_of_task H_job_of_tsk H_sched !eq_refl].
            Qed.

          End Case4.

          (** We use the above case analysis to prove that any time instant
             t ∈ <<[t1, t1 + x)>> the sum of [interference j t] and [scheduled_at j t]
             is no larger than the sum of [the service received by jobs of task
             tsk at time t] and [task_iterference tsk t]. *)
          Lemma interference_plus_sched_le_serv_of_task_plus_task_interference:
            interference j t + scheduled_at sched j t
            <= service_of_jobs_at (job_of_task tsk) (arrivals_between t1 (t1 + A + ε)) t
              + task_interference_received_before tsk t2 t.
          Proof.
            move: (H_busy_interval) => [[/andP [BUS LT] _] _].
            case SCHEDt: (sched t) => [j1 | ].
            2: by apply interference_plus_sched_le_serv_of_task_plus_task_interference_idle.
            have ARRs: arrives_in arr_seq j1;
              first by apply H_jobs_come_from_arrival_sequence with t; rewrite scheduled_at_def; apply/eqP.
            case_eq (job_task j1 == tsk) => TSK.
            2: by eapply interference_plus_sched_le_serv_of_task_plus_task_interference_task; [eassumption| apply/negbT].
            case EQ: (j == j1); [move: EQ => /eqP EQ; subst j1 | ].
            1: by apply interference_plus_sched_le_serv_of_task_plus_task_interference_j.
            eapply interference_plus_sched_le_serv_of_task_plus_task_interference_job;
              auto; repeat split; eauto; apply/eqP; move: EQ => /eqP EQ; auto.
          Qed.

        End CaseAnalysis.

        (** Next we prove cumulative version of the lemma above. *)
        Lemma cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference:
          cumul_interference j t1 (t1 + x)
          <= (task_service_of_jobs_in (arrivals_between t1 (t1 + A + ε)) t1 (t1 + x)
             - service_during sched j t1 (t1 + x)) + cumul_task_interference t2 t1 (t1 + x).
        Proof.
          have j_is_in_arrivals_between: j \in arrivals_between t1 (t1 + A + ε).
          { eapply arrived_between_implies_in_arrivals; eauto 2.
            move: (H_busy_interval) => [[/andP [GE _] [_ _]] _].
              by apply/andP; split; last rewrite /A subnKC // addn1.
          }
          rewrite /cumul_interference /cumul_interference /task_service_of_jobs_in
          /service_of_jobs.task_service_of_jobs_in
          /service_of_jobs exchange_big //=.
          rewrite -(leq_add2r (\sum_(t1 <= t < (t1 + x)) service_at sched j t)).
          rewrite [X in _ <= X]addnC addnA subnKC; last first.
          { rewrite exchange_big //= (big_rem j) //=; auto using j_is_in_arrivals_between.
              by rewrite /job_of_task H_job_of_tsk eq_refl leq_addr. }
          rewrite -big_split -big_split //=.
          rewrite big_nat_cond [X in _ <= X]big_nat_cond leq_sum //; move => t /andP [NEQ _].
          rewrite -scheduled_at_def.
            by apply interference_plus_sched_le_serv_of_task_plus_task_interference.
        Qed.

        (** On the other hand, the service terms in the inequality
           above can be upper-bound by the workload terms. *)
        Lemma serv_of_task_le_workload_of_task_plus:
          task_service_of_jobs_in (arrivals_between t1 (t1 + A + ε)) t1 (t1 + x)
          - service_during sched j t1 (t1 + x) + cumul_task_interference t2 t1 (t1 + x)
          <= (task_workload_between t1 (t1 + A + ε) - job_cost j)
            + cumul_task_interference t2 t1 (t1 + x).
        Proof.
          have j_is_in_arrivals_between: j \in arrivals_between t1 (t1 + A + ε).
          { eapply arrived_between_implies_in_arrivals; eauto 2.
            move: (H_busy_interval) => [[/andP [GE _] [_ _]] _].
              by apply/andP; split; last rewrite /A subnKC // addn1.
          }
          rewrite leq_add2r.
          rewrite /task_workload /task_service_of_jobs_in
                  /service_of_jobs.task_service_of_jobs_in/service_of_jobs /workload_of_jobs /job_of_task.
          rewrite (big_rem j) ?[X in _ <= X - _](big_rem j) //=; auto using j_is_in_arrivals_between.
          rewrite /job_of_task  H_job_of_tsk eq_refl.
          rewrite addnC -addnBA; last by done.
          rewrite [X in _ <= X - _]addnC -addnBA; last by done.
          rewrite !subnn !addn0.
            by apply service_of_jobs_le_workload; auto using ideal_proc_model_provides_unit_service.
        Qed.

        (** Finally, we show that the cumulative interference of job j in the interval <<[t1, t1 + x)>>
           is bounded by the sum of the task workload in the interval [t1, t1 + A + ε) and
           the cumulative interference of [j]'s task in the interval [t1, t1 + x). *)
        Lemma cumulative_job_interference_le_task_interference_bound:
          cumul_interference j t1 (t1 + x)
          <= (task_workload_between t1 (t1 + A + ε) - job_cost j)
            + cumul_task_interference t2 t1 (t1 + x).
        Proof.
          apply leq_trans with
              (task_service_of_jobs_in (arrivals_between t1 (t1 + A + ε)) t1 (t1 + x)
               - service_during sched j t1 (t1 + x)
               + cumul_task_interference t2 t1 (t1 + x));
            [ apply cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference
            | apply serv_of_task_le_workload_of_task_plus].
        Qed.

      End TaskInterferenceBoundsInterference.

      (** In order to obtain a more convenient bound of the cumulative interference, we need to
         abandon the actual workload in favor of a bound which depends on task parameters only.
         So, we show that actual workload of the task excluding workload of any job [j] is no
         greater than bound of workload excluding the cost of job [j]'s task. *)
      Lemma task_rbf_excl_tsk_bounds_task_workload_excl_j:
        task_workload_between t1 (t1 + A + ε) - job_cost j <= task_rbf (A + ε) - task_cost tsk.
      Proof.
        move: H_j_arrives H_job_of_tsk H_busy_interval => ARR TSK [[/andP [JAGET1 JALTT2] _] _].
        apply leq_trans with
            (task_cost tsk * number_of_task_arrivals arr_seq tsk t1 (t1 + A + ε) - task_cost tsk); last first.
        { rewrite leq_sub2r // leq_mul2l; apply/orP; right.
          rewrite -addnA -{2}[(A+1)](addKn t1).
            by apply H_is_arrival_curve; auto using leq_addr. }
        have Fact6: j \in arrivals_between (t1 + A) (t1 + A + ε).
        { apply arrived_between_implies_in_arrivals; try done.
          apply/andP; split; rewrite /A subnKC //.
            by rewrite addn1 ltnSn //. }
        have Fact4: j \in arrivals_at arr_seq (t1 + A).
        { by move: ARR => [t ARR]; rewrite subnKC //; feed (H_arrival_times_are_consistent j t); try (subst t). }
        have Fact1: 1 <= number_of_task_arrivals arr_seq tsk (t1 + A) (t1 + A + ε).
        { rewrite /number_of_task_arrivals /task_arrivals_between /arrival_sequence.arrivals_between.
            by rewrite -count_filter_fun -has_count; apply/hasP; exists j; last rewrite TSK.
        }
        rewrite (@num_arrivals_of_task_cat _ _ _ _ _ (t1 + A)); last by apply/andP; split; rewrite leq_addr //.
        rewrite mulnDr.
        have Step1: task_workload_between t1 (t1 + A + ε)
                    = task_workload_between t1 (t1 + A) + task_workload_between (t1 + A) (t1 + A + ε).
        { by apply workload_of_jobs_cat; apply/andP; split; rewrite leq_addr. } rewrite Step1; clear Step1.
        rewrite -!addnBA; first last.
        { by rewrite /task_workload_between /workload.task_workload_between /task_workload
                     /workload_of_jobs /job_of_task (big_rem j) //=  TSK eq_refl leq_addr. }
        { apply leq_trans with (task_cost tsk); first by done.
            by rewrite -{1}[task_cost tsk]muln1 leq_mul2l; apply/orP; right. }
        rewrite leq_add; [by done | by eapply task_workload_le_num_of_arrivals_times_cost; eauto | ].
        rewrite /task_workload_between /workload.task_workload_between /task_workload /workload_of_jobs
                /arrival_sequence.arrivals_between /number_of_task_arrivals /task_arrivals_between
                /arrival_sequence.arrivals_between /job_of_task.
        rewrite {1}addn1 big_nat1 addn1 big_nat1.
        rewrite (big_rem j) //= TSK !eq_refl; simpl.
        rewrite addnC -addnBA // subnn addn0.
        rewrite (filter_size_rem _ j); [ | by done | by rewrite TSK].
        rewrite mulnDr mulnC muln1 -addnBA // subnn addn0 mulnC.
        apply sum_majorant_constant.
        move => j' ARR' /eqP TSK2.
          by rewrite -TSK2; apply H_valid_job_cost; exists (t1 + A); apply rem_in in ARR'.
      Qed.

      (** Finally, we use the lemmas above to obtain the bound on
         [interference] in terms of [task_rbf] and [task_interference]. *)
      Lemma cumulative_job_interference_bound:
        cumul_interference j t1 (t1 + x)
        <= (task_rbf (A + ε) - task_cost tsk) + cumul_task_interference t2 t1 (t1 + x).
      Proof.
        set (y := t1 + x) in *.
        have IN: j \in arrivals_between t1 (t1 + A + ε).
        { eapply arrived_between_implies_in_arrivals; eauto 2.
          move: (H_busy_interval) => [[/andP [GE _] _] _].
            by apply/andP; split; last rewrite /A subnKC // addn1.
        }
        apply leq_trans with (task_workload_between t1 (t1+A+ε) - job_cost j + cumul_task_interference t2 t1 y).
        - by apply cumulative_job_interference_le_task_interference_bound.
        - rewrite leq_add2r.
          eapply task_rbf_excl_tsk_bounds_task_workload_excl_j; eauto 2.
      Qed.

    End BoundOfCumulativeJobInterference.

    (** In this section, we prove that [H_R_is_maximum_seq] implies [H_R_is_maximum]. *)
    Section MaxInSeqHypothesisImpMaxInNonseqHypothesis.

      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_task j = tsk.

      (** For simplicity, let's define a local name for the search space. *)
      Let is_in_search_space A :=
        is_in_search_space tsk L total_interference_bound A.

      (** We prove that [H_R_is_maximum] holds. *)
      Lemma max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis:
        forall (A : duration),
          is_in_search_space A ->
          exists (F : duration),
            A + F = task_run_to_completion_threshold tsk +
                    (task_rbf (A + ε) - task_cost tsk + task_interference_bound_function tsk A (A + F)) /\
            F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.
      Proof.
        move: H_valid_run_to_completion_threshold => [PRT1 PRT2].
        intros A INSP.
        clear H_sequential_tasks H_interference_and_workload_consistent_with_sequential_tasks.
        move: (H_R_is_maximum_seq _ INSP) => [F [FIX LE]].
        exists F; split; last by done.
        rewrite {1}FIX.
        apply/eqP.
        rewrite addnA eqn_add2r.
        rewrite addnBA; last first.
        { apply leq_trans with (task_rbf 1).
          eapply task_rbf_1_ge_task_cost; eauto 2.
              eapply task_rbf_monotone; eauto 2.
                by rewrite addn1.
        }
          by rewrite subnBA; auto; rewrite addnC.
      Qed.

    End MaxInSeqHypothesisImpMaxInNonseqHypothesis.

    (** Finally, we apply the [uniprocessor_response_time_bound] theorem, and using the
       lemmas above, we prove that all the requirements are satisfied. So, R is a response
       time bound. *)
    Theorem uniprocessor_response_time_bound_seq:
      response_time_bounded_by tsk R.
    Proof.
      intros j ARR TSK.
      eapply uniprocessor_response_time_bound with
          (interference_bound_function :=
             fun tsk A R => task_rbf (A + ε) - task_cost tsk + task_interference_bound_function tsk A R)
          (interfering_workload0 := interfering_workload); eauto 2.
      apply ideal_proc_model_ensures_ideal_progress.
      apply ideal_proc_model_provides_unit_service.
      { clear ARR TSK H_R_is_maximum_seq R j.
        intros t1 t2 R j BUSY NEQ ARR TSK COMPL.
        move: (posnP (@job_cost _ H3 j)) => [ZERO|POS].
        { exfalso.
          move: COMPL => /negP COMPL; apply: COMPL.
            by rewrite /service.completed_by /completed_by ZERO.
        }
        set (A := job_arrival j - t1) in *.
        apply leq_trans with
            (task_rbf (A + ε) - task_cost tsk + cumul_task_interference t2 t1 (t1 + R)).
        - by eapply cumulative_job_interference_bound; eauto 2.
        - by rewrite leq_add2l; apply H_task_interference_is_bounded.
      }
      { by eapply max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis; eauto. }
    Qed.

  End ResponseTimeBound.

End Sequential_Abstract_RTA.
