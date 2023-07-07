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
  Context `{JobCost Job}.
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

  (** We assume that the schedule is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Unlike the previous theorem
      [uniprocessor_response_time_bound_ideal], we assume that (1)
      tasks are sequential, moreover (2) functions interference and
      interfering_workload are consistent with the hypothesis of
      sequential tasks. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.
  Hypothesis H_interference_and_workload_consistent_with_sequential_tasks :
    interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk.

  (** Assume we have a constant [L] that bounds the busy interval of
      any of [tsk]'s jobs. *)
  Variable L : duration.
  Hypothesis H_busy_interval_exists :
    busy_intervals_are_bounded_by arr_seq sched tsk L.

  (** Next, we assume that [task_IBF] is a bound on interference
      incurred by the task. *)
  Variable task_IBF : Task -> duration -> duration -> duration.
  Hypothesis H_task_interference_is_bounded :
    task_interference_is_bounded_by arr_seq sched tsk task_IBF.

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let arrivals_between := arrivals_between arr_seq.

  (** Given any job [j] of task [tsk] that arrives exactly [A] units
      after the beginning of the busy interval, the bound on the total
      interference incurred by [j] within an interval of length [Δ] is
      no greater than [task_rbf (A + ε) - task_cost tsk + task's IBF
      Δ]. Note that in case of sequential tasks the bound consists of
      two parts: (1) the part that bounds the interference received
      from other jobs of task [tsk] -- [task_rbf (A + ε) - task_cost
      tsk] and (2) any other interference that is bounded by
      [task_IBF(tsk, A, Δ)]. *)
  Let total_interference_bound (tsk : Task) (A Δ : duration) :=
    task_rbf (A + ε) - task_cost tsk + task_IBF tsk A Δ.

  (** Note that since we consider the modified interference bound
      function, the search space has also changed. One can see that
      the new search space is guaranteed to include any A for which
      [task_rbf (A) ≠ task_rbf (A + ε)], since this implies the fact
      that [total_interference_bound (tsk, A, Δ) ≠
      total_interference_bound (tsk, A + ε, Δ)]. *)
  Let is_in_search_space_seq := is_in_search_space tsk L total_interference_bound.

  (** Consider any value [R], and assume that for any relative arrival
      time [A] from the search space there is a solution [F] of the
      response-time recurrence that is bounded by [R]. In contrast to
      the formula in "non-sequential" Abstract RTA, assuming that
      tasks are sequential leads to a more precise response-time
      bound. Now we can explicitly express the interference caused by
      other jobs of the task under consideration.

      To understand the right part of the fix-point in the equation,
      it is helpful to note that the bound on the total interference
      ([bound_of_total_interference]) is equal to [task_rbf (A + ε) -
      task_cost tsk + task_IBF tsk A Δ]. Besides, a job must receive
      enough service to become non-preemptive [task_lock_in_service
      tsk]. The sum of these two quantities is exactly the right-hand
      side of the equation. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum_seq :
    forall (A : duration),
      is_in_search_space_seq A ->
      exists (F : duration),
        A + F >= (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk)) + task_IBF tsk A (A + F)
        /\ R >= F + (task_cost tsk - task_rtct tsk).

  (** Since we are going to use the
      [uniprocessor_response_time_bound_ideal] theorem to prove the
      theorem of this section, we have to show that all the hypotheses
      are satisfied. Namely, we need to show that [H_R_is_maximum_seq]
      implies [H_R_is_maximum]. Note that the fact that hypotheses
      [H_sequential_tasks, H_i_w_are_task_consistent and
      H_task_interference_is_bounded_by] imply
      [H_job_interference_is_bounded] is proven in the file
      [analysis/abstract/IBF/task]. *)

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
                    (task_rbf (A + ε) - task_cost tsk + task_IBF tsk A (A + F))
          /\ R >= F + (task_cost tsk - task_rtct tsk).
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

  (** We apply the [uniprocessor_response_time_bound_ideal] theorem,
      and using the lemmas proven earlier, we prove that all the
      requirements are satisfied. So, [R] is a response-time bound. *)
  Theorem uniprocessor_response_time_bound_seq :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => j ARR TSK.
    eapply uniprocessor_response_time_bound_ideal => //.
    { by apply: task_IBF_implies_job_IBF => //. }
    { by apply: max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis => //. }
  Qed.

End Sequential_Abstract_RTA.
