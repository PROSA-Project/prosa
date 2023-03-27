From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Export prosa.analysis.facts.model.ideal.schedule.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.analysis.abstract.search_space.
Require Export prosa.analysis.abstract.abstract_rta.
Require Export prosa.analysis.abstract.iw_auxiliary.

(** * Abstract Response-Time Analysis For Processor State with Ideal Uni-Service Progress Model *)
(** In this module, we present an instantiation of the general
    response-time analysis framework for models that satisfy the ideal
    uni-service progress assumptions. *)

(** We prove that the maximum (with respect to the set of offsets)
    among the solutions of the response-time bound recurrence is a
    response-time bound for [tsk]. Note that in this section we add
    additional restrictions on the processor state. These assumptions
    allow us to eliminate the second equation from [aRTA+]'s
    recurrence since jobs experience no delays while executing
    non-preemptively. *)
Section AbstractRTAIdeal.

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

  (** Consider any kind of uni-service ideal processor state model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_ideal_progress_proc_model : ideal_progress_proc_model PState.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** Next, consider any schedule of this arrival sequence... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Consider a task set [ts]... *)
  Variable ts : list Task.

  (** ... and a task [tsk] of [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
      is, [task_rtc tsk] is (1) no bigger than [tsk]'s cost and (2)
      for any job [j] of task [tsk] [job_rtct j] is bounded by
      [task_rtct tsk]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** Assume we are provided with abstract functions for Interference
      and Interfering Workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** We assume that the scheduler is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Let [L] be a constant that bounds any busy interval of task [tsk]. *)
  Variable L : duration.
  Hypothesis H_busy_interval_exists :
    busy_intervals_are_bounded_by arr_seq sched tsk L.

  (** Next, assume that [interference_bound_function] is a bound on
      the interference incurred by jobs of task [tsk] parametrized by
      the relative arrival time [A]. *)
  Variable interference_bound_function : Task -> (* A *) duration -> (* Δ *) duration -> duration.
  Hypothesis H_job_interference_is_bounded :
    job_interference_is_bounded_by
      arr_seq sched tsk interference_bound_function (relative_arrival_time_of_job_is_A sched).

  (** To apply the generalized aRTA, we have to instantiate [IBF_P]
      and [IBF_NP]. In this file, we assume we are given a generic function
      [interference_bound_function] that bounds interference of jobs
      of tasks in [ts] and which have to be instantiated in subsequent
      files. We use this function to instantiate [IBF_P]. *)

  (** However, we still have to instantiate function [IBF_NP], which
      is a function that bounds interference in a non-preemptive stage
      of execution. We prove that this function can be instantiated
      with a constant function [λ tsk F Δ ⟹ F - task_rtct tsk]. *)
  Let IBF_NP (tsk : Task) (F : duration) (Δ : duration) := F - task_rtct tsk.

  (** Let us re-iterate on the intuitive interpretation of this
      function. Since [F] is a solution to the first equation
      [task_rtct tsk + IBF_P tsk A F <= F], we know that by time
      instant [t1 + F] a job receives [task_rtct tsk] units of service
      and, hence, it becomes non-preemptive. Given this information,
      how can we bound the job's interference in an interval <<[t1, t1
      + R)>>? Note that this interval starts with the beginning of the
      busy interval. We know that the job receives [F - task_rtct tsk]
      units of interference, and there will no more
      interference. Hence, [IBF_NP tsk F Δ := F - task_rtct tsk]. *)
  Lemma nonpreemptive_interference_is_bounded :
    job_interference_is_bounded_by
      arr_seq sched tsk IBF_NP (relative_time_to_reach_rtct sched tsk interference_bound_function).
  Proof.
    move => t1 t2 Δ j ARR TSK BUSY LT NCOM F RTC; specialize (RTC _ _ BUSY).
    have POS : 0 < job_cost j.
    { move_neq_up ZE; move: ZE; rewrite leqn0; move => /eqP ZE.
      move: NCOM => /negP NCOM; apply: NCOM.
      by rewrite /completed_by ZE.
    }
    move: (BUSY) => [PREF _].
    move : (TSK) (BUSY) RTC => /eqP TSKeq [[/andP [LE1 LE2] [QT1 AQT]] QT2] [LEQ RTC].
    rewrite leq_subRL_impl // addnC -/cumulative_interference.
    destruct (leqP t2 (t1 + F)) as [NEQ1|NEQ1]; last destruct (leqP F Δ) as [NEQ2|NEQ2].
    { rewrite -leq_subLR in NEQ1.
      rewrite -(leqRW NEQ1) (leqRW RTC) (leqRW (service_at_most_cost _ _ _ _ _)) //
              (leqRW (service_within_busy_interval_ge_job_cost  _ _ _ _ _ _ _)); rt_eauto.
      rewrite (leqRW (cumulative_interference_sub _ t1 _ t1 t2 _ _ )); try lia.
      have LLL : (t1 < t2) = true by apply leq_ltn_trans with (t1 + Δ); lia.
      interval_to_duration t1 t2 k.
      eapply leq_trans.
      - by rewrite addnC; (eapply service_and_interference_bounded with (t := t1) (t3 := t1+k)
                        || eapply service_and_interference_bounded with (t := t1) (t2 := t1+k)); rt_eauto.
      - lia.
    }
    { have NoInterference: cumulative_interference j (t1 + F) (t1 + Δ) = 0.
      { rewrite /cumulative_interference /definitions.cumulative_interference big_nat.
        apply big1; move => t /andP [GE__t LT__t].
        apply/eqP; rewrite eqb0; apply/negP; eapply H_work_conserving; rt_eauto.
        { by apply/andP; split; lia. }
        eapply H_ideal_progress_proc_model, job_nonpreemptive_after_run_to_completion_threshold; rt_eauto.
        - by rewrite -(leqRW RTC); apply H_valid_run_to_completion_threshold.
        - by move: NCOM; apply contra; apply completion_monotonic; lia.
      }
      rewrite (leqRW RTC); erewrite cumulative_interference_cat with (t := t1 + F); last by lia.
      rewrite NoInterference addn0; erewrite no_service_before_busy_interval; rt_eauto.
      by rewrite addnC; eapply service_and_interference_bounded; rt_eauto.
    }
    { rewrite (leqRW RTC) (leqRW (cumulative_interference_sub _ t1 _ t1 (t1 + F) _ _ )); try lia.
      erewrite no_service_before_busy_interval; rt_eauto.
      by rewrite addnC; eapply service_and_interference_bounded; rt_eauto.
    }
  Qed.

  (** For simplicity, let's define a local name for the search space. *)
  Let is_in_search_space A := is_in_search_space tsk L interference_bound_function A.

  (** Consider any value [R] that upper-bounds the solution of each
      response-time recurrence, i.e., for any relative arrival time A
      in the search space, there exists a corresponding solution [F]
      such that [F + (task_cost tsk - task_rtc tsk) <= R]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum_ideal :
    forall A,
      is_in_search_space A ->
      exists F,
        task_rtct tsk + interference_bound_function tsk A (A + F) <= A + F /\
        F + (task_cost tsk - task_rtct tsk) <= R.

  (** Using the lemma about [IBF_NP], we instantiate the general RTA
      theorem's result to the ideal uniprocessor's case to prove that
      [R] is a response-time bound. *)
  Theorem uniprocessor_response_time_bound_ideal :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    try (eapply uniprocessor_response_time_bound with (IBF_NP := fun tsk F Δ => F - task_rtct tsk)
         || eapply uniprocessor_response_time_bound with (IBF_NP0 := fun tsk F Δ => F - task_rtct tsk)); rt_eauto.
    { by apply nonpreemptive_interference_is_bounded. }
    { move => F _.
      destruct (leqP F (task_rtct tsk)) as [NEQ|NEQ].
      - eapply leq_trans; [apply NEQ | ].
        by eapply leq_trans; [apply H_valid_run_to_completion_threshold | lia].
      - by rewrite addnBCA; [lia | apply H_valid_run_to_completion_threshold | lia].
    }
    { move => A SP; specialize (H_R_is_maximum_ideal A SP).
      destruct H_R_is_maximum_ideal as [F [EQ1 EQ2]].
      exists (A + F); split; first by done.
      eapply leq_trans; [ | by erewrite leq_add2l; apply EQ2].
      by rewrite addnBCA; [lia | apply H_valid_run_to_completion_threshold | lia].
    }
  Qed.

End AbstractRTAIdeal.
