Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.arrival.basic.arrival_bounds.
Require Import prosa.classic.model.schedule.uni.schedule_of_task prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedulability prosa.classic.model.schedule.uni.response_time
               prosa.classic.model.schedule.uni.service.
Require Import prosa.classic.model.schedule.uni.limited.busy_interval prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.analysis.uni.basic.workload_bound_fp.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTimeAnalysisFP.

  Import Job ScheduleOfTask SporadicTaskset Priority ResponseTime
         TaskArrival ArrivalBounds WorkloadBoundFP Platform Schedulability
         BusyIntervalJLFP Workload Service.

  (* In this section, we prove that any fixed point in the RTA for uniprocessor
     FP scheduling is a response-time bound. *)
  Section ResponseTimeBound.

    Context {SporadicTask: eqType}.
    Variable task_cost: SporadicTask -> time.
    Variable task_period: SporadicTask -> time.
    Variable task_deadline: SporadicTask -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> SporadicTask.
    
    (* Assume any job arrival sequence with consistent, duplicate-free arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_no_duplicate_arrivals: arrival_sequence_is_a_set arr_seq.
    
    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Consider a task set ts where all tasks have valid parameters... *)
    Variable ts: seq SporadicTask.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.

    (* ... and assume that all jobs in the arrival sequence come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ... where jobs do not execute before their arrival times nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Consider an FP policy that indicates a higher-or-equal priority relation,
       and assume that the relation is reflexive and transitive. *)
    Variable higher_eq_priority: FP_policy SporadicTask.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    
    (* Next, assume that the schedule is a work-conserving FP schedule. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_respects_fp_policy:
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority.
    
    (* Now we proceed with the analysis.
       Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: SporadicTask.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Recall the definition of response-time bound and the total workload bound W
       for tasks with higher-or-equal priority (with respect to tsk). *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    Let W := total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk.

    (* Let R be any positive fixed point of the response-time recurrence. *)
    Variable R: time.
    Hypothesis H_R_positive: R > 0.
    Hypothesis H_response_time_is_fixed_point: R = W R.

    (* Since R = W R bounds the workload of higher-or-equal priority
       in any interval of length R, it follows from the busy-interval
       lemmas that R bounds the response-time of job j.
       (For more details, see model/uni/basic/busy_interval.v and
        analysis/uni/basic/workload_bound_fp.v.) *)
    Theorem uniprocessor_response_time_bound_fp:
      response_time_bounded_by tsk R.
    Proof.
      rename H_response_time_is_fixed_point into FIX.
      intros j ARRj JOBtsk.
      move: (posnP (job_cost j)) => [Z|POS].
      { by rewrite /is_response_time_bound_of_job /completed_by Z. }
      set prio := FP_to_JLFP job_task higher_eq_priority.
      apply busy_interval_bounds_response_time with
          (arr_seq0 := arr_seq)
          (higher_eq_priority0 := prio)
          (priority_inversion_bound := 0); try by done.
      - by intros x; apply H_priority_is_reflexive.
      { intros t1 t2 BUSY.
        rewrite /cumulative_priority_inversion /is_priority_inversion leqn0.
        rewrite big_nat big1 //; move => t NEQ.
        destruct (sched t) eqn:SCHED; last by done.
        have HP := pending_hp_job_exists
                     job_arrival job_cost arr_seq _ sched
                     prio _ ARRj _ _ _ _ _ BUSY _ NEQ.
        feed_n 4 HP; try done.
        { by intros x; apply H_priority_is_reflexive. }
        move: HP => [jhp [ARRjhp [PEND PRIO]]].
        apply/eqP; rewrite eqb0 Bool.negb_involutive.
        rewrite /prio /FP_to_JLFP.
        eapply H_priority_is_transitive with (job_task jhp); last by done.
        destruct (s == jhp) eqn:EQ; first by move: EQ => /eqP EQ; subst s. 
        apply H_respects_fp_policy with t; try done.
        { apply/andP; split; first by done.
          rewrite /scheduled_at SCHED.
          apply/negP. intros SNEQ; move: SNEQ => /eqP SNEQ.
          move: EQ => /negP EQ; apply EQ.
            by inversion SNEQ.
        } 
        { by rewrite /scheduled_at SCHED. }
      }
      apply fp_workload_bound_holds with
          (job_arrival0 := job_arrival) (task_cost0 := task_cost)
          (task_period0 := task_period) (task_deadline0 := task_deadline)
          (job_deadline0 := job_deadline) (ts0 := ts); try (by done).
        by rewrite JOBtsk.
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.