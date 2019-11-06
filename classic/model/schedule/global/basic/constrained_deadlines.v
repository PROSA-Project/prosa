Require Import rt.util.all.
Require Import rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.priority rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.global.basic.schedule rt.model.schedule.global.basic.interference
               rt.model.schedule.global.basic.platform.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module ConstrainedDeadlines.

  Import Job SporadicTaskset ScheduleOfSporadicTask SporadicTaskset
         TaskArrival Interference Priority Platform.
  
  Section Lemmas.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence ... *)
    Variable arr_seq: arrival_sequence Job.

    (* ... and any schedule of this arrival sequence. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.

    (* Assume all jobs have valid parameters, ...*)
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* In this section we prove the absence of multiple jobs of the same
       task when constrained deadlines are assumed.  *)
    Section NoMultipleJobs.

      (* Assume any work-conserving priority-based scheduler. *)
      Variable higher_eq_priority: JLDP_policy Job.
      Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
      Hypothesis H_respects_JLDP_policy:
        respects_JLDP_policy job_arrival job_cost arr_seq sched higher_eq_priority.

      (* Consider task set ts. *)
      Variable ts: taskset_of sporadic_task.

      (* Assume that all jobs come from the taskset. *)
      Hypothesis H_all_jobs_from_taskset:
        forall j,
          arrives_in arr_seq j -> job_task j \in ts.

      (* Suppose that jobs are sequential, ...*)
      Hypothesis H_sequential_jobs: sequential_jobs sched.
      (* ... jobs must arrive to execute, ... *)
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.
      (* ... and jobs do not execute after completion. *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched.

      (* Assume that the schedule satisfies the sporadic task model ...*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period job_arrival job_task arr_seq.

      (* Consider a valid task tsk, ...*)
      Variable tsk: sporadic_task.
      Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.

      (*... whose job j ... *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Variable H_job_of_tsk: job_task j = tsk.

      (*... is backlogged at time t. *)
      Variable t: time.
      Hypothesis H_j_backlogged: backlogged job_arrival job_cost sched j t.

      (* Assume that any previous jobs of tsk have completed by the period. *)
      Hypothesis H_all_previous_jobs_completed :
        forall j_other tsk_other,
          arrives_in arr_seq j_other ->
          job_task j_other = tsk_other ->
          job_arrival j_other + task_period tsk_other <= t ->
          completed job_cost sched j_other (job_arrival j_other + task_period (job_task j_other)).

      Let scheduled_task_other_than (tsk tsk_other: sporadic_task) :=
        task_is_scheduled job_task sched tsk_other t && (tsk_other != tsk).

      (* Then, there can be at most one pending job of each task at time t. *)
      Lemma platform_at_most_one_pending_job_of_each_task :
        forall j1 j2,
          arrives_in arr_seq j1 ->
          arrives_in arr_seq j2 ->
          pending job_arrival job_cost sched j1 t ->
          pending job_arrival job_cost sched j2 t ->
          job_task j1 = job_task j2 ->
          j1 = j2.
      Proof.
        rename H_sporadic_tasks into SPO, H_all_previous_jobs_completed into PREV.
        intros j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF. 
        move: PENDING1 PENDING2 => /andP [ARRIVED1 /negP NOTCOMP1] /andP [ARRIVED2 /negP NOTCOMP2].
        destruct (leqP (job_arrival j1) (job_arrival j2)) as [BEFORE1 | BEFORE2].
        {
          specialize (SPO j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1).
          exploit (PREV j1 (job_task j1) ARR1);
            [by done | by apply leq_trans with (n := job_arrival j2) | intros COMP1].
          apply NOTCOMP1.
          apply completion_monotonic with (t0 := job_arrival j1 + task_period (job_task j1));
            try (by done).
          by apply leq_trans with (n := job_arrival j2). 
        }
        {
          apply ltnW in BEFORE2.
          exploit (SPO j2 j1); try (by done); [by red; ins; subst | intro SPO'].
          exploit (PREV j2 (job_task j2) ARR2);
            [by done | by apply leq_trans with (n := job_arrival j1) | intros COMP2].
          apply NOTCOMP2.
          apply completion_monotonic with (t0 := job_arrival j2 + task_period (job_task j2));
            try (by done).
          by apply leq_trans with (n := job_arrival j1).
        }
      Qed.

      (* Therefore, all processors are busy with tasks other than tsk. *)
      Lemma platform_cpus_busy_with_interfering_tasks :      
        count (scheduled_task_other_than tsk) ts = num_cpus.
      Proof.
        have UNIQ := platform_at_most_one_pending_job_of_each_task.
        rename H_all_jobs_from_taskset into FROMTS,
               H_sequential_jobs into SEQUENTIAL, H_work_conserving into WORK,
               H_respects_JLDP_policy into PRIO,
               H_j_backlogged into BACK, H_jobs_come_from_arrival_sequence into FROMarr,
               H_job_of_tsk into JOBtsk, H_valid_job_parameters into JOBPARAMS,
               H_valid_task into TASKPARAMS,
               H_all_previous_jobs_completed into PREV, H_completed_jobs_dont_execute into COMP,
               H_jobs_must_arrive_to_execute into ARRIVE.
        apply work_conserving_eq_work_conserving_count in WORK.
        unfold valid_sporadic_job, valid_realtime_job,
               respects_JLDP_policy, completed_jobs_dont_execute,
               sporadic_task_model, is_valid_sporadic_task,
               jobs_of_same_task_dont_execute_in_parallel,
               sequential_jobs in *.  
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        {
          apply leq_trans with (n := count (fun x => task_is_scheduled job_task sched x t) ts);
            first by apply sub_count; first by red; move => x /andP [SCHED _].    
          unfold task_is_scheduled.
          apply count_exists; first by destruct ts.
          {
            intros cpu x1 x2 SCHED1 SCHED2.
            unfold task_scheduled_on in *.
            destruct (sched cpu t); last by done.
            move: SCHED1 SCHED2 => /eqP SCHED1 /eqP SCHED2.
            by rewrite -SCHED1 -SCHED2.
          }
        }
        {
          rewrite -(WORK j t) // -count_predT.       
          apply leq_trans with (n := count (fun j => scheduled_task_other_than tsk (job_task j)) (jobs_scheduled_at sched t));
            last first.
          {
            rewrite -count_map.
            apply count_sub_uniqr; last first.
            {
              move => tsk' /mapP [j' INj' JOBtsk']; subst; apply FROMTS.
              by rewrite mem_scheduled_jobs_eq_scheduled in INj'; eauto 2.
            }
            rewrite map_inj_in_uniq; first by apply scheduled_jobs_uniq.
            red; intros j1 j2 SCHED1 SCHED2 SAMEtsk.
            rewrite 2!mem_scheduled_jobs_eq_scheduled in SCHED1 SCHED2.
            have ARRin1: arrives_in arr_seq j1 by apply (FROMarr j1 t).
              have ARRin2: arrives_in arr_seq j2 by apply (FROMarr j2 t).
              by apply UNIQ; try (by done); apply scheduled_implies_pending. 
          }
          {
            apply sub_in_count; intros j' SCHED' _.
            rewrite mem_scheduled_jobs_eq_scheduled in SCHED'.
            unfold scheduled_task_other_than; apply/andP; split.
            {
              move: SCHED' => /existsP [cpu /eqP SCHED'].
              by apply/existsP; exists cpu; rewrite /task_scheduled_on SCHED' eq_refl.
            }
            {
              apply/eqP; red; intro SAMEtsk; symmetry in SAMEtsk.
              move: BACK => /andP [PENDING NOTSCHED].
              have ARRin': arrives_in arr_seq j' by apply (FROMarr j' t).
              exploit (UNIQ j j'); try (by done);
                [by apply scheduled_implies_pending | by rewrite -SAMEtsk |].
              by intro EQjob; subst; rewrite SCHED' in NOTSCHED.
            }
          }
        }
      Qed.
      
    End NoMultipleJobs.

    (* In this section we also prove the absence of multiple jobs of the same
       task when constrained deadlines are assumed, but in the specific case
       of fixed-priority scheduling.  *)
    Section NoMultipleJobsFP.

      (* Assume any work-conserving priority-based scheduler. *)
      Variable higher_eq_priority: FP_policy sporadic_task.
      Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
      Hypothesis H_respects_JLDP_policy:
        respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority.

      (* Consider any task set ts. *)
      Variable ts: taskset_of sporadic_task.

      (* Assume that all jobs come from the taskset. *)
      Hypothesis H_all_jobs_from_taskset:
        forall j,
          arrives_in arr_seq j -> job_task j \in ts.

      (* Suppose that jobs are sequential, ...*)
      Hypothesis H_sequential_jobs: sequential_jobs sched.
      (* ... jobs must arrive to execute, ... *)
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.
      (* ... and jobs do not execute after completion. *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched.

      (* Assume that jobs arrive sporadically. *)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period job_arrival job_task arr_seq.

      (* Consider a valid task tsk, ...*)
      Variable tsk: sporadic_task.
      Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.

      (*... whose job j ... *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Variable H_job_of_tsk: job_task j = tsk.

      (*... is backlogged at time t <= job_arrival j + task_period tsk. *)
      Variable t: time.
      Hypothesis H_j_backlogged: backlogged job_arrival job_cost sched j t.
      Hypothesis H_t_before_period: t < job_arrival j + task_period tsk.

      (* Recall the definition of a higher-priority task (with respect to tsk). *)
      Let is_hp_task := higher_priority_task higher_eq_priority tsk.

      (* Assume that any jobs of higher-priority tasks complete by their period. *)
      Hypothesis H_all_previous_jobs_completed :
        forall j_other tsk_other,
          arrives_in arr_seq j_other ->
          job_task j_other = tsk_other ->
          is_hp_task tsk_other ->
          completed job_cost sched j_other (job_arrival j_other + task_period tsk_other).

      (* Assume that any jobs of tsk prior to j complete by their period. *)
      Hypothesis H_all_previous_jobs_of_tsk_completed :
        forall j0,
          arrives_in arr_seq j0 ->
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + task_period tsk).
      
      Definition scheduled_task_with_higher_eq_priority (tsk tsk_other: sporadic_task) :=
        task_is_scheduled job_task sched tsk_other t &&
        is_hp_task tsk_other.
                             
      (* Then, there can be at most one pending job of higher-priority tasks at time t. *)
      Lemma platform_fp_no_multiple_jobs_of_interfering_tasks :
        forall j1 j2,
          arrives_in arr_seq j1 ->
          arrives_in arr_seq j2 ->
          pending job_arrival job_cost sched j1 t ->
          pending job_arrival job_cost sched j2 t ->
          job_task j1 = job_task j2 ->
          is_hp_task (job_task j1) ->
          j1 = j2.
      Proof.
        unfold sporadic_task_model in *.
        rename H_sporadic_tasks into SPO, H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_all_previous_jobs_completed into PREV.
        intros j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk INTERF.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF.
        move: PENDING1 PENDING2 => /andP [ARRIVED1 /negP NOTCOMP1] /andP [ARRIVED2 /negP NOTCOMP2].
        destruct (leqP (job_arrival j1) (job_arrival j2)) as [BEFORE1 | BEFORE2].
        {
          specialize (SPO j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1).
          exploit (PREV j1 (job_task j1) ARR1); [by done | by apply INTERF | intros COMP1].
          apply NOTCOMP1.
          apply completion_monotonic with (t0 := job_arrival j1 + task_period (job_task j1));
            try (by done).
          by apply leq_trans with (n := job_arrival j2). 
        }
        {
          apply ltnW in BEFORE2.
          exploit (SPO j2 j1); try (by done); [by red; ins; subst j2 | intro SPO']. 
          exploit (PREV j2 (job_task j2) ARR2);
            [by done | by rewrite -SAMEtsk | intro COMP2 ].
          apply NOTCOMP2.
          apply completion_monotonic with (t0 := job_arrival j2 + task_period (job_task j2));
            try (by done).
          by apply leq_trans with (n := job_arrival j1).
        }
      Qed.
      
      (* Also, there can be at most one pending job of tsk at time t. *)
      Lemma platform_fp_no_multiple_jobs_of_tsk :
        forall j',
          arrives_in arr_seq j' ->
          pending job_arrival job_cost sched j' t ->
          job_task j' = tsk ->
          j' = j.
      Proof.
        unfold sporadic_task_model in *.
        rename H_sporadic_tasks into SPO,
               H_valid_task into PARAMS,
               H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_all_previous_jobs_completed into PREV,
               H_j_backlogged into BACK, H_job_of_tsk into JOBtsk.
        intros j' ARR' PENDING' SAMEtsk.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF.
        move: BACK PENDING' => /andP [/andP [ARRIVED /negP NOTCOMP] NOTSCHED]
                               /andP [ARRIVED' /negP NOTCOMP'].
        destruct (leqP (job_arrival j') (job_arrival j)) as [BEFORE | BEFORE'].
        {
          exploit (SPO j' j DIFF ARR' H_j_arrives); [by rewrite JOBtsk | by done | intro SPO'].
          apply NOTCOMP'.
          apply completion_monotonic with (t0 := job_arrival j' + task_period tsk); try (by done);
            first by apply leq_trans with (n := job_arrival j); [by rewrite -SAMEtsk | by done].
          {
            apply PREVtsk; try (by done).
            apply leq_trans with (n := job_arrival j' + task_period tsk); last by rewrite -SAMEtsk.
            rewrite -addn1; apply leq_add; first by done.
            by unfold is_valid_sporadic_task in *; des.
          }
        }
        {
          unfold has_arrived in *.
          rewrite leqNgt in ARRIVED'; move: ARRIVED' => /negP BUG; apply BUG.
          apply leq_trans with (n := job_arrival j + task_period tsk); first by done.
          by rewrite -JOBtsk; apply SPO; try (by done);
            [by red; ins; subst j' | by rewrite SAMEtsk | by apply ltnW].
        }
      Qed.
      
      (* Therefore, all processors are busy with tasks other than tsk. *)
      Lemma platform_fp_cpus_busy_with_interfering_tasks :      
        count (scheduled_task_with_higher_eq_priority tsk) ts = num_cpus.
      Proof.
        have UNIQ := platform_fp_no_multiple_jobs_of_interfering_tasks.
        have UNIQ' := platform_fp_no_multiple_jobs_of_tsk. 
        rename H_all_jobs_from_taskset into FROMTS, H_sequential_jobs into SEQUENTIAL,
               H_work_conserving into WORK, H_respects_JLDP_policy into PRIO,
               H_j_backlogged into BACK, H_job_of_tsk into JOBtsk,
               H_sporadic_tasks into SPO, H_valid_job_parameters into JOBPARAMS,
               H_valid_task into TASKPARAMS, H_all_previous_jobs_completed into PREV,
               H_completed_jobs_dont_execute into COMP, H_jobs_come_from_arrival_sequence into FROMarr,
               H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_jobs_must_arrive_to_execute into ARRIVE.
        apply work_conserving_eq_work_conserving_count in WORK.
        unfold valid_sporadic_job, valid_realtime_job,
               respects_FP_policy, respects_JLDP_policy, FP_to_JLDP,
               completed_jobs_dont_execute, sequential_jobs,
               sporadic_task_model, is_valid_sporadic_task,
               jobs_of_same_task_dont_execute_in_parallel,
               is_hp_task in *.
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        {
          apply leq_trans with (n := count (fun x => task_is_scheduled job_task sched x t) ts);
            first by apply sub_count; red; move => x /andP [SCHED _].
          unfold task_is_scheduled.
          apply count_exists; first by destruct ts.
          {
            intros cpu x1 x2 SCHED1 SCHED2.
            unfold task_scheduled_on in *.
            destruct (sched cpu t); last by done.
            move: SCHED1 SCHED2 => /eqP SCHED1 /eqP SCHED2.
            by rewrite -SCHED1 -SCHED2.
          }
        }
        {
          rewrite -(WORK j t) // -count_predT.
          apply leq_trans with (n := count (fun j =>
            scheduled_task_with_higher_eq_priority tsk (job_task j)) (jobs_scheduled_at sched t));
            last first.
          {
            rewrite -count_map.
            apply leq_trans with (n := count predT [seq x <- (map (fun j => job_task j) (jobs_scheduled_at sched t)) | scheduled_task_with_higher_eq_priority tsk x]);
              first  by rewrite count_filter; apply sub_count; red; ins.
            apply leq_trans with (n := count predT [seq x <- ts | scheduled_task_with_higher_eq_priority tsk x]);
              last by rewrite count_predT size_filter.
            apply count_sub_uniqr; last first.
            {
              red; intros tsk' IN'.
              rewrite mem_filter in IN'; move: IN' => /andP [SCHED IN'].
              rewrite mem_filter; apply/andP; split; first by done.
              move: IN' => /mapP [j' IN'] ->; apply FROMTS.
              by rewrite mem_scheduled_jobs_eq_scheduled in IN'; eauto 2.
            }
            {
              rewrite filter_map.
              rewrite map_inj_in_uniq; first by apply filter_uniq, scheduled_jobs_uniq.
              red; intros j1 j2 SCHED1 SCHED2 SAMEtsk.
              rewrite 2!mem_filter in SCHED1 SCHED2.
              move: SCHED1 SCHED2 => /andP [/andP [_ HP1] SCHED1] /andP [/andP [_ HP2] SCHED2].
              rewrite 2!mem_scheduled_jobs_eq_scheduled in SCHED1 SCHED2.
              have ARRin1: arrives_in arr_seq j1 by apply (FROMarr j1 t).
              have ARRIn2: arrives_in arr_seq j2 by apply (FROMarr j2 t).
              by apply UNIQ; try (by done); apply scheduled_implies_pending.
            }
          }
          {
            apply sub_in_count; intros j' SCHED' _.
            rewrite mem_scheduled_jobs_eq_scheduled in SCHED'.
            apply/andP; split.
            {
              move: SCHED' => /existsP [cpu /eqP SCHED'].
              by apply/existsP; exists cpu; rewrite /task_scheduled_on SCHED' eq_refl.
            }
            apply/andP; split; first by rewrite -JOBtsk; apply PRIO with (t := t).
            {
              apply/eqP; red; intro SAMEtsk.
              generalize SCHED'; intro PENDING'.
              have ARRin': arrives_in arr_seq j' by apply (FROMarr j' t).
              apply scheduled_implies_pending with (job_arrival0 := job_arrival)
                (job_cost0 := job_cost) in PENDING'; try (by done).
              specialize (UNIQ' j' ARRin' PENDING' SAMEtsk); subst j'.
              by move: BACK => /andP [_ NOTSCHED]; rewrite SCHED' in NOTSCHED.
            }
          }
        }
      Qed.
      
    End NoMultipleJobsFP.
    
  End Lemmas.

End ConstrainedDeadlines.