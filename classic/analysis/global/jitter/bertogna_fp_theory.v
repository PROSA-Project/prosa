Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.workload prosa.classic.model.schedule.global.response_time
               prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.jitter.job prosa.classic.model.schedule.global.jitter.interference
               prosa.classic.model.schedule.global.jitter.schedule prosa.classic.model.schedule.global.jitter.platform
               prosa.classic.model.schedule.global.jitter.constrained_deadlines.
Require Import prosa.classic.analysis.global.jitter.workload_bound
               prosa.classic.analysis.global.jitter.interference_bound_fp.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export JobWithJitter SporadicTaskset ScheduleOfSporadicTaskWithJitter
         Workload Interference Platform ConstrainedDeadlines Schedulability
         ResponseTime Priority TaskArrival WorkloadBoundJitter
         Interference InterferenceBoundFP.
    
  (* In this section, we prove that any fixed point in Bertogna and
     Cirinei's RTA for FP scheduling modified to account for jitter
     yields a safe response-time bound. This is an extension of the
     analysis found in Chapter 18.2 of Baruah et al.'s book
     Multiprocessor Scheduling for Real-time Systems. *)
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    Variable task_jitter: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> time.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                       job_deadline job_task job_jitter j.

    (* Assume that we have a task set where all tasks have valid
       parameters and constrained deadlines, ... *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_constrained_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    (* ... and that all jobs in the arrival sequence come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j,
        arrives_in arr_seq j -> job_task j \in ts.

    (* Next, consider any schedule of this arrival sequence such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ...jobs are sequential, do not execute before the jitter
       has passed and nor longer than their execution costs. *)
    Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_jobs_execute_after_jitter:
      jobs_execute_after_jitter job_arrival job_jitter sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Assume that there exists at least one processor. *)
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Consider a given FP policy, ... *)
    Variable higher_eq_priority: FP_policy sporadic_task.

    (* ...and assume that the schedule is work-conserving and respects this policy. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost job_jitter arr_seq sched.
    Hypothesis H_respects_priority:
      respects_FP_policy job_arrival job_cost job_task job_jitter arr_seq sched higher_eq_priority.

    (* Let's define some local names to avoid passing many parameters. *)
    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.

    (* Next, we consider the response-time recurrence.
       Let tsk be a task in ts that is to be analyzed. *)
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    (* Let is_hp_task denote whether a task is a higher-priority task
       (with respect to tsk). *)
    Let is_hp_task := higher_priority_task higher_eq_priority tsk.

    (* Assume a response-time bound is known... *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    Hypothesis H_response_time_of_interfering_tasks_is_known:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        response_time_bounded_by hp_tsk (task_jitter hp_tsk + R).
    
    (* ... for every higher-priority task. *)
    Hypothesis H_hp_bounds_has_interfering_tasks:
      forall hp_tsk,
        hp_tsk \in ts ->
        is_hp_task hp_tsk ->
        exists R,
          (hp_tsk, R) \in hp_bounds.

    (* Assume that the response-time bounds are larger than task costs. *)
    Hypothesis H_response_time_bounds_ge_cost:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds -> R >= task_cost hp_tsk.
    
    (* Assume that no deadline is missed by any higher-priority task. *)
    Hypothesis H_interfering_tasks_miss_no_deadlines:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        task_jitter hp_tsk + R <= task_deadline hp_tsk.
    
    (* Let R be the fixed point of Bertogna and Cirinei's recurrence, ...*)
    Variable R: time.
    Hypothesis H_response_time_recurrence_holds :
      R = task_cost tsk +
          div_floor
            (total_interference_bound_fp task_cost task_period task_jitter
                                         tsk hp_bounds R)
            num_cpus.

    (* ... and assume that jitter + R is no larger than the deadline of tsk.*)
    Hypothesis H_response_time_no_larger_than_deadline:
      task_jitter tsk + R <= task_deadline tsk.

    (* In order to prove that R is a response-time bound, we first provide some lemmas. *)
    Section Lemmas.

      (* Consider any job j of tsk. *)
      Variable j: Job.
      Hypothesis H_job_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* Let t1 be the first point in time where j can actually be scheduled. *)
      Let t1 := job_arrival j + job_jitter j.

      (* Assume that job j is the first job of tsk not to complete by the response time bound. *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (t1 + R).
      Hypothesis H_previous_jobs_of_tsk_completed :
        forall j0,
          arrives_in arr_seq j0 ->
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + task_jitter tsk + R).
      
      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_arrival job_cost job_task job_jitter sched j tsk_other t1 (t1 + R).

      (* ...and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_arrival job_cost job_jitter sched j t1 (t1 + R).

      (* Recall Bertogna and Cirinei's workload bound. *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W_jitter task_cost task_period task_jitter tsk_other R_other R.

      (* Let hp_tasks denote the set of higher-priority tasks. *)
      Let hp_tasks := [seq tsk_other <- ts | is_hp_task tsk_other].

      (* Now we establish results the higher-priority tasks. *)
      Section LemmasAboutHPTasks.
        
        (* Let (tsk_other, R_other) be any pair of higher-priority task and
           response-time bound computed in previous iterations. *)
        Variable tsk_other: sporadic_task.
        Variable R_other: time.
        Hypothesis H_response_time_of_tsk_other: (tsk_other, R_other) \in hp_bounds.

        (* Since tsk_other cannot interfere more than it executes, we show that
           the interference caused by tsk_other is no larger than workload bound W. *)
        Lemma bertogna_fp_workload_bounds_interference :
          x tsk_other <= workload_bound tsk_other R_other.
        Proof.
          unfold response_time_bounded_by, is_response_time_bound_of_task,
                 completed, completed_jobs_dont_execute, valid_sporadic_job in *.
          rename H_valid_job_parameters into PARAMS,
                 H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into TASK_PARAMS,
                 H_constrained_deadlines into RESTR,
                 H_response_time_of_interfering_tasks_is_known into RESP,
                 H_interfering_tasks_miss_no_deadlines into NOMISS,
                 H_response_time_bounds_ge_cost into GE_COST.
          unfold x, workload_bound.
          destruct ([exists t: 'I_(t1 + R),
                       task_is_scheduled job_task sched tsk_other t]) eqn: SCHED;
            last first.
          {
            apply negbT in SCHED; rewrite negb_exists in SCHED.
            move: SCHED => /forallP SCHED.
            apply leq_trans with (n := 0); last by done.
            apply leq_trans with (n := \sum_(t1 <= t < t1 + R) 0);
              last by rewrite big1.
            apply leq_sum_nat; move => t /andP [_ LTt] _.
            unfold t1 in LTt.
            specialize (SCHED (Ordinal LTt)).
            rewrite negb_exists in SCHED; move: SCHED => /forallP SCHED.
            rewrite big1 //; intros cpu _.
            specialize (SCHED cpu); apply negbTE in SCHED.
            by rewrite SCHED andbF.
          }
          move: SCHED => /existsP [t /existsP [cpu SCHED]].
          unfold task_scheduled_on in SCHED.
          destruct (sched cpu t) as [j0 |] eqn:SCHED0; last by done.
          assert (INts: tsk_other \in ts).
          {
            move: SCHED => /eqP <-. apply FROMTS, (H_jobs_come_from_arrival_sequence j0 t).
            by apply/existsP; exists cpu; apply/eqP.
          }
          apply leq_trans with (n := workload job_task sched tsk_other t1 (t1 + R));
            first by apply task_interference_le_workload.
          apply workload_bounded_by_W with (task_deadline0 := task_deadline)
              (job_arrival0 := job_arrival) (arr_seq0 := arr_seq)
              (job_jitter0 := job_jitter) (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by ins); last 2 first;
              [ by apply NOMISS
              | by ins; rewrite -addnA; apply RESP
              | by ins; apply TASK_PARAMS
              | by ins; apply RESTR
              | by ins; apply GE_COST]. 
        Qed.

      End LemmasAboutHPTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.

        (* 0) Since job j did not complete by its response time bound, it follows that
              the total interference X >= R - e_k + 1. *)
        Lemma bertogna_fp_too_much_interference : X >= R - task_cost tsk + 1.
        Proof.
          rename H_completed_jobs_dont_execute into COMP,
                 H_valid_job_parameters into PARAMS,
                 H_response_time_recurrence_holds into REC,
                 H_job_of_tsk into JOBtsk, H_j_not_completed into NOTCOMP.
          unfold completed, valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          unfold X, total_interference; rewrite addn1.
          rewrite -(ltn_add2r (task_cost tsk)).
          rewrite subh1; last by rewrite [R](REC) // leq_addr.
          rewrite -addnBA // subnn addn0.
          move: (NOTCOMP) => /negP NOTCOMP'.
          rewrite -ltnNge in NOTCOMP.

          apply leq_ltn_trans with (n := (\sum_(t1 <= t < t1 + R)
                                       backlogged job_arrival job_cost job_jitter sched j t) +
                                     service sched j (t1 + R)); last first.
          {
            rewrite -addn1 -addnA leq_add2l addn1.
            apply leq_trans with (n := job_cost j); first by done.
            by specialize (PARAMS j H_job_arrives); des; rewrite -JOBtsk.
          }
          unfold service.
          rewrite -> big_cat_nat with (n := t1) (m := 0); rewrite ?leq_addr // /=.
          rewrite (cumulative_service_before_jitter_zero job_arrival job_jitter) // add0n.
          rewrite -big_split /=.
          apply leq_trans with (n := \sum_(t1 <= i < t1 + R) 1);
            first by simpl_sum_const; rewrite addKn.
          apply leq_sum_nat; move => i /andP [GEi LTi] _.
          destruct (backlogged job_arrival job_cost job_jitter sched j i) eqn:BACK;
            first by rewrite -addn1 addnC; apply leq_add.
          apply negbT in BACK.
          rewrite add0n lt0n -not_scheduled_no_service negbK.
          rewrite /backlogged negb_and negbK in BACK.
          move: BACK => /orP [/negP NOTPENDING | SCHED]; last by done.
          exfalso; apply NOTPENDING; unfold pending; apply/andP; split; first by done.
          apply/negP; red; intro BUG; apply NOTCOMP'.
          by apply completion_monotonic with (t := i); try (by done); apply ltnW.
        Qed.

        (* 1) Next, we prove that during the scheduling window of j, any job that is
              scheduled while j is backlogged comes from a different task.
              This follows from the fact that j is the first job not to complete
              by its response-time bound, so previous jobs of j's task must have
              completed by their periods and cannot be pending. *)
        Lemma bertogna_fp_interference_by_different_tasks :
          forall t j_other,
            t1 <= t < t1 + R ->
            arrives_in arr_seq j_other ->
            backlogged job_arrival job_cost job_jitter sched j t ->
            scheduled sched j_other t ->
            job_task j_other != tsk.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_job_parameters into JOBPARAMS, H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK,
                 H_constrained_deadlines into CONSTR,
                 H_previous_jobs_of_tsk_completed into PREV,
                 H_response_time_no_larger_than_deadline into NOMISS.
          unfold valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          move => t j_other /andP [LEt GEt] ARRother BACK SCHED.
          apply/eqP; red; intro SAMEtsk.
          move: SCHED => /existsP [cpu SCHED].
          have SCHED': scheduled sched j_other t by apply/existsP; exists cpu.
          clear SCHED; rename SCHED' into SCHED.
          move: (SCHED) => PENDING.
          apply scheduled_implies_pending with (job_arrival0 := job_arrival)
                (job_cost0 := job_cost) (job_jitter0 := job_jitter) in PENDING; try (by done).
          destruct (ltnP (job_arrival j_other) (job_arrival j)) as [BEFOREother | BEFOREj].
          {
            move: (BEFOREother) => LT; rewrite -(ltn_add2r R) in LT.
            specialize (PREV j_other ARRother SAMEtsk BEFOREother).
            move: PENDING => /andP [_ /negP NOTCOMP]; apply NOTCOMP.
            apply completion_monotonic with (t0 := job_arrival j_other + task_jitter tsk + R);
              try by done.
            apply leq_trans with (n := job_arrival j);
              last by apply leq_trans with (n := t1); [by apply leq_addr | by done].
            apply leq_trans with (n := job_arrival j_other + task_period tsk).
            {
              rewrite -addnA leq_add2l.
              by apply leq_trans with (n := task_deadline tsk);
                [by apply NOMISS | by apply CONSTR; rewrite -JOBtsk FROMTS].
            }
            rewrite -SAMEtsk; apply SPO; [ | by done | by done | by rewrite JOBtsk | by apply ltnW].
            by red; intro EQ; subst j_other; rewrite ltnn in BEFOREother.
          }
          {
            move: PENDING => /andP [ARRIVED _].
            exploit (SPO j j_other); try (by done); [ | by rewrite SAMEtsk | ]; last first.
            {
              apply/negP; rewrite -ltnNge JOBtsk.
              apply leq_trans with (n := job_arrival j + task_deadline tsk);
                last by rewrite leq_add2l; apply CONSTR; rewrite -JOBtsk FROMTS.
              apply leq_trans with (n := job_arrival j + task_jitter tsk + R);
                last by rewrite -addnA leq_add2l; apply NOMISS.
              apply leq_trans with (n := t1 + R); last first.
              {
                rewrite leq_add2r leq_add2l -JOBtsk.
                by specialize (JOBPARAMS j H_job_arrives); des.
              }
              apply leq_ltn_trans with (n := job_arrival j_other + job_jitter j_other);
                first by apply leq_addr.
              by apply leq_ltn_trans with (n := t).
            }
            by intros EQtsk; subst j_other; rewrite /backlogged SCHED andbF in BACK.
          }
        Qed.

        (* Let's define a predicate to identify the other tasks that are scheduled. *)
        Let other_scheduled_task (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          is_hp_task tsk_other.
      
        (* 2) Now we prove that, at all times that j is backlogged, the number
              of tasks other than tsk that are scheduled is exactly the number
              of processors in the system. This is required to prove lemma (3). *)
        Lemma bertogna_fp_all_cpus_are_busy:
          forall t,
            t1 <= t < t1 + R ->
            backlogged job_arrival job_cost job_jitter sched j t ->
            count (other_scheduled_task t) ts = num_cpus.
        Proof.
          rename H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_all_jobs_from_taskset into FROMTS,
                 H_sporadic_tasks into SPO,
                 H_valid_job_parameters into JOBPARAMS,
                 H_constrained_deadlines into RESTR,
                 H_hp_bounds_has_interfering_tasks into HAS,
                 H_interfering_tasks_miss_no_deadlines into NOMISS,
                 H_response_time_of_interfering_tasks_is_known into PREV,
                 H_previous_jobs_of_tsk_completed into PREVtsk.
          unfold sporadic_task_model, is_response_time_bound_of_task,
                 valid_sporadic_job_with_jitter in *.
          move => t /andP [LEt LTt] BACK.

          apply platform_fp_cpus_busy_with_interfering_tasks with (task_cost0 := task_cost)
          (task_period0 := task_period) (task_deadline0 := task_deadline) (job_task0 := job_task)
          (ts0 := ts) (tsk0 := tsk) (higher_eq_priority0 := higher_eq_priority) (arr_seq0 := arr_seq)
            in BACK; try (by done); first by apply PARAMS; rewrite -JOBtsk FROMTS.
          {
            apply leq_trans with (n := job_arrival j + job_jitter j + R); first by done.
            rewrite -addnA leq_add2l.
            apply leq_trans with (n := task_deadline tsk); last by apply RESTR.
            apply leq_trans with (n := task_jitter tsk + R); last by done.
            by rewrite leq_add2r -JOBtsk; specialize (JOBPARAMS j H_job_arrives); des.
          }
          {
            intros j_other tsk_other ARRother JOBother INTERF.
            feed (HAS tsk_other); first by rewrite -JOBother FROMTS.
            move: (HAS INTERF) => [R' IN].
            apply completion_monotonic with (t0 := job_arrival j_other + task_jitter tsk_other + R');
              try (by done); last by rewrite -addnA; apply PREV.
            rewrite -addnA leq_add2l; apply leq_trans with (n := task_deadline tsk_other);
              [by apply NOMISS | by apply RESTR; rewrite -JOBother; apply FROMTS].
          }
          {
            ins; apply completion_monotonic with (t0 := job_arrival j0 + task_jitter tsk + R);
              try (by done); last by apply PREVtsk.
            rewrite -addnA leq_add2l.
            by apply leq_trans with (n := task_deadline tsk); [by done | by apply RESTR].
          }
        Qed.

        (* 3) Now we prove that, at all times that j is backlogged, the number
              of tasks other than tsk that are scheduled is exactly the number
              of processors in the system. This is required to prove lemma (4). *)
        Lemma bertogna_fp_interference_on_all_cpus:
          \sum_(tsk_k <- hp_tasks) x tsk_k = X * num_cpus.
        Proof.
          have DIFFTASK := bertogna_fp_interference_by_different_tasks.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS, H_jobs_come_from_arrival_sequence into SEQ,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK, H_constrained_deadlines into CONSTR,
                 H_previous_jobs_of_tsk_completed into PREV,
                 H_respects_priority into FP, H_response_time_no_larger_than_deadline into NOMISS.
          unfold sporadic_task_model in *.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /= mul1n.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _ _ _) _]big_mkcond.
          apply eq_big_nat; move => t /andP [GEt LTt].
          destruct (backlogged job_arrival job_cost job_jitter sched j t) eqn:BACK;
            last by rewrite big1 //; ins; rewrite big1.
          rewrite big_mkcond /=.
          rewrite exchange_big /=.
          apply eq_trans with (y := \sum_(cpu < num_cpus) 1); last by simpl_sum_const.
          apply eq_bigr; intros cpu _.
          move: (WORK j t H_job_arrives BACK cpu) => [j_other /eqP SCHED]; unfold scheduled_on in *.
          rewrite (bigD1_seq (job_task j_other)) /=; last by rewrite filter_uniq; destruct ts.
          {
            rewrite (eq_bigr (fun i => 0));
              last by intros i DIFF; rewrite /task_scheduled_on SCHED;apply/eqP;rewrite eqb0 eq_sym.
            simpl_sum_const; apply/eqP; rewrite eqb1.
            by unfold task_scheduled_on; rewrite SCHED.
          }
          have ARRother: arrives_in arr_seq j_other.
            by apply (SEQ j_other t); apply/existsP; exists cpu; apply/eqP.
          rewrite mem_filter; apply/andP; split; last by apply FROMTS.
          unfold is_hp_task, higher_priority_task; apply/andP; split.
          {
            rewrite -JOBtsk; apply FP with (t := t); try by done.
            by apply/existsP; exists cpu; apply/eqP.
          }
          apply DIFFTASK with (t := t); [by auto | by done | by done |].
          by apply/existsP; exists cpu; apply/eqP.
        Qed.

        (* Before stating the next lemma, let (num_tasks_exceeding delta) be the
           number of interfering tasks whose interference x is larger than delta. *)
        Let num_tasks_exceeding delta := count (fun i => x i >= delta) (hp_tasks).

        (* 4) Now we prove that, for any delta, if (num_task_exceeding delta > 0), then the
              cumulative interference caused by the complementary set of interfering tasks fills
              the remaining, not-completely-full (num_cpus - num_tasks_exceeding delta)
              processors. *)
        Lemma bertogna_fp_interference_in_non_full_processors :
          forall delta,
            0 < num_tasks_exceeding delta < num_cpus ->
            \sum_(i <- hp_tasks | x i < delta) x i >= delta * (num_cpus - num_tasks_exceeding delta).
        Proof.
          have INV := bertogna_fp_all_cpus_are_busy.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS, H_valid_job_parameters into JOBPARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_previous_jobs_of_tsk_completed into BEFOREok,
                 H_response_time_no_larger_than_deadline into NOMISS,
                 H_constrained_deadlines into CONSTR,
                 H_sequential_jobs into SEQ, H_jobs_come_from_arrival_sequence into FROMSEQ,
                 H_respects_priority into FP, H_hp_bounds_has_interfering_tasks into HASHP,
                 H_interfering_tasks_miss_no_deadlines into NOMISSHP.
          unfold sporadic_task_model, valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          move => delta /andP [HAS LT]. 
          rewrite -has_count in HAS.

          set some_interference_A := fun t =>
            has (fun tsk_k => backlogged job_arrival job_cost job_jitter sched j t &&
                              (x tsk_k >= delta) &&
                              task_is_scheduled job_task sched tsk_k t) hp_tasks.
          set total_interference_B := fun t =>
              backlogged job_arrival job_cost job_jitter sched j t *
              count (fun tsk_k => (x tsk_k < delta) &&
                    task_is_scheduled job_task sched tsk_k t) hp_tasks.

          apply leq_trans with ((\sum_(t1 <= t < t1 + R)
                                some_interference_A t) * (num_cpus - num_tasks_exceeding delta)).
          {
            rewrite leq_mul2r; apply/orP; right.
            move: HAS => /hasP HAS; destruct HAS as [tsk_a INa LEa].
            apply leq_trans with (n := x tsk_a); first by apply LEa.
            unfold x, task_interference, some_interference_A.
            apply leq_sum_nat; move => t /andP [GEt LTt] _.
            destruct (backlogged job_arrival job_cost job_jitter sched j t) eqn:BACK;
              last by rewrite (eq_bigr (fun x => 0)); [by simpl_sum_const | by ins].
            destruct ([exists cpu, task_scheduled_on job_task sched tsk_a cpu t]) eqn:SCHED;
              last first.
            {
              apply negbT in SCHED; rewrite negb_exists in SCHED; move: SCHED => /forallP ALL.
              rewrite (eq_bigr (fun x => 0)); first by simpl_sum_const.
              by intros cpu _; specialize (ALL cpu); apply negbTE in ALL; rewrite ALL.
            }
            move: SCHED => /existsP [cpu SCHED].
            apply leq_trans with (n := 1); last first.
            {
              rewrite lt0b; apply/hasP; exists tsk_a; first by done.
              by rewrite LEa 2!andTb; apply/existsP; exists cpu.
            }
            rewrite (bigD1 cpu) /= // SCHED.
            rewrite (eq_bigr (fun x => 0)); first by simpl_sum_const; rewrite leq_b1.
            intros cpu' DIFF.
            apply/eqP; rewrite eqb0; apply/negP.
            intros SCHED'. 
            move: DIFF => /negP DIFF; apply DIFF; apply/eqP.
            unfold task_scheduled_on in *.
            destruct (sched cpu t) as [j1|] eqn:SCHED1; last by done.
            destruct (sched cpu' t) as [j2|] eqn:SCHED2; last by done.
            move: SCHED SCHED' => /eqP JOB /eqP JOB'.
            subst tsk_a; symmetry in JOB'.
            have ARR1: arrives_in arr_seq j1.
              by apply (FROMSEQ j1 t); apply/existsP; exists cpu; apply/eqP. 
            have ARR2: arrives_in arr_seq j2.
              by apply (FROMSEQ j2 t); apply/existsP; exists cpu'; apply/eqP. 
            assert (PENDING1: pending job_arrival job_cost job_jitter sched j1 t).
            {
              apply scheduled_implies_pending; try by done.
              by apply/existsP; exists cpu; apply/eqP.
            }
            assert (PENDING2: pending job_arrival job_cost job_jitter sched j2 t).
            {
              apply scheduled_implies_pending; try by done.
              by apply/existsP; exists cpu'; apply/eqP.
            }
            assert (BUG: j1 = j2).
            {
              destruct (job_task j1 == tsk) eqn:SAMEtsk.
              {
                move: SAMEtsk => /eqP SAMEtsk.
                move: (PENDING1) => SAMEjob. 
                apply platform_fp_no_multiple_jobs_of_tsk with (task_cost0 := task_cost)
                  (task_period0 := task_period) (task_deadline0 := task_deadline) (arr_seq0 := arr_seq)
                  (job_task0 := job_task) (tsk0 := tsk) (j0 := j) in SAMEjob; try (by done);
                  [ | by apply PARAMS | |]; last 2 first.
                {
                  apply (leq_trans LTt); rewrite -addnA leq_add2l.
                  apply leq_trans with (n := task_deadline tsk); last by apply CONSTR.
                  apply leq_trans with (n := task_jitter tsk + R); last by apply NOMISS.
                  by rewrite leq_add2r -JOBtsk; specialize (JOBPARAMS j H_job_arrives); des.
                }
                {
                  intros j0 ARR0 JOB0 LT0.
                  apply completion_monotonic with (t0 := job_arrival j0 + task_jitter tsk + R);
                    try (by done); last by apply BEFOREok.
                  rewrite -addnA leq_add2l.
                  by apply leq_trans with (n := task_deadline tsk); last by apply CONSTR.
                }
                move: BACK => /andP [_ /negP NOTSCHED]; exfalso; apply NOTSCHED.
                by rewrite -SAMEjob; apply/existsP; exists cpu; apply/eqP.
              }
              {
                assert (INTERF: is_hp_task (job_task j1)).
                {
                  apply/andP; split; last by rewrite SAMEtsk.
                  rewrite -JOBtsk; apply FP with (t := t); try (by done).
                  by apply/existsP; exists cpu; apply/eqP.
                }
                apply platform_fp_no_multiple_jobs_of_interfering_tasks with
                 (task_period0 := task_period) (tsk0 := tsk) (job_arrival0 := job_arrival)
                 (higher_eq_priority0 := higher_eq_priority) (job_jitter0 := job_jitter)
                 (arr_seq0 := arr_seq)
                 (job_cost0 := job_cost) (job_task0 := job_task) (sched0 := sched) (t0 := t);
                  rewrite ?JOBtsk ?SAMEtsk //.
                {
                  intros j0 tsk0 ARR0 JOB0 INTERF0.
                  feed (HASHP tsk0); first by rewrite -JOB0 FROMTS.
                  move: (HASHP INTERF0) => [R0 IN0].
                  apply completion_monotonic with (t0 := job_arrival j0 + task_jitter tsk0 + R0);
                    try (by done).
                  {
                    rewrite -addnA leq_add2l.
                    by apply leq_trans with (n := task_deadline tsk0);
                      [by apply NOMISSHP | by apply CONSTR; rewrite -JOB0 FROMTS].
                  }
                  rewrite -addnA.
                  by eapply H_response_time_of_interfering_tasks_is_known; first by apply IN0.
                }
              }
            }
            by subst j2; apply SEQ with (j := j1) (t := t).
          }

          apply leq_trans with (\sum_(t1 <= t < t1 + R)
                                     total_interference_B t).
          {
            rewrite big_distrl /=.
            apply leq_sum_nat; move => t LEt _.
            unfold some_interference_A, total_interference_B. 
            destruct (backlogged job_arrival job_cost job_jitter sched j t) eqn:BACK;
              [rewrite mul1n /= | by rewrite has_pred0 //].

            destruct (has (fun tsk_k : sporadic_task => (delta <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) hp_tasks) eqn:HAS';
              last by done.
            rewrite mul1n; move: HAS => /hasP [tsk_k INk LEk].
            unfold num_tasks_exceeding.
            apply leq_trans with (n := num_cpus -
                         count (fun i => (x i >= delta) &&
                            task_is_scheduled job_task sched i t) hp_tasks).
            {
              apply leq_sub2l.
              rewrite -2!sum1_count big_mkcond /=.
              rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
              apply leq_sum; intros i _.
              by destruct (task_is_scheduled job_task sched i t);
                [by rewrite andbT | by rewrite andbF].
            }
            rewrite -count_filter -[count _ hp_tasks]count_filter.
            eapply leq_trans with (n := count (predC (fun tsk => delta <= x tsk)) _);
              last by apply eq_leq, eq_in_count; red; ins; rewrite ltnNge.
            rewrite leq_subLR count_predC size_filter.
            by apply leq_trans with (n := count (other_scheduled_task t) ts);
              [by rewrite INV | by rewrite count_filter].            
          }
          {
            unfold x at 2, total_interference_B.
            rewrite exchange_big /=; apply leq_sum; intros t _.
            destruct (backlogged job_arrival job_cost job_jitter sched j t) eqn:BACK; last by ins.
            rewrite mul1n -sum1_count.
            rewrite big_mkcond [\sum_(i <- hp_tasks | _ < _) _]big_mkcond /=.
            apply leq_sum_seq; move => tsk_k IN _.
            destruct (x tsk_k < delta); [rewrite andTb | by rewrite andFb].
            destruct (task_is_scheduled job_task sched tsk_k t) eqn:SCHED; last by done.
            move: SCHED => /existsP [cpu SCHED].
            by rewrite (bigD1 cpu) /= // SCHED.
          }
        Qed.

        (* 5) Based on lemma (4), we prove that, for any interval delta, if the sum of per-task
              interference exceeds (delta * num_cpus), the same applies for the
              sum of the minimum of the interference and delta. *)
        Lemma bertogna_fp_minimum_exceeds_interference :
          forall delta,
            \sum_(tsk_k <- hp_tasks) x tsk_k >= delta * num_cpus ->
               \sum_(tsk_k <- hp_tasks) minn (x tsk_k) delta >=
               delta * num_cpus.
        Proof.
          intros delta SUMLESS.
          set more_interf := fun tsk_k => x tsk_k >= delta.
          rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
          unfold more_interf, minn.
          rewrite [\sum_(_ <- _ | delta <= _)_](eq_bigr (fun i => delta));
            last by intros i COND; rewrite leqNgt in COND; destruct (delta > x i).
          rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < delta)
                                                (fun i => x i));
            [| by red; ins; rewrite ltnNge
             | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

          (* Case 1: num_tasks_exceeding = 0 *)
          destruct (~~ has (fun i => delta <= x i) hp_tasks) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in hp_tasks) && true));
              last by red; intros tsk_k; destruct (tsk_k \in hp_tasks) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond.
          } apply negbFE in HASa.

          (* Case 2: num_tasks_exceeding >= num_cpus *)
          destruct (num_tasks_exceeding delta >= num_cpus) eqn:CARD.
          {
            apply leq_trans with (delta * num_tasks_exceeding delta);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold num_tasks_exceeding; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          (* Case 3: num_tasks_exceeding < num_cpus *)
          rewrite big_const_seq iter_addn addn0; fold num_tasks_exceeding.
          apply leq_trans with (n := delta * num_tasks_exceeding delta +
                                     delta * (num_cpus - num_tasks_exceeding delta));
            first by rewrite -mulnDr subnKC //; apply ltnW.
          rewrite leq_add2l; apply bertogna_fp_interference_in_non_full_processors.
          by apply/andP; split; first by rewrite -has_count.
        Qed.

        (* 6) Next, using lemmas (0), (3) and (5) we prove that the reduction-based
              interference bound is not enough to cover the sum of the minima over all tasks
              (artifact of the proof by contradiction). *)
        Lemma bertogna_fp_sum_exceeds_total_interference:
          \sum_((tsk_k, R_k) <- hp_bounds)
            minn (x tsk_k) (R - task_cost tsk + 1) >
          total_interference_bound_fp task_cost task_period task_jitter tsk hp_bounds R.
        Proof.
          have EXCEEDS := bertogna_fp_minimum_exceeds_interference.
          have ALLBUSY := bertogna_fp_interference_on_all_cpus.
          have TOOMUCH := bertogna_fp_too_much_interference.
          rename H_hp_bounds_has_interfering_tasks into HAS,
                 H_response_time_recurrence_holds into REC.
          apply leq_trans with (n := \sum_(tsk_k <- hp_tasks) minn (x tsk_k) (R - task_cost tsk + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
              last by ins; destruct i.
            have MAP := @big_map _ 0 addn _ _ (fun x => fst x) hp_bounds (fun x => true) (fun y => minn (x y) (R - task_cost tsk + 1)).
            rewrite -MAP.
            apply leq_sum_sub_uniq; first by apply filter_uniq; destruct ts.
            red; move => tsk0 IN0.
            rewrite mem_filter in IN0; move: IN0 => /andP [INTERF0 IN0].
            apply/mapP.
            feed (HAS tsk0); first by done.
            move: (HAS INTERF0) => [R0 IN].
            by exists (tsk0, R0).
          }
          apply ltn_div_trunc with (d := num_cpus);
            first by apply H_at_least_one_cpu.
          unfold div_floor in REC. 
          rewrite -(ltn_add2l (task_cost tsk)) -REC.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by rewrite REC; apply leq_addr.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          apply EXCEEDS.
          apply leq_trans with (n := X * num_cpus); last by rewrite ALLBUSY.
          by rewrite leq_mul2r; apply/orP; right; apply TOOMUCH.
        Qed.

        (* 7) After concluding that the sum of the minima exceeds (R - e_i + 1),
              we prove that there exists a tuple (tsk_k, R_k) that satisfies
              min (x_k, R - e_i + 1) > min (W_k', R - e_i + 1).
              This implies that x_k > W_k', which is of course a contradiction,
              since W_k is a valid task interference bound. *)
        Lemma bertogna_fp_exists_task_that_exceeds_bound :
          exists tsk_k R_k,
            (tsk_k, R_k) \in hp_bounds /\
            (minn (x tsk_k) (R - task_cost tsk + 1) >
              minn (workload_bound tsk_k R_k) (R - task_cost tsk + 1)).
        Proof.
          have SUM := bertogna_fp_sum_exceeds_total_interference.
          rename H_hp_bounds_has_interfering_tasks into HASHP.
          assert (HAS: has (fun tup : task_with_response_time =>
                             let (tsk_k, R_k) := tup in
                               (minn (x tsk_k) (R - task_cost tsk + 1) >
                                minn (workload_bound tsk_k R_k)(R - task_cost tsk + 1)))
                            hp_bounds).
          {
              apply/negP; unfold not; intro NOTHAS.
              move: NOTHAS => /negP /hasPn ALL.
              rewrite -[_ < _]negbK in SUM.
              move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
              rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
                last by ins; destruct i.
              unfold total_interference_bound_fp.
              rewrite big_seq_cond.
              rewrite [\sum_(_ <- _ | true)_]big_seq_cond.
              apply leq_sum.
              intros p; rewrite andbT; intros IN.
              by specialize (ALL p IN); destruct p; rewrite leqNgt.
          }
          move: HAS => /hasP HAS; destruct HAS as [[tsk_k R_k] HPk MINk]; exists tsk_k, R_k.
          by repeat split.
        Qed.
      
      End DerivingContradiction.

    End Lemmas.
    
    (* Using the lemmas above, we prove that R' bounds the response time of task tsk. *)
    Theorem bertogna_cirinei_response_time_bound_fp :
      response_time_bounded_by tsk (task_jitter tsk + R).
    Proof.
      have EX := bertogna_fp_exists_task_that_exceeds_bound.
      have WORKLOAD := bertogna_fp_workload_bounds_interference.
      rename H_valid_job_parameters into PARAMS.
      unfold valid_sporadic_job_with_jitter, valid_sporadic_job in *.
      intros j ARRj JOBtsk.

      (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
      remember (job_arrival j + (task_jitter tsk + R)) as ctime.
      
      (* Now, we apply strong induction on the absolute response-time bound. *)
      generalize dependent j.
      induction ctime as [ctime IH] using strong_ind.

      intros j ARRj JOBtsk EQc; subst ctime.

      (* First, let's simplify the induction hypothesis. *)
      assert (BEFOREok: forall j0,
                          arrives_in arr_seq j0 ->
                          job_task j0 = tsk ->
                          job_arrival j0 < job_arrival j ->
                          completed job_cost sched j0 (job_arrival j0 + task_jitter tsk + R)).
      {
        by ins; rewrite -addnA; apply IH; try (by done); first by rewrite ltn_add2r.
      } clear IH.
      
      (* Now we start the proof. Assume by contradiction that job j
         is not complete at time (job_arrival j + job_jitter j + R'). *)
      rewrite addnA.
      apply completion_monotonic with (t := job_arrival j + job_jitter j + R).
      {
        rewrite leq_add2r leq_add2l.
        specialize (PARAMS j ARRj); des.
        by rewrite -JOBtsk; apply PARAMS0.
      }
      destruct (completed job_cost sched j (job_arrival j + job_jitter j + R)) eqn:NOTCOMP;
        first by done.
      apply negbT in NOTCOMP; exfalso.

      (* We derive a contradiction using the previous lemmas. *)
      specialize (EX j ARRj JOBtsk NOTCOMP BEFOREok).
      destruct EX as [tsk_k [R_k [HPk LTmin]]].
      unfold minn at 1 in LTmin.
      specialize (WORKLOAD j tsk_k R_k HPk).
      destruct (W_jitter task_cost task_period task_jitter tsk_k R_k R < R - task_cost tsk + 1);
        rewrite leq_min in LTmin; 
        last by move: LTmin => /andP [_ BUG]; rewrite ltnn in BUG.
      move: LTmin => /andP [BUG _]; des.
      by apply leq_trans with (p := W_jitter task_cost task_period task_jitter tsk_k R_k R) in BUG;
        first by rewrite ltnn in BUG.
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.