Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task_arrival
        prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.global.workload prosa.classic.model.schedule.global.schedulability
               prosa.classic.model.schedule.global.response_time.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform
               prosa.classic.model.schedule.global.basic.constrained_deadlines prosa.classic.model.schedule.global.basic.interference.
Require Import prosa.classic.analysis.global.parallel.workload_bound prosa.classic.analysis.global.parallel.interference_bound_fp.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference
         InterferenceBoundFP Platform Schedulability ResponseTime
         Priority TaskArrival WorkloadBound ConstrainedDeadlines.
    
  (* In this section, we prove that any fixed point in Bertogna and
     Cirinei's RTA for FP scheduling modified to consider (potentially)
     parallel jobs yields a safe response-time bound. This is an extension
     of the analysis found in Chapter 18.2 of Baruah et al.'s book
     Multiprocessor Scheduling for Real-time Systems. *)
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Assume that we have a task set where all tasks have valid
       parameters and constrained deadlines, ... *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_constrained_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    (* ... and that all jobs in the arrival sequence come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Next, consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    
    (* ...jobs do not execute before their arrival times nor longer
       than their execution costs. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Consider a given FP policy, ... *)
    Variable higher_eq_priority: FP_policy sporadic_task.
    
    (* ... and assume that the schedule is an APA work-conserving
       schedule that respects this policy. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_respects_FP_policy:
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority.
    
    (* Assume that there exists at least one processor. *)
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

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
        response_time_bounded_by hp_tsk R.
    
    (* ... for every higher-priority task. *)
    Hypothesis H_hp_bounds_has_interfering_tasks:
      forall hp_tsk,
        hp_tsk \in ts ->
        is_hp_task hp_tsk ->
          exists R, (hp_tsk, R) \in hp_bounds.

    (* Let R be the fixed point of Bertogna and Cirinei's recurrence, ...*)
    Variable R: time.
    Hypothesis H_response_time_recurrence_holds :
      R = task_cost tsk +
          div_floor
            (total_interference_bound_fp task_cost task_period hp_bounds R)
            num_cpus.

    (* ... and assume that R is no larger than the deadline of tsk.*)
    Hypothesis H_response_time_no_larger_than_deadline:
      R <= task_deadline tsk.

    (* In order to prove that R is a response-time bound, we first provide some lemmas. *)
    Section Lemmas.

      (* Consider any job j of tsk. *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* Assume that job j is the first job of tsk not to complete by the response time bound. *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (job_arrival j + R).
      Hypothesis H_previous_jobs_of_tsk_completed :
        forall j0,
          arrives_in arr_seq j0 ->
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + R).
      
      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_arrival job_cost job_task sched j
                          tsk_other (job_arrival j) (job_arrival j + R).

      (* ...and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R).

      (* Recall Bertogna and Cirinei's workload bound. *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W task_cost task_period tsk_other R_other R.

      (* Let hp_tasks denote the set of higher-priority tasks. *)
      Let hp_tasks := [seq tsk_other <- ts | is_hp_task tsk_other].

      (* Now we establish results about the higher-priority tasks. *)
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
          rename H_valid_task_parameters into TASK_PARAMS,
                 H_all_jobs_from_taskset into FROMTS,
                 H_response_time_of_interfering_tasks_is_known into RESP.
          unfold x, workload_bound.
          destruct ([exists t: 'I_(job_arrival j + R),
                       task_is_scheduled job_task sched tsk_other t]) eqn: SCHED;
            last first.
          {
            apply negbT in SCHED; rewrite negb_exists in SCHED.
            move: SCHED => /forallP SCHED.
            apply leq_trans with (n := 0); last by done.
            apply leq_trans with (n := \sum_(job_arrival j <= t < job_arrival j + R) 0);
              last by rewrite big1.
            apply leq_sum_nat; move => i /andP [_ LTi] _.
            specialize (SCHED (Ordinal LTi)).
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
            move: SCHED => /eqP <-; apply FROMTS, (H_jobs_come_from_arrival_sequence j0 t).
            by apply/existsP; exists cpu; apply/eqP.
          }
          apply leq_trans with (n := workload job_task sched tsk_other
                                              (job_arrival j) (job_arrival j + R));
            first by apply task_interference_le_workload.
          by apply workload_bounded_by_W with (task_deadline0 := task_deadline) (arr_seq0 := arr_seq)
              (job_arrival0 := job_arrival)  (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by ins);
              [ by ins; apply TASK_PARAMS
              | by ins; apply RESP with (hp_tsk := tsk_other)].
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
                 H_job_of_tsk into JOBtsk,
                 H_j_not_completed into NOTCOMP.
          unfold completed, valid_sporadic_job in *.
          unfold X, total_interference; rewrite addn1.
          rewrite -(ltn_add2r (task_cost tsk)).
          rewrite subh1; last by rewrite REC leq_addr.
          rewrite -addnBA // subnn addn0.
          move: (NOTCOMP) => /negP NOTCOMP'.
          rewrite -ltnNge in NOTCOMP.
          apply leq_ltn_trans with (n := (\sum_(job_arrival j <= t < job_arrival j + R)
                                       backlogged job_arrival job_cost sched j t) +
                                     service sched j (job_arrival j + R)); last first.
          {
            rewrite -addn1 -addnA leq_add2l addn1.
            apply leq_trans with (n := job_cost j); first by done.
            by specialize (PARAMS j H_j_arrives); des; rewrite -JOBtsk.
          }
          unfold service; rewrite service_before_arrival_eq_service_during //.
          rewrite -big_split /=.
          apply leq_trans with (n := \sum_(job_arrival j <= i < job_arrival j + R) 1);
            first by rewrite big_const_nat iter_addn mul1n addn0 addKn.
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true) _]big_nat_cond.
          apply leq_sum; move => i /andP [/andP [GEi LTi] _].
          destruct (backlogged job_arrival job_cost sched j i) eqn:BACK;
            first by rewrite -addn1 addnC; apply leq_add.
          apply negbT in BACK.
          rewrite add0n lt0n -not_scheduled_no_service negbK.
          rewrite /backlogged negb_and negbK in BACK.
          move: BACK => /orP [/negP NOTPENDING | SCHED]; last by done.
          exfalso; apply NOTPENDING; unfold pending; apply/andP; split; first by done.
          apply/negP; red; intro BUG; apply NOTCOMP'.
          by apply completion_monotonic with (t := i); try (by done); apply ltnW.
        Qed.

        (* Let's define a predicate to identify the other tasks that are scheduled. *)
        Let other_scheduled_task (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          is_hp_task tsk_other.
      
        (* 1) Now we prove that, at all times that j is backlogged, the number
              of tasks other than tsk that are scheduled is exactly the number
              of processors in the system. This is required to prove lemma (2). *)
        Lemma bertogna_fp_all_cpus_are_busy:
          \sum_(tsk_k <- hp_tasks) x tsk_k = X * num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS, H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK, H_jobs_come_from_arrival_sequence into FROMarr,
                 H_constrained_deadlines into RESTR,
                 H_respects_FP_policy into FP,
                 H_previous_jobs_of_tsk_completed into BEFOREok,
                 H_response_time_no_larger_than_deadline into NOMISS.
          unfold sporadic_task_model, respects_FP_policy,
                 respects_JLDP_policy, FP_to_JLDP in *.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _ _) _]big_mkcond.
          apply eq_big_nat; move => t /andP [GEt LTt].
          destruct (backlogged job_arrival job_cost sched j t) eqn:BACK; last first.
          {
            rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
            by intros i _; rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
          }
          rewrite big_mkcond mul1n /=.
          rewrite exchange_big /=.
          apply eq_trans with (y := \sum_(cpu < num_cpus) 1);
            last by rewrite big_const_ord iter_addn mul1n addn0.
          apply eq_bigr; intros cpu _.
          specialize (WORK j t H_j_arrives BACK cpu); des.
          move: WORK => /eqP SCHED.
          rewrite (bigD1_seq (job_task j_other)) /=; last by rewrite filter_uniq; destruct ts.
          {
            rewrite (eq_bigr (fun i => 0));
              last by intros i DIFF; rewrite /task_scheduled_on SCHED;apply/eqP;rewrite eqb0 eq_sym.
            rewrite big_const_seq iter_addn mul0n 2!addn0; apply/eqP; rewrite eqb1.
            by unfold task_scheduled_on; rewrite SCHED.
          }
          have ARRother: arrives_in arr_seq j_other.
            by apply (FROMarr j_other t); apply/existsP; exists cpu; apply/eqP.
          rewrite mem_filter; apply/andP; split; last by apply FROMTS.
          apply/andP; split.
          {
            rewrite -JOBtsk; apply FP with (t := t); try (by done).
            by apply/existsP; exists cpu; apply/eqP. 
          }
          {
            apply/eqP; intro SAMEtsk.
            assert (SCHED': scheduled sched j_other t).
            {
              unfold scheduled, scheduled_on.
              by apply/existsP; exists cpu; rewrite SCHED.
            } clear SCHED; rename SCHED' into SCHED.
            move: (SCHED) => PENDING.
            apply scheduled_implies_pending with (job_arrival0 := job_arrival)
                                                 (job_cost0 := job_cost) in PENDING; try (by done).
            destruct (ltnP (job_arrival j_other) (job_arrival j)) as [BEFOREother | BEFOREj].
            {
              specialize (BEFOREok j_other ARRother SAMEtsk BEFOREother).
              move: PENDING => /andP [_ /negP NOTCOMP]; apply NOTCOMP.
              apply completion_monotonic with (t0 := job_arrival j_other + R); try (by done).
              apply leq_trans with (n := job_arrival j); last by done.
              apply leq_trans with (n := job_arrival j_other + task_deadline tsk);
              first by rewrite leq_add2l; apply NOMISS.
              apply leq_trans with (n := job_arrival j_other + task_period tsk);
                first by rewrite leq_add2l; apply RESTR; rewrite -JOBtsk FROMTS.
              rewrite -SAMEtsk; apply SPO; try (by done); [ | by rewrite JOBtsk | by apply ltnW].
              by red; intro EQ; rewrite EQ ltnn in BEFOREother.
            }
            {
              move: PENDING => /andP [ARRIVED _].
              exploit (SPO j j_other); try (by done); [ | by rewrite SAMEtsk | ]; last first.
              {
                apply/negP; rewrite -ltnNge.
                apply leq_ltn_trans with (n := t); first by done.
                apply leq_trans with (n := job_arrival j + R); first by done.
                by rewrite leq_add2l; apply leq_trans with (n := task_deadline tsk);
                [by apply NOMISS | by rewrite JOBtsk RESTR // -JOBtsk FROMTS].
              }
              by red; intros EQjob; rewrite EQjob /backlogged SCHED andbF in BACK.
            }
          }
        Qed.

        (* 2) Next, using lemmas (0) and (1) we prove that the reduction-based
              interference bound is not enough to cover the sum of the minima over all tasks
              (artifact of the proof by contradiction). *)
        Lemma bertogna_fp_sum_exceeds_total_interference:
          \sum_((tsk_k, R_k) <- hp_bounds)
           x tsk_k > total_interference_bound_fp task_cost task_period hp_bounds R.
        Proof.
          have TOOMUCH := bertogna_fp_too_much_interference.
          have ALLBUSY := bertogna_fp_all_cpus_are_busy.
          rename H_hp_bounds_has_interfering_tasks into HAS,
                 H_response_time_recurrence_holds into REC.
          apply leq_trans with (n := \sum_(tsk_k <- hp_tasks) x tsk_k);
              last first.
          {
            rewrite (eq_bigr (fun i => x (fst i))); last by ins; destruct i.
            have MAP := @big_map _ 0 addn _ _ (fun x => fst x) hp_bounds (fun x => true) (fun y => (x y)).
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
          rewrite -(ltn_add2l (task_cost tsk)) -REC.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by rewrite REC; apply leq_addr.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          rewrite ALLBUSY.
          by rewrite leq_mul2r; apply/orP; right; apply TOOMUCH.
        Qed.

        (* 3) After concluding that the sum of the minima exceeds (R - e_i + 1),
              we prove that there exists a tuple (tsk_k, R_k) that satisfies
              min (x_k, R - e_i + 1) > min (W_k, R - e_i + 1).
              This implies that x_k > W_k, which is of course a contradiction,
              since W_k is a valid task interference bound. *)
        Lemma bertogna_fp_exists_task_that_exceeds_bound :
          exists tsk_k R_k,
            (tsk_k, R_k) \in hp_bounds /\
            x tsk_k > workload_bound tsk_k R_k.
        Proof.
          have SUM := bertogna_fp_sum_exceeds_total_interference.
          rename H_hp_bounds_has_interfering_tasks into HASHP.
          assert (HAS: has (fun tup : task_with_response_time =>
                             let (tsk_k, R_k) := tup in
                               x tsk_k > workload_bound tsk_k R_k)
                            hp_bounds).
          {
            apply/negP; unfold not; intro NOTHAS.
            move: NOTHAS => /negP /hasPn ALL.
            rewrite -[_ < _]negbK in SUM.
            move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
            rewrite (eq_bigr (fun i => x (fst i))); last by ins; destruct i.
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
    
    (* Using the lemmas above, we prove that R bounds the response time of task tsk. *)
    Theorem bertogna_cirinei_response_time_bound_fp :
      response_time_bounded_by tsk R.
    Proof.
      have EX := bertogna_fp_exists_task_that_exceeds_bound.
      have BOUND := bertogna_fp_workload_bounds_interference.
      rename H_response_time_recurrence_holds into REC,
             H_response_time_of_interfering_tasks_is_known into RESP,
             H_hp_bounds_has_interfering_tasks into HAS,
             H_response_time_no_larger_than_deadline into LEdl.
      intros j ARRj JOBtsk.
       
      (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
      remember (job_arrival j + R) as ctime.
      
      (* Now, we apply strong induction on the absolute response-time bound. *)
      generalize dependent j.
      induction ctime as [ctime IH] using strong_ind.

      intros j ARRj JOBtsk EQc; subst ctime.

      (* First, let's simplify the induction hypothesis. *)
      assert (BEFOREok: forall j0,
                          arrives_in arr_seq j0 ->
                          job_task j0 = tsk ->
                          job_arrival j0 < job_arrival j ->
                          service sched j0 (job_arrival j0 + R) >= job_cost j0).
      {
        by ins; apply IH; try (by done); rewrite ltn_add2r.
      } clear IH.
              
      unfold response_time_bounded_by, is_response_time_bound_of_task,
             completed, completed_jobs_dont_execute, valid_sporadic_job in *.

      (* Now we start the proof. Assume by contradiction that job j
         is not complete at time (job_arrival j + R). *)
      destruct (completed job_cost sched j (job_arrival j + R)) eqn:NOTCOMP;
        first by done.
      apply negbT in NOTCOMP; exfalso.

      (* We derive a contradiction using the previous lemmas. *)
      specialize (EX j ARRj JOBtsk NOTCOMP BEFOREok).
      destruct EX as [tsk_k [R_k [HPk LTmin]]].
      specialize (BOUND j tsk_k R_k HPk).
      by apply (leq_ltn_trans BOUND) in LTmin; rewrite ltnn in LTmin.
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.