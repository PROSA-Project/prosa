Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.response_time prosa.classic.model.schedule.global.schedulability
               prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.apa.platform prosa.classic.model.schedule.apa.constrained_deadlines
               prosa.classic.model.schedule.apa.interference prosa.classic.model.schedule.apa.affinity.
Require Import prosa.classic.analysis.apa.workload_bound
               prosa.classic.analysis.apa.interference_bound_fp.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference InterferenceBoundFP
         Platform Schedulability ResponseTime Priority
         TaskArrival WorkloadBound Affinity ConstrainedDeadlines.
    
  (* In this section, we prove that any fixed point in the APA-reduction of Bertogna
     and Cirinei's RTA for FP scheduling with slack updates is a safe response-time
     bound. This result corresponds to Lemma 9 in the revised version of the APA paper:
     http://www.mpi-sws.org/~bbb/papers/pdf/ecrts13a-rev1.pdf *)
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
      forall j,
        arrives_in arr_seq j -> job_task j \in ts.

    (* Also assume that every task has a non-empty processor affinity alpha. *)
    Context {num_cpus: nat}.
    Variable alpha: task_affinity sporadic_task num_cpus.

    (* Next, consider any schedule such that...*)
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    
    (* ...jobs are sequential and do not execute before their
       arrival times nor longer than their execution costs. *)
    Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Consider a given FP policy, ... *)
    Variable higher_eq_priority: FP_policy sporadic_task.

    (* ... and assume that the schedule is an APA work-conserving
       schedule that respects this policy. *)
    Hypothesis H_respects_affinity: respects_affinity job_task sched alpha.
    Hypothesis H_work_conserving: apa_work_conserving job_arrival job_cost job_task
                                                      arr_seq sched alpha.
    Hypothesis H_respects_FP_policy:
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
                                        sched alpha higher_eq_priority.

    (* Let's define some local names to avoid passing many parameters. *)
    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.

    (* Next, we consider the response-time recurrence.
       Let tsk be a task in ts that is to be analyzed. *)
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    (* When computing the response-time bounds, we assume that each task under
       analysis has a non-empty subaffinity alpha'. *)
    Variable alpha': task_affinity sporadic_task num_cpus.
    Hypothesis H_affinity_subset: forall tsk, tsk \in ts -> is_subaffinity (alpha' tsk) (alpha tsk).
    Hypothesis H_at_least_one_cpu : forall tsk, tsk \in ts -> #|alpha' tsk| > 0.
    
    (* Let (hp_task_in alpha') denote whether a task is a higher-priority task
       (with respect to tsk) that can execute on processors in (alpha' tsk). *)
    Let hp_task_in alpha' := higher_priority_task_in alpha higher_eq_priority tsk alpha'.

    (* Assume a response-time bound is known... *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    Hypothesis H_response_time_of_interfering_tasks_is_known:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R.
    
    (* ... for every higher-priority task in (alpha tsk). *)
    Hypothesis H_hp_bounds_has_interfering_tasks:
      forall hp_tsk,
        hp_tsk \in ts ->
        hp_task_in (alpha tsk) hp_tsk ->
        exists R,
          (hp_tsk, R) \in hp_bounds.

    (* Assume that the response-time bounds are larger than task costs. *)
    Hypothesis H_response_time_bounds_ge_cost:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds -> R >= task_cost hp_tsk.
    
    (* Assume that no deadline is missed by any higher-priority task. *)
    Hypothesis H_interfering_tasks_miss_no_deadlines:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds -> R <= task_deadline hp_tsk.
    
    (* Let R be the fixed point of the APA-reduction of Bertogna and
       Cirinei's response-time recurrence (using subaffinity alpha'), ...*)
    Variable R: time.
    Hypothesis H_response_time_recurrence_holds :
      R = task_cost tsk +
          div_floor
            (total_interference_bound_fp task_cost task_period alpha tsk
                            (alpha' tsk) hp_bounds R higher_eq_priority)
            #|alpha' tsk|.

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
        task_interference job_arrival job_cost job_task sched alpha j tsk_other
                          (job_arrival j) (job_arrival j + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R).

      (* Recall Bertogna and Cirinei's workload bound. *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W task_cost task_period tsk_other R_other R.

      (* Let (hp_tasks_in alpha') denote the set of higher-priority tasks
         that can be scheduled on subaffinity alpha'. *)
      Let hp_tasks_in alpha' :=
        [seq tsk_other <- ts | hp_task_in (alpha' tsk) tsk_other].

      (* Now we establish results the higher-priority tasks. *)
      Section LemmasAboutHPTasks.
        
        (* Let (tsk_other, R_other) be any pair of higher-priority task
           and response-time bound computed in previous iterations. *)
        Variable tsk_other: sporadic_task.
        Variable R_other: time.
        Hypothesis H_tsk_other_already_processed: (tsk_other, R_other) \in hp_bounds.
        Hypothesis H_tsk_other_has_higher_priority: hp_task_in (alpha tsk) tsk_other.

        (* Since tsk_other cannot interfere more than it executes, we show that
           the interference caused by tsk_other is no larger than workload bound W. *)
        Lemma bertogna_fp_workload_bounds_interference :
          x tsk_other <= workload_bound tsk_other R_other.
        Proof.
          unfold completed, completed_jobs_dont_execute, valid_sporadic_job in *.
          rename H_valid_job_parameters into PARAMS,
                 H_valid_task_parameters into TASK_PARAMS,
                 H_constrained_deadlines into RESTR,
                 H_all_jobs_from_taskset into FROMTS,
                 H_response_time_of_interfering_tasks_is_known into RESP,
                 H_interfering_tasks_miss_no_deadlines into NOMISS,
                 H_response_time_bounds_ge_cost into GE_COST.
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
          destruct (sched cpu t) as [j0 |] eqn:SCHED'; last by done.
          assert (INts: tsk_other \in ts).
          {
            move: SCHED => /eqP <-. apply FROMTS, (H_jobs_come_from_arrival_sequence j0 t).
            by apply/existsP; exists cpu; apply/eqP.
          }
          apply leq_trans with (n := workload job_task sched tsk_other
                                              (job_arrival j) (job_arrival j + R));
            first by apply task_interference_le_workload.
          by apply workload_bounded_by_W with (task_deadline0 := task_deadline) (arr_seq0 := arr_seq)
             (job_arrival0 := job_arrival) (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by ins); last 2 first;
              [ by ins; apply GE_COST 
              | by ins; apply NOMISS
              | by ins; apply TASK_PARAMS
              | by ins; apply RESTR
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
                 H_job_of_tsk into JOBtsk, H_j_not_completed into NOTCOMP.
          unfold completed, valid_sporadic_job in *.
          unfold X, total_interference; rewrite addn1.
          rewrite -(ltn_add2r (task_cost tsk)).
          rewrite subh1; last by rewrite [R]REC // leq_addr.
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

        (* 1) Next, we prove that during the scheduling window of j, any job that is
              scheduled while j is backlogged comes from a different task.
              This follows from the fact that j is the first job not to complete
              by its response-time bound, so previous jobs of j's task must have
              completed by their periods and cannot be pending. *)
        Lemma bertogna_fp_interference_by_different_tasks :
          forall t j_other,
            job_arrival j <= t < job_arrival j + R ->
            arrives_in arr_seq j_other ->
            backlogged job_arrival job_cost sched j t ->
            scheduled sched j_other t ->
            job_task j_other != tsk.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK,
                 H_previous_jobs_of_tsk_completed into BEFOREok,
                 H_response_time_no_larger_than_deadline into NOMISS,
                 H_constrained_deadlines into RESTR.
          move => t j_other /andP [LEt GEt] ARRother BACK SCHED.
          apply/eqP; red; intro SAMEtsk.
          move: SCHED => /existsP [cpu SCHED].
          assert (SCHED': scheduled sched j_other t).
            by apply/existsP; exists cpu.
          clear SCHED; rename SCHED' into SCHED.
          move: (SCHED) => PENDING.
          apply scheduled_implies_pending with (job_arrival0 := job_arrival)
                                               (job_cost0 := job_cost) in PENDING; try (by done).
          destruct (ltnP (job_arrival j_other) (job_arrival j)) as [BEFOREother | BEFOREj].
           {
            move: (BEFOREother) => LT; rewrite -(ltn_add2r R) in LT.
            specialize (BEFOREok j_other ARRother SAMEtsk BEFOREother).
            move: PENDING => /andP [_ /negP NOTCOMP]; apply NOTCOMP.
            apply completion_monotonic with (t0 := job_arrival j_other + R); try (by done).
            apply leq_trans with (n := job_arrival j); last by done.
            apply leq_trans with (n := job_arrival j_other + task_deadline tsk);
              first by rewrite leq_add2l; apply NOMISS.
            apply leq_trans with (n := job_arrival j_other + task_period tsk);
              first by rewrite leq_add2l; apply RESTR; rewrite -JOBtsk FROMTS.
            rewrite -SAMEtsk; apply SPO; try (by done); [ | by rewrite JOBtsk | by apply ltnW].
            by red; intro EQ; subst j_other; rewrite ltnn in BEFOREother.
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
            by red; intros EQtsk; subst j_other; rewrite /backlogged SCHED andbF in BACK.
          }
        Qed.

        (* 2) In order to use the lemmas in constrained_deadlines.v, we show that
              all jobs of higher-priority tasks released before the end of the
              interval complete by their periods. This follows trivially from
              the fact that all these tasks are known to be schedulable. 
              With this lemma, we can conclude that during job j's scheduling
              window there cannot be multiple pending jobs of higher-priority tasks.*)
        Lemma bertogna_fp_previous_interfering_jobs_complete_by_their_period:
          forall j0,
            arrives_in arr_seq j0 ->
            hp_task_in (alpha tsk) (job_task j0) ->
            completed job_cost sched j0
               (job_arrival j0 + task_period (job_task j0)).
        Proof.
          rename H_hp_bounds_has_interfering_tasks into HAS,
                 H_constrained_deadlines into CONSTR,
                 H_response_time_no_larger_than_deadline into NOMISS,
                 H_all_jobs_from_taskset into FROMTS,
                 H_interfering_tasks_miss_no_deadlines into NOMISS',
                 H_previous_jobs_of_tsk_completed into BEFOREok,
                 H_response_time_of_interfering_tasks_is_known into RESP.
          intros j0 ARR0 INTERF.
          exploit (HAS (job_task j0));
            [by rewrite FROMTS | by done | move => [R0 INbounds]].
          apply completion_monotonic with (t := job_arrival j0 + R0).
          - rewrite leq_add2l; apply leq_trans with (n := task_deadline (job_task j0));
              [by apply NOMISS' | by apply CONSTR; rewrite FROMTS].
          - by apply (RESP (job_task j0)).
        Qed.

        (* 3) Next, we prove that the sum of the interference of each task is equal to the
              total interference multiplied by the number of processors in tsk's *actual*
              affinity. This holds because interference only occurs when all processors in
              the affinity are busy.
              With this lemma we can relate per-task interference with the total interference
              incurred by j (backlogged time). *)
        Lemma bertogna_fp_all_cpus_in_affinity_busy :
          \sum_(tsk_k <- hp_tasks_in alpha) x tsk_k = X * #|alpha tsk|.
        Proof.
          have DIFFTASK := bertogna_fp_interference_by_different_tasks.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK, H_jobs_come_from_arrival_sequence into SEQ,
                 H_previous_jobs_of_tsk_completed into BEFOREok,
                 H_response_time_no_larger_than_deadline into NOMISS,
                 H_constrained_deadlines into RESTR,
                 H_respects_affinity into APA, H_respects_FP_policy into FP.
          unfold sporadic_task_model in *.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /= mul1n.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _ _) _]big_mkcond.
          apply eq_big_nat; move => t /andP [GEt LTt].
          destruct (backlogged job_arrival job_cost sched j t) eqn:BACK; last first.
          {
            rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
            by intros i _; rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
          }
          rewrite big_mkcond /=.
          rewrite exchange_big /=.
          apply eq_trans with (y := \sum_(cpu < num_cpus | cpu \in alpha tsk) 1);
            last by rewrite sum1_card.
          rewrite [\sum_(_ < _ | _) 1]big_mkcond /=.
          apply eq_bigr; intros cpu _.
          unfold can_execute_on in *.
          destruct (cpu \in alpha (job_task j)) eqn:ALPHA; rewrite -?JOBtsk ALPHA;
            last by rewrite big_filter (eq_bigr (fun x => 0));
              [by simpl_sum_const | by ins].
          move: (WORK j t H_j_arrives BACK cpu ALPHA) => [j_other /eqP SCHED]; unfold scheduled_on in *.
          rewrite (bigD1_seq (job_task j_other)) /=; last by rewrite filter_uniq; destruct ts.
          {
            rewrite (eq_bigr (fun i => 0));
              last by intros i DIFF; rewrite /task_scheduled_on SCHED;apply/eqP;rewrite eqb0 eq_sym.
            rewrite big_const_seq iter_addn mul0n 2!addn0; apply/eqP; rewrite eqb1.
            by unfold task_scheduled_on; rewrite SCHED.
          }
          have ARRother: arrives_in arr_seq j_other.
            by apply (SEQ j_other t); apply/existsP; exists cpu; apply/eqP.
          rewrite mem_filter; apply/andP; split; last by apply FROMTS.
          unfold higher_priority_task_in, affinity_intersects.
          apply/andP; split; last first.
          {
            apply/existsP; exists cpu; rewrite -JOBtsk ALPHA andTb.
            by apply APA with (t := t); apply/eqP.
          }
          apply/andP; split; last first.
          {
            apply DIFFTASK with (t := t); try (by done); first by auto.
            by apply/existsP; exists cpu; apply/eqP.
          }
          by rewrite -JOBtsk; apply FP with (cpu := cpu) (t := t); try (by apply/eqP).
        Qed.

        (* 4) Recall that the reduction-based analysis considers only the interfering tasks
              within subaffinity (alpha' tsk), as opposed to (alpha tsk). Therefore, we must
              reason about the task interference wihin (alpha' tsk).
              We begin by showing that the cumulative interference within (alpha' tsk) is at
              least the total interference multiplied by the number of processors in (alpha' tsk). *)
        Lemma bertogna_fp_all_cpus_in_subaffinity_busy :
          \sum_(tsk_k <- hp_tasks_in alpha') x tsk_k >= X * #|alpha' tsk|.
        Proof.
          have DIFFTASK := bertogna_fp_interference_by_different_tasks.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS, H_jobs_come_from_arrival_sequence into SEQ,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK,
                 H_response_time_no_larger_than_deadline into NOMISS,
                 H_constrained_deadlines into RESTR,
                 H_respects_FP_policy into FP,
                 H_respects_affinity into APA, H_affinity_subset into SUB.
          unfold sporadic_task_model in *.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /= mul1n.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _ _) _]big_mkcond /=.
          apply leq_sum_nat; move => t /andP [GEt LTt] _.
          destruct (backlogged job_arrival job_cost sched j t) eqn:BACK; last first.
          {
            rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
            by intros i _; rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
          }
          rewrite big_mkcond /=.
          rewrite exchange_big /=.
          apply leq_trans with (n := \sum_(cpu < num_cpus | cpu \in alpha' tsk) 1);
            first by rewrite sum1_card.
          rewrite [\sum_(_ < _ | _) 1]big_mkcond /=.
          apply leq_sum; intros cpu _.
          unfold can_execute_on in *.
          destruct (cpu \in alpha' (job_task j)) eqn:ALPHA'; rewrite -?JOBtsk ALPHA';
            last by done.
          feed (SUB (job_task j)); first by apply FROMTS.
          specialize (SUB cpu ALPHA').
          move: (WORK j t H_j_arrives BACK cpu SUB) => [j_other /eqP SCHED]; unfold scheduled_on in *.
          have ARRother: arrives_in arr_seq j_other.
            by apply (SEQ j_other t); apply/existsP; exists cpu; apply/eqP.          
          rewrite (bigD1_seq (job_task j_other)) /=; last by apply filter_uniq; destruct ts.
          {
            by rewrite {1}/task_scheduled_on SUB SCHED eq_refl andTb.
          }
          {
            rewrite mem_filter; apply/andP; split; last by apply FROMTS.
            apply/andP; split; last first.
            {
              apply/existsP; exists cpu; apply/andP; split; first by rewrite -JOBtsk.
              by apply APA with (t := t); apply/eqP.
            }
            apply/andP; split; last first.
            {
              apply DIFFTASK with (t := t); try (by done); first by auto.
              by apply/existsP; exists cpu; apply/eqP.
            }
            by rewrite -JOBtsk; apply FP with (cpu := cpu) (t := t); try (by apply/eqP).
          }
        Qed.

        (* Let's define a predicate for whether a task is scheduled on (alpha tsk). *)
        Let scheduled_on_alpha_tsk := fun t tsk_k =>
          task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t.


        (* 5) Now we prove that, at all times that j is backlogged, the number
           of tasks whose affinity intersects (alpha' tsk) that are in fact
           scheduled on (alpha' tsk) is at least the size of (alpha' tsk).
           This is required to prove lemma (6). *)
        Lemma bertogna_fp_alpha'_is_full:
          forall t,
            job_arrival j <= t < job_arrival j + R ->
            backlogged job_arrival job_cost sched j t ->
            count (scheduled_on_alpha_tsk t) (hp_tasks_in alpha') >= #|alpha' tsk|.
        Proof.
          have DIFFTASK := bertogna_fp_interference_by_different_tasks.
          have COMP := bertogna_fp_previous_interfering_jobs_complete_by_their_period.
          rename H_work_conserving into WORK, H_respects_affinity into APA,
                 H_affinity_subset into SUB, H_job_of_tsk into JOBtsk,
                 H_all_jobs_from_taskset into FROMTS, H_jobs_come_from_arrival_sequence into FROMSEQ,
                 H_valid_task_parameters into PARAMS,
                 H_previous_jobs_of_tsk_completed into BEFOREok,
                 H_sequential_jobs into SEQ, H_constrained_deadlines into CONSTR,
                 H_respects_FP_policy into FP.
          move => t /andP [GEt LTt] BACK. 
          move: WORK  => WORK.
          specialize (WORK j t H_j_arrives BACK).
          rewrite -size_filter.
          apply leq_trans with (n := size (alpha' tsk));
            first by apply card_size.
          apply leq_trans with (n := size (pmap (fun cpu => sched cpu t) (enum (alpha' tsk)))).
          {
            rewrite size_pmap -size_filter.
            apply uniq_leq_size; first by destruct (alpha' tsk).
            intros cpu IN.
            rewrite mem_filter; apply/andP; split; last by rewrite mem_enum.
            feed (WORK cpu); first by apply SUB; rewrite JOBtsk.
            by move: WORK => [j_other /eqP SCHED]; rewrite SCHED.
          }
          {
            apply leq_trans with (n := size (map (fun j => job_task j) (pmap (fun cpu => sched cpu t) (enum (alpha' tsk)))));
              first by rewrite size_map.
            apply uniq_leq_size.
            {
              rewrite map_inj_in_uniq.
              {
                apply pmap_inj_in_uniq; last by apply enum_uniq.
                intros cpu1 cpu2 IN1 IN2 SCHED2.
                destruct (sched cpu1 t) as [j0 |] eqn:SCHED1; symmetry in SCHED2;
                  first by apply SEQ with (j := j0) (t := t).
                rewrite 2!mem_enum in IN1 IN2.
                exploit (WORK cpu1); first by apply SUB; rewrite JOBtsk.
                by move => [j_other SCHED]; rewrite /scheduled_on SCHED1 in SCHED.  
              }
              {
                intros j1 j2 SCHED1 SCHED2 SAMEtsk.
                rewrite 2!mem_pmap in SCHED1 SCHED2.
                move: SCHED1 SCHED2 => /mapP [cpu1 IN1 SCHED1] /mapP [cpu2 IN2 SCHED2].
                have ARR1: arrives_in arr_seq j1.
                  by apply (FROMSEQ j1 t); apply/existsP; exists cpu1; apply/eqP. 
                have ARR2: arrives_in arr_seq j2.
                  by apply (FROMSEQ j2 t); apply/existsP; exists cpu2; apply/eqP. 
                assert (PENDING1: pending job_arrival job_cost sched j1 t).
                {
                  apply scheduled_implies_pending; try by done.
                  by apply/existsP; exists cpu1; rewrite /scheduled_on -SCHED1.
                }
                assert (SCHED2': pending job_arrival job_cost sched j2 t).
                {
                  apply scheduled_implies_pending; try by done.
                  by apply/existsP; exists cpu2; rewrite /scheduled_on -SCHED2. 
                }

                apply platform_fp_no_multiple_jobs_of_interfering_tasks with
                  (arr_seq0 := arr_seq) (task_period0 := task_period) (tsk0 := tsk) (alpha0 := alpha)
                  (job_arrival0 := job_arrival) (higher_eq_priority0 := higher_eq_priority) (t0 := t)
                (job_cost0 := job_cost) (job_task0 := job_task) (sched0 := sched);
                  rewrite ?JOBtsk ?SAMEtsk //.
                {
                  by intros j0 tsk0 TSK0 LE; subst tsk0; apply COMP.
                }
                {
                  apply/andP; split; last first.
                  {
                    apply/existsP; exists cpu2; apply/andP; split.
                    by apply SUB; [rewrite -JOBtsk FROMTS | rewrite -mem_enum].
                    by apply APA with (t := t); apply/eqP; rewrite SCHED2.
                  }
                  apply/andP; split.
                  {
                    rewrite -JOBtsk; apply FP with (cpu := cpu2) (t := t); try (by done);
                      first by apply/eqP; rewrite SCHED2.
                    by apply SUB; rewrite ?FROMTS // -mem_enum JOBtsk.
                  }
                  {
                    apply DIFFTASK with (t := t); try (by done); first by auto.
                    by apply/existsP; exists cpu2; apply/eqP; rewrite SCHED2.
                  }
                }
              }
            }
            {
              move => tsk' /mapP [j' IN EQtsk'].
              rewrite mem_pmap in IN.
              move: IN => /mapP [cpu INcpu SCHED'].
              rewrite mem_enum in INcpu.
              rewrite mem_filter; apply/andP; split.
              {
                apply/existsP; exists cpu; apply/andP; split; first by apply SUB.
                by rewrite /task_scheduled_on -SCHED' EQtsk'.
              }
              have ARR': arrives_in arr_seq j'.
                by apply (FROMSEQ j' t); apply/existsP; exists cpu; apply/eqP. 
              rewrite EQtsk' mem_filter; apply/andP; split; last by apply FROMTS.
              apply/andP; split; last first.
              {
                apply/existsP; exists cpu; apply/andP; split; first by done.
                by apply APA with (t := t); rewrite /scheduled_on SCHED'.
              }
              apply/andP; split.
              {
                by rewrite -JOBtsk; apply FP with (cpu := cpu) (t := t);
                  try (by done); [by apply/eqP; rewrite SCHED' | apply SUB; rewrite JOBtsk].
              }
              {
                apply/eqP; intro SAMEtsk.
                move: BACK => /andP [PENDING NOTSCHED].
                assert (SCHEDULED': scheduled sched j' t).
                {
                  by apply/existsP; exists cpu; rewrite /scheduled_on -SCHED'.
                }
                move: (SCHEDULED') => PENDING'.
                apply scheduled_implies_pending with (job_cost0 := job_cost)
                            (job_arrival0 := job_arrival) in PENDING'; try by done.
                assert (BUG: j' = j).
                {
                  apply platform_fp_no_multiple_jobs_of_tsk with (task_cost0 := task_cost)
                    (task_period0 := task_period) (task_deadline0 := task_deadline)
                    (job_arrival0 := job_arrival) (job_cost0 := job_cost) (job_task0 := job_task)
                    (arr_seq0 := arr_seq) (sched0 := sched) (tsk0 := tsk) (t0 := t);
                    try (by done);
                    [by apply PARAMS | by apply/andP; split | |].
                  {
                    apply leq_trans with (n := job_arrival j + R); first by done.
                    by rewrite leq_add2l; apply leq_trans with (n := task_deadline tsk);
                      last by apply CONSTR; rewrite -JOBtsk FROMTS.
                  }
                  {
                    intros j0 JOB0 ARR0 LT0.
                    apply completion_monotonic with (t0 := job_arrival j0 + R); [| by apply BEFOREok].
                    by rewrite leq_add2l; apply leq_trans with (n := task_deadline tsk);
                      last by apply CONSTR; rewrite -JOBtsk FROMTS.
                  }
                }
                by rewrite -BUG SCHEDULED' in NOTSCHED.
              }
            }
          }
        Qed.

        (* Before stating the next lemma, let (num_tasks_exceeding delta) be the
           number of interfering tasks that can execute on (alpha' tsk) whose
           interference x is larger than delta. *)
        Let num_tasks_exceeding delta := count (fun i => x i >= delta) (hp_tasks_in alpha').

        (* 6) Now we prove that, for any delta, if (num_task_exceeding delta > 0), then the
              cumulative interference caused by the complementary set of interfering tasks fills
              the remaining, not-completely-full (#|alpha' tsk| - num_tasks_exceeding delta)
              processors. *)
        Lemma bertogna_fp_interference_in_non_full_processors :
          forall delta,
            0 < num_tasks_exceeding delta < #|alpha' tsk| ->
            \sum_(i <- hp_tasks_in alpha' | x i < delta) x i >= delta * (#|alpha' tsk| - num_tasks_exceeding delta).
        Proof.
          have ATMOST := platform_at_most_one_pending_job_of_each_task.
          have INV := bertogna_fp_alpha'_is_full.
          have DIFFTASK := bertogna_fp_interference_by_different_tasks.
          have COMP := bertogna_fp_previous_interfering_jobs_complete_by_their_period.
          rename H_all_jobs_from_taskset into FROMTS, H_jobs_come_from_arrival_sequence into FROMSEQ,
                 H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk, H_affinity_subset into SUB,
                 H_sporadic_tasks into SPO, H_respects_affinity into APA,
                 H_constrained_deadlines into RESTR,
                 H_sequential_jobs into SEQ, H_respects_FP_policy into FP.
          unfold sporadic_task_model in *.
          move => delta /andP [HAS LT]. 
          rewrite -has_count in HAS.

          set some_interference_A := fun t =>
            has (fun tsk_k => backlogged job_arrival job_cost sched j t &&
                              (x tsk_k >= delta) &&
                              scheduled_on_alpha_tsk t tsk_k)
              (hp_tasks_in alpha').
          set total_interference_B := fun t =>
              backlogged job_arrival job_cost sched j t *
              count (fun tsk_k => (x tsk_k < delta) &&
                    scheduled_on_alpha_tsk t tsk_k) (hp_tasks_in alpha').

          apply leq_trans with ((\sum_(job_arrival j <= t < job_arrival j + R)
                                some_interference_A t) * (#|alpha' tsk| - num_tasks_exceeding delta)).
          {
            rewrite leq_mul2r; apply/orP; right.
            move: HAS => /hasP HAS; destruct HAS as [tsk_a INa LEa].
            apply leq_trans with (n := x tsk_a); first by apply LEa.
            unfold x, task_interference, some_interference_A.
            apply leq_sum_nat; move => t /andP [GEt LTt] _.
            destruct (backlogged job_arrival job_cost sched j t) eqn:BACK;
              last by rewrite (eq_bigr (fun x => 0)); [by simpl_sum_const | by ins].
            destruct ([exists cpu, can_execute_on alpha (job_task j) cpu &&
                                task_scheduled_on job_task sched tsk_a cpu t]) eqn:SCHED;
              last first.
            {
              apply negbT in SCHED; rewrite negb_exists in SCHED; move: SCHED => /forallP ALL.
              rewrite (eq_bigr (fun x => 0)); first by simpl_sum_const.
              by intros cpu _; specialize (ALL cpu); apply negbTE in ALL; rewrite ALL.
            }
            move: SCHED => /existsP [cpu /andP [CAN SCHED]].
            apply leq_trans with (n := 1); last first.
            {
              rewrite lt0b; apply/hasP; exists tsk_a; first by done.
              rewrite LEa 2!andTb; apply/existsP; exists cpu.
              by apply/andP; split; first by rewrite -JOBtsk.
            }
            rewrite (bigD1 cpu) /= // SCHED.
            rewrite (eq_bigr (fun x => 0)); first by simpl_sum_const; rewrite leq_b1.
            intros cpu' DIFF.
            apply/eqP; rewrite eqb0; apply/negP.
            move => /andP [ALPHA' SCHED'].
            move: DIFF => /negP DIFF; apply DIFF; apply/eqP.
            unfold task_scheduled_on in *.
            destruct (sched cpu t) as [j1|] eqn:SCHED1; last by done.
            destruct (sched cpu' t) as [j2|] eqn:SCHED2; last by done.
            move: SCHED SCHED' => /eqP JOB /eqP JOB'.
            subst tsk_a; symmetry in JOB'.
            assert (BUG: j1 = j2).
            {
              have ARR1: arrives_in arr_seq j1.
                by apply (FROMSEQ j1 t); apply/existsP; exists cpu; apply/eqP. 
              have ARR2: arrives_in arr_seq j2.
                by apply (FROMSEQ j2 t); apply/existsP; exists cpu'; apply/eqP.             
              assert (PENDING1: pending job_arrival job_cost sched j1 t).
              {
                apply scheduled_implies_pending; try by done.
                by apply/existsP; exists cpu; rewrite /scheduled_on -SCHED1.
              }
              assert (SCHED2': pending job_arrival job_cost sched j2 t).
              {
                apply scheduled_implies_pending; try by done.
                by apply/existsP; exists cpu'; rewrite /scheduled_on -SCHED2. 
              }
              apply platform_fp_no_multiple_jobs_of_interfering_tasks with
                (arr_seq0 := arr_seq) (task_period0 := task_period) (tsk0 := tsk) (alpha0 := alpha)
                (job_arrival0 := job_arrival) (higher_eq_priority0 := higher_eq_priority) (t0 := t)
                (job_cost0 := job_cost) (job_task0 := job_task) (sched0 := sched); try (by done);
                  rewrite ?JOBtsk ?SAMEtsk //.
                {
                  by intros j0 tsk0 TSK0 LE; subst tsk0; apply COMP.
                }
                {
                  apply/andP; split; last first.
                  {
                    apply/existsP; exists cpu; apply/andP; split;
                      first by rewrite -JOBtsk.
                    by apply APA with (t := t); apply/eqP.
                  }
                  apply/andP; split.
                  {
                    by rewrite -JOBtsk; apply FP with (cpu := cpu) (t := t);
                      try (by done); apply/eqP.
                  }
                  {
                    apply DIFFTASK with (t := t); try (by done); first by auto.
                    by apply/existsP; exists cpu; apply/eqP.
                  }
                }
              }
              by subst j2; apply SEQ with (j := j1) (t := t).
            }

          apply leq_trans with (\sum_(job_arrival j <= t < job_arrival j + R)
                                     total_interference_B t).
          {
            rewrite big_distrl /=.
            apply leq_sum_nat; move => t LEt _.
            unfold some_interference_A, total_interference_B. 
            destruct (backlogged job_arrival job_cost sched j t) eqn:BACK;
              [rewrite mul1n /= | by rewrite has_pred0 //].

            destruct (has (fun tsk_k : sporadic_task => (delta <= x tsk_k) &&
                       scheduled_on_alpha_tsk t tsk_k) (hp_tasks_in alpha')) eqn:HAS';
              last by done.
            rewrite mul1n; move: HAS => /hasP [tsk_k INk LEk].
            unfold num_tasks_exceeding.
            apply leq_trans with (n := #|alpha' tsk| -
                         count (fun i => (x i >= delta) &&
                            scheduled_on_alpha_tsk t i) (hp_tasks_in alpha')).
            {
              apply leq_sub2l.
              rewrite -2!sum1_count big_mkcond /=.
              rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
              apply leq_sum; intros i _.
              by destruct (scheduled_on_alpha_tsk t i);
                [by rewrite andbT | by rewrite andbF].
            }
            rewrite -count_filter -[count _ (hp_tasks_in _)]count_filter.
            eapply leq_trans with (n := count (predC (fun tsk => delta <= x tsk)) _);
              last by apply eq_leq, eq_in_count; red; ins; rewrite ltnNge.
            rewrite leq_subLR count_predC size_filter.
            move: INV => INV. by apply (INV t).
          }
          {
            unfold x at 2, total_interference_B.
            rewrite exchange_big /=; apply leq_sum; intros t _.
            destruct (backlogged job_arrival job_cost sched j t) eqn:BACK; last by ins.
            rewrite mul1n -sum1_count.
            rewrite big_mkcond [\sum_(i <- hp_tasks_in alpha' | _ < _) _]big_mkcond /=.
            apply leq_sum_seq; move => tsk_k IN _.
            destruct (x tsk_k < delta); [rewrite andTb | by rewrite andFb].
            destruct (scheduled_on_alpha_tsk t tsk_k) eqn:SCHED; last by done.
            move: SCHED => /existsP [cpu /andP [ALPHA SCHED]].
            rewrite (bigD1 cpu) /= // JOBtsk SCHED andbT.
            by rewrite /can_execute_on ALPHA.
          }
        Qed.

        (* 7) Based on lemma (6), we prove that, for any interval delta, if the sum of per-task
              interference exceeds (delta * |alpha' tsk|), the same applies for the
              sum of the minimum of the interference and delta. *)
        Lemma bertogna_fp_minimum_exceeds_interference :
          forall delta,
            \sum_(tsk_k <- hp_tasks_in alpha') x tsk_k >= delta * #|alpha' tsk| ->
               \sum_(tsk_k <- hp_tasks_in alpha') minn (x tsk_k) delta >=
               delta * #|alpha' tsk|.
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
          destruct (~~ has (fun i => delta <= x i) (hp_tasks_in alpha')) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in hp_tasks_in alpha') && true));
              last by red; intros tsk_k; destruct (tsk_k \in hp_tasks_in alpha') eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond.
          } apply negbFE in HASa.

          (* Case 2: num_tasks_exceeding >= |alpha' tsk| *)
          destruct (num_tasks_exceeding delta >= #|alpha' tsk|) eqn:CARD.
          {
            apply leq_trans with (delta * num_tasks_exceeding delta);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold num_tasks_exceeding; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          (* Case 3: num_tasks_exceeding < |alpha' tsk| *)
          rewrite big_const_seq iter_addn addn0; fold num_tasks_exceeding.
          apply leq_trans with (n := delta * num_tasks_exceeding delta +
                                     delta * (#|alpha' tsk| - num_tasks_exceeding delta));
            first by rewrite -mulnDr subnKC //; apply ltnW.
          rewrite leq_add2l bertogna_fp_interference_in_non_full_processors //.
          by apply/andP; split; [by rewrite -has_count | by done].
        Qed.

        (* 8) Note that lemma (7) only refers to interference within subaffinity (alpha' tsk).
              To reason about the interference incurred by job j in its complete affinity,
              we prove that an exceeding interference on affinity (alpha tsk) also
              implies an exceeding interference on the subaffinity (alpha' tsk). *)
        Lemma bertogna_fp_interference_on_subaffinity :
          forall delta,
            \sum_(tsk_k <- hp_tasks_in alpha) x tsk_k >= delta * #|alpha tsk| ->
            \sum_(tsk_k <- hp_tasks_in alpha') x tsk_k >= delta * #|alpha' tsk|.
        Proof.
          have ALL := bertogna_fp_all_cpus_in_affinity_busy.
          have SUB := bertogna_fp_all_cpus_in_subaffinity_busy.
          rename H_at_least_one_cpu into NONEMPTY',
                 H_job_of_tsk into JOBtsk, H_affinity_subset into SUBSET,
                 H_all_jobs_from_taskset into FROMTS.
          intros delta LE.
          rewrite ALL in LE.
          apply leq_trans with (n := X * #|alpha' tsk|); last by apply SUB.
          rewrite leq_mul2r in LE;  move: LE => /orP [/eqP EMPTY | LEx];
            last by rewrite leq_mul2r; apply/orP; right.
          assert (NONEMPTY: #|alpha tsk| > 0).
          {
            apply leq_trans with (n := #|alpha' tsk|);
              last by apply leq_subaffinity, SUBSET; rewrite -JOBtsk FROMTS.
            by apply NONEMPTY'; rewrite -JOBtsk FROMTS.
          }
          by rewrite EMPTY ltnn in NONEMPTY.
        Qed.

        (* 9) Next, using lemmas (0), (3), (7) and (8), we prove that the reduction-based
              interference bound is not enough to cover the sum of the minima over all tasks
              (artifact of the proof by contradiction). *)
        Lemma bertogna_fp_sum_exceeds_total_interference:
          \sum_((tsk_other, R_other) <- hp_bounds | hp_task_in (alpha' tsk) tsk_other)
           minn (x tsk_other) (R - task_cost tsk + 1) >
          total_interference_bound_fp task_cost task_period alpha tsk
                           (alpha' tsk) hp_bounds R higher_eq_priority.
        Proof.
          have EXCEEDS := bertogna_fp_minimum_exceeds_interference.
          have SUB := bertogna_fp_interference_on_subaffinity.
          have ALLBUSY := bertogna_fp_all_cpus_in_affinity_busy.
          have TOOMUCH := bertogna_fp_too_much_interference.

          rename H_hp_bounds_has_interfering_tasks into HAS,
                 H_response_time_recurrence_holds into REC,
                 H_at_least_one_cpu into NONEMPTY,
                 H_affinity_subset into SUBSET.
          unfold total_interference_bound_fp.
          apply leq_trans with (n := \sum_(tsk_other <- hp_tasks_in alpha') minn (x tsk_other) (R - task_cost tsk + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
              last by ins; destruct i.
            rewrite (eq_bigl (fun i => hp_task_in (alpha' tsk) (fst i)));
              last by intro p; destruct p.
            have MAP := @big_map _ 0 addn _ _ (fun x => fst x) hp_bounds _ (fun y => minn (x y) (R - task_cost tsk + 1)).
            rewrite -MAP.
            rewrite -[\sum_(_ <- [seq fst _ | _ <- _] | _)_]big_filter. 
            apply leq_sum_sub_uniq; first by apply filter_uniq; destruct ts.
            red; move => tsk0 IN0.
            rewrite mem_filter in IN0; move: IN0 => /andP [INTERF0 IN0].
            rewrite mem_filter; apply/andP; split; first by done.
            apply/mapP.
            exploit (HAS tsk0); [by done | | move => [R0 INbounds0]].
            {
              move: INTERF0 => /andP [HP INTER].
              apply/andP; split; first by done.
              move: INTER => /existsP [cpu /andP [IN1 IN2]].
              by apply/existsP; exists cpu; rewrite IN2 andbT; apply SUBSET.
            }
            by exists (tsk0, R0).
          }
          apply ltn_div_trunc with (d := #|alpha' tsk|); first by apply NONEMPTY.
          rewrite -(ltn_add2l (task_cost tsk)) -REC.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by rewrite REC; apply leq_addr.
          rewrite leq_divRL; last by apply NONEMPTY.
          apply EXCEEDS, SUB.
          apply leq_trans with (n := X * #|alpha tsk|); last by rewrite ALLBUSY.
          by rewrite leq_mul2r; apply/orP; right; apply TOOMUCH.
        Qed.

        (* 10) After concluding that the sum of the minima exceeds (R - e_i + 1),
              we prove that there exists a tuple (tsk_k, R_k) that satisfies
              min (x_k, R - e_i + 1) > min (W_k, R - e_i + 1).
              This implies that x_k > W_k, which is of course a contradiction,
              since W_k is a valid task interference bound. *)
        Lemma bertogna_fp_exists_task_that_exceeds_bound :
          exists tsk_k R_k,
            (tsk_k, R_k) \in hp_bounds /\
            (minn (x tsk_k) (R - task_cost tsk + 1) >
              minn (workload_bound tsk_k R_k) (R - task_cost tsk + 1)).
        Proof.
          assert (HAS: has (fun tup : task_with_response_time =>
                               let (tsk_k, R_k) := tup in
                                 (minn (x tsk_k) (R - task_cost tsk + 1) >
                                  minn (workload_bound tsk_k R_k)(R - task_cost tsk + 1)))
                              hp_bounds).
            {
              apply/negP; unfold not; intro NOTHAS.
              move: NOTHAS => /negP /hasPn ALL.
              have SUM := bertogna_fp_sum_exceeds_total_interference.
              rewrite -[_ < _]negbK in SUM.
              move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
              unfold total_interference_bound_fp.
              rewrite big_seq_cond.
              rewrite [\sum_(i <- _| let '(tsk_other,_) := i in _)_]big_seq_cond.
              apply leq_sum; move => [tsk_k R_k /andP [IN INTERk]].
              specialize (ALL (tsk_k, R_k)); simpl in ALL.
              by rewrite leqNgt; apply ALL, IN.
            }
          move: HAS => /hasP HAS; destruct HAS as [[tsk_k R_k] HPk MIN].
          by exists tsk_k, R_k; repeat split.
        Qed.

      End DerivingContradiction.

    End Lemmas.
    
    (* Using the lemmas above, we prove that R bounds the response time of tsk. *)
    Theorem bertogna_cirinei_response_time_bound_fp :
      response_time_bounded_by tsk R.
    Proof.
      have EX := bertogna_fp_exists_task_that_exceeds_bound.
      have WORKLOAD := bertogna_fp_workload_bounds_interference.
      rename H_response_time_bounds_ge_cost into GE_COST,
             H_interfering_tasks_miss_no_deadlines into NOMISS,
             H_response_time_recurrence_holds into REC,
             H_response_time_of_interfering_tasks_is_known into RESP,
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
      unfold minn at 1 in LTmin.
      specialize (WORKLOAD j tsk_k R_k HPk).
      destruct (W task_cost task_period tsk_k R_k R < R - task_cost tsk + 1); rewrite leq_min in LTmin; 
        last by move: LTmin => /andP [_ BUG]; rewrite ltnn in BUG.
      move: LTmin => /andP [BUG _]; des.
      apply leq_trans with (p := W task_cost task_period tsk_k R_k R) in BUG; last by done.
      by rewrite ltnn in BUG.
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.