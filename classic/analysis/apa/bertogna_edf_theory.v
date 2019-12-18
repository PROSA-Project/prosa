Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.workload prosa.classic.model.schedule.global.response_time
               prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.apa.platform prosa.classic.model.schedule.apa.interference
               prosa.classic.model.schedule.apa.affinity prosa.classic.model.schedule.apa.constrained_deadlines.
Require Import prosa.classic.analysis.apa.workload_bound prosa.classic.analysis.apa.interference_bound_edf.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisEDF.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Schedulability ResponseTime
         Priority TaskArrival WorkloadBound InterferenceBoundEDF
         Interference Platform Affinity ConstrainedDeadlines.

  (* In this section, we prove that any fixed point in the APA-reduction of
     Bertogna and Cirinei's RTA for EDF scheduling is a safe response-time bound.
     This result corresponds to Lemma 10 in the revised version of the APA paper:
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

    (* Consider a task set ts where all tasks have valid parameters
       and constrained deadlines, ... *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_constrained_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    (* ... and assume that all jobs in the arrival sequence come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.
    
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

    (* Assume that the schedule is an work-conserving APA schedule that
       respects EDF priorities. *)
    Hypothesis H_respects_affinity: respects_affinity job_task sched alpha.
    Hypothesis H_work_conserving: apa_work_conserving job_arrival job_cost job_task arr_seq
                                                      sched alpha.
    Hypothesis H_edf_policy:
      respects_JLFP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
                                          sched alpha (EDF job_arrival job_deadline).

    (* Let's define some local names to avoid passing many parameters. *)
    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.

    (* Now we consider the response-time recurrence. In the computation of
       the response-time bound, we assume that each task under analysis has
       a non-empty subaffinity alpha'.
       Note that the notation #|...| expresses the cardinality of the set. *)
    Variable alpha': task_affinity sporadic_task num_cpus.
    Hypothesis H_affinity_subset: forall tsk, tsk \in ts -> is_subaffinity (alpha' tsk) (alpha tsk).
    Hypothesis H_at_least_one_cpu : forall tsk, tsk \in ts -> #|alpha' tsk| > 0.
    
    (* Assume that a response-time bound R is known...  *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable rt_bounds: seq task_with_response_time.

    (* ...for any task in the task set, ... *)
    Hypothesis H_rt_bounds_contains_all_tasks: unzip1 rt_bounds = ts.

    (* ... where R is a fixed-point of the response-time recurrence (with
           alpha' as the reduced affinity mask), ... *)
    Let I (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline alpha
                                   tsk (alpha' tsk) rt_bounds delta.
    Hypothesis H_response_time_is_fixed_point :
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        R = task_cost tsk + div_floor (I tsk R) #|alpha' tsk|.
    
    (* ..., and R is no larger than the deadline. *)
    Hypothesis H_tasks_miss_no_deadlines:
      forall tsk R,
        (tsk, R) \in rt_bounds -> R <= task_deadline tsk.

    (* In order to prove that R is a response-time bound, we first provide some lemmas. *)
    Section Lemmas.

      (* Let (tsk, R) be any task to be analyzed, with its response-time bound R. *)
      Variable tsk: sporadic_task.
      Variable R: time.
      Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

      (* Consider any job j of tsk ... *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* ... that did not complete on time, ... *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (job_arrival j + R).

      (* ... and that is the first job not to satisfy its response-time bound. *)
      Hypothesis H_all_previous_jobs_completed_on_time :
        forall j_other tsk_other R_other,
          arrives_in arr_seq j_other ->
          job_task j_other = tsk_other ->
          (tsk_other, R_other) \in rt_bounds ->
          job_arrival j_other + R_other < job_arrival j + R ->
          completed job_cost sched j_other (job_arrival j_other + R_other).

      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_arrival job_cost job_task sched alpha j
                          tsk_other (job_arrival j) (job_arrival j + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R).

      (* Recall Bertogna and Cirinei's workload bound ... *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W task_cost task_period tsk_other R_other R.

      (*... and the EDF-specific bound, ... *)
      Let edf_specific_bound (tsk_other: sporadic_task) (R_other: time) :=
        edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other.

      (* ... which combined form the interference bound. *)
      Let interference_bound (tsk_other: sporadic_task) (R_other: time) :=
        interference_bound_edf task_cost task_period task_deadline tsk R (tsk_other, R_other). 
      
      (* Based on the definition of a different task in subaffinity alpha', ... *)
      Let other_task_in alpha' := different_task_in alpha tsk alpha'.

      (* ...let (other_tasks_in alpha') denote the set of tasks that are different from tsk
         and that can be scheduled on subaffinity alpha'. *)
      Let other_tasks_in alpha' :=
        [seq tsk_other <- ts | other_task_in (alpha' tsk) tsk_other].

      (* Now we establish results the interfering tasks. *)
      Section LemmasAboutInterferingTasks.
        
        (* Let (tsk_other, R_other) be any pair of higher-priority task and
           response-time bound computed in previous iterations. *)
        Variable tsk_other: sporadic_task.
        Variable R_other: time.
        Hypothesis H_response_time_of_tsk_other: (tsk_other, R_other) \in rt_bounds.

        (* Note that tsk_other is in the task set, ...*)
        Lemma bertogna_edf_tsk_other_in_ts: tsk_other \in ts.
        Proof.
          by rewrite set_mem -H_rt_bounds_contains_all_tasks; apply/mapP; exists (tsk_other, R_other).
        Qed.

        (* ... and R_other is larger than the cost of tsk_other. *)
        Lemma bertogna_edf_R_other_ge_cost :
          R_other >= task_cost tsk_other.
        Proof.
          by rewrite [R_other](H_response_time_is_fixed_point tsk_other);
            first by apply leq_addr.
        Qed.

        (* Since tsk_other cannot interfere more than it executes, we show that
           the interference caused by tsk_other is no larger than workload bound W. *)
        Lemma bertogna_edf_workload_bounds_interference :
          x tsk_other <= workload_bound tsk_other R_other.
        Proof.
          unfold valid_sporadic_job in *.
          rename H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_valid_job_parameters into PARAMS,
                 H_valid_task_parameters into TASK_PARAMS,
                 H_constrained_deadlines into RESTR,
                 H_tasks_miss_no_deadlines into NOMISS.
          unfold x, task_interference.
          have INts := bertogna_edf_tsk_other_in_ts.
          apply leq_trans with (n := workload job_task sched tsk_other
                                         (job_arrival j) (job_arrival j + R));
            first by apply task_interference_le_workload.
          by apply workload_bounded_by_W with (task_deadline0 := task_deadline)
             (job_arrival0 := job_arrival) (arr_seq0 := arr_seq)
             (job_cost0 := job_cost) (job_deadline0 := job_deadline); try (by ins); last 2 first;
            [ by apply bertogna_edf_R_other_ge_cost
            | by ins; apply NOMISS
            | by ins; apply TASK_PARAMS
            | by ins; apply RESTR
            | by ins; apply BEFOREok with (tsk_other := tsk_other)].
        Qed.

        (* Recall that the edf-specific interference bound also holds for tsk_other. *)
        Lemma bertogna_edf_specific_bound_holds :
          x tsk_other <= edf_specific_bound tsk_other R_other.
        Proof.
          apply interference_bound_edf_bounds_interference with
              (job_deadline0 := job_deadline)
              (arr_seq0 := arr_seq) (ts0 := ts); try (by done);
            [ by apply bertogna_edf_tsk_other_in_ts | 
                by apply H_tasks_miss_no_deadlines | ].
            by ins; apply H_all_previous_jobs_completed_on_time with (tsk_other := tsk_other). 
        Qed.
        
      End LemmasAboutInterferingTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.

      (* 0) Since job j did not complete by its response time bound, it follows that
            the total interference X exceeds  R - e_k + 1. *)
      Lemma bertogna_edf_too_much_interference : X >= R - task_cost tsk + 1.
      Proof.
        rename H_completed_jobs_dont_execute into COMP,
               H_valid_job_parameters into PARAMS, H_response_time_is_fixed_point into REC,
               H_job_of_tsk into JOBtsk, H_j_not_completed into NOTCOMP.
        unfold completed, valid_sporadic_job in *.
        unfold X, total_interference; rewrite addn1.
        rewrite -(ltn_add2r (task_cost tsk)).
        rewrite subh1; last by rewrite [R](REC tsk) // leq_addr.
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
      Lemma bertogna_edf_interference_by_different_tasks :
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
               H_tsk_R_in_rt_bounds into INbounds,
               H_all_previous_jobs_completed_on_time into BEFOREok,
               H_tasks_miss_no_deadlines into NOMISS,
               H_constrained_deadlines into RESTR.
        move => t j_other /andP [LEt GEt] ARRother BACK SCHED.
        apply/eqP; red; intro SAMEtsk.
        move: SCHED => /existsP [cpu SCHED].
        assert (SCHED': scheduled sched j_other t).
          by apply/existsP; exists cpu.
        clear SCHED; rename SCHED' into SCHED.
        move: (SCHED) => PENDING.
        apply scheduled_implies_pending with (job_arrival0 := job_arrival) (job_cost0 := job_cost)
           in PENDING; try (by done).
        destruct (ltnP (job_arrival j_other) (job_arrival j)) as [BEFOREother | BEFOREj].
         {
          move: (BEFOREother) => LT; rewrite -(ltn_add2r R) in LT.
          specialize (BEFOREok j_other tsk R ARRother SAMEtsk INbounds LT).
          move: PENDING => /andP [_ /negP NOTCOMP]; apply NOTCOMP.
          apply completion_monotonic with (t0 := job_arrival j_other + R); try (by done).
          apply leq_trans with (n := job_arrival j); last by done.
          apply leq_trans with (n := job_arrival j_other + task_deadline tsk);
            first by rewrite leq_add2l; apply NOMISS.
          apply leq_trans with (n := job_arrival j_other + task_period tsk);
            first by rewrite leq_add2l; apply RESTR; rewrite -JOBtsk FROMTS.
          rewrite -SAMEtsk; apply SPO; try (by done); [ | by rewrite JOBtsk | by apply ltnW].
          by red; intro EQ; subst; rewrite ltnn in BEFOREother.
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
          by red; intros EQtsk; subst; rewrite /backlogged SCHED andbF in BACK.
        }
      Qed.
        
      (* 2) In order to use the lemmas in constrained_deadlines.v, we show that
            all jobs released before the end of the interval complete by their
            periods. This follows trivially from the hypothesis that all jobs
            before (job_arrival j + R) complete by their response-time bounds. 
            With this lemma, we can conclude that during job j's scheduling
            window there cannot be multiple pending jobs of each task.*)
      Lemma bertogna_edf_all_previous_jobs_complete_by_their_period:
        forall t j0,
          arrives_in arr_seq j0 ->
          t < job_arrival j + R ->
          job_arrival j0 + task_period (job_task j0) <= t ->
          completed job_cost sched j0
             (job_arrival j0 + task_period (job_task j0)).
      Proof.
        rename H_rt_bounds_contains_all_tasks into UNZIP,
               H_constrained_deadlines into CONSTR,
               H_tasks_miss_no_deadlines into NOMISS,
               H_all_jobs_from_taskset into FROMTS,
               H_all_previous_jobs_completed_on_time into BEFOREok.
        intros t j0 ARR0 LEt LE.
        cut ((job_task j0) \in unzip1 rt_bounds = true); last by rewrite UNZIP FROMTS.
        move => /mapP [p IN EQ]; destruct p as [tsk' R0]; simpl in *; subst tsk'.
        apply completion_monotonic with (t0 := job_arrival j0 + R0).
        {
          rewrite leq_add2l; apply leq_trans with (n := task_deadline (job_task j0));
            [by apply NOMISS | by apply CONSTR; rewrite FROMTS].
        }
        apply BEFOREok with (tsk_other := (job_task j0)); try by done.
        apply leq_ltn_trans with (n := t); last by done.
        apply leq_trans with (n := job_arrival j0 + task_period (job_task j0)); last by done.
        by rewrite leq_add2l; apply leq_trans with (n := task_deadline (job_task j0));
          [by apply NOMISS | apply CONSTR; rewrite FROMTS].
      Qed.

      (* 3) Next, we prove that the sum of the interference of each task is equal to the
            total interference multiplied by the number of processors in tsk's *actual*
            affinity. This holds because interference only occurs when all processors in
            the affinity are busy.
            With this lemma we can relate per-task interference with the total interference
            incurred by j (backlogged time). *)
      Lemma bertogna_edf_all_cpus_in_affinity_busy :
        \sum_(tsk_k <- other_tasks_in alpha) x tsk_k = X * #|alpha tsk|.
      Proof.
        have DIFFTASK := bertogna_edf_interference_by_different_tasks.
        rename H_all_jobs_from_taskset into FROMTS,
               H_valid_task_parameters into PARAMS, H_jobs_come_from_arrival_sequence into FROMSEQ,
               H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
               H_work_conserving into WORK,
               H_tsk_R_in_rt_bounds into INbounds,
               H_all_previous_jobs_completed_on_time into BEFOREok,
               H_tasks_miss_no_deadlines into NOMISS,
               H_rt_bounds_contains_all_tasks into UNZIP,
               H_constrained_deadlines into RESTR,
               H_respects_affinity into APA.
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
        have ARRother: arrives_in arr_seq j_other.
          by apply (FROMSEQ j_other t); apply/existsP; exists cpu; apply/eqP.
        rewrite (bigD1_seq (job_task j_other)) /=; last by rewrite filter_uniq; destruct ts.
        {
          rewrite (eq_bigr (fun i => 0));
            last by intros i DIFF; rewrite /task_scheduled_on SCHED;apply/eqP;rewrite eqb0 eq_sym.
          rewrite big_const_seq iter_addn mul0n 2!addn0; apply/eqP; rewrite eqb1.
          by unfold task_scheduled_on; rewrite SCHED.
        }
        rewrite mem_filter; apply/andP; split; last by apply FROMTS.
        unfold different_task_in, affinity_intersects.
        apply/andP; split; last first.
        {
          apply/existsP; exists cpu; rewrite -JOBtsk ALPHA andTb.
          by apply APA with (t := t); apply/eqP.
        }
        apply DIFFTASK with (t := t); try (by done); first by auto.
        by apply/existsP; exists cpu; apply/eqP.
      Qed.

      (* 4) Recall that the reduction-based analysis considers only the interfering tasks
            within subaffinity (alpha' tsk), as opposed to (alpha tsk). Therefore, we must
            reason about the task interference wihin (alpha' tsk).
            We begin by showing that the cumulative interference within (alpha' tsk) is at
            least the total interference multiplied by the number of processors in (alpha' tsk). *)
      Lemma bertogna_edf_all_cpus_in_subaffinity_busy :
        \sum_(tsk_k <- other_tasks_in alpha') x tsk_k >= X * #|alpha' tsk|.
      Proof.
        have DIFFTASK := bertogna_edf_interference_by_different_tasks.
        rename H_all_jobs_from_taskset into FROMTS,
               H_valid_task_parameters into PARAMS,
               H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
               H_work_conserving into WORK,
               H_tsk_R_in_rt_bounds into INbounds,
               H_all_previous_jobs_completed_on_time into BEFOREok,
               H_tasks_miss_no_deadlines into NOMISS,
               H_rt_bounds_contains_all_tasks into UNZIP,
               H_constrained_deadlines into RESTR,
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
          by apply (H_jobs_come_from_arrival_sequence j_other t); apply/existsP; exists cpu; apply/eqP.
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
          apply DIFFTASK with (t := t); try (by done); first by auto.
          by apply/existsP; exists cpu; apply/eqP.
        }
      Qed.
      
      (* Let's define a predicate for whether a task is scheduled on (alpha tsk). *)
      Let scheduled_on_alpha_tsk := fun t tsk_k =>
        task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t.
      
      (* 5) Now we prove that, at all times that j is backlogged, the number
            of tasks whose affinity intersects (alpha' tsk) that are in fact
            scheduled on (alpha' tsk) is at least the size of (alpha' tsk).
            This is required to prove lemma (6). *)
      Lemma bertogna_edf_alpha'_is_full:
        forall t,
          job_arrival j <= t < job_arrival j + R ->
          backlogged job_arrival job_cost sched j t ->
          count (scheduled_on_alpha_tsk t) (other_tasks_in alpha') >= #|alpha' tsk|.
      Proof.
        have COMP := bertogna_edf_all_previous_jobs_complete_by_their_period.       
        rename H_work_conserving into WORK, H_respects_affinity into APA,
               H_affinity_subset into SUB, H_job_of_tsk into JOBtsk,
               H_all_jobs_from_taskset into FROMTS, H_jobs_come_from_arrival_sequence into FROMSEQ,
               H_valid_task_parameters into PARAMS,
               H_sequential_jobs into SEQ.
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
          feed (WORK cpu); first by apply SUB; rewrite ?FROMTS ?JOBtsk.
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
              destruct (sched cpu1 t) as [j0|] eqn:SCHED1; symmetry in SCHED2;
                first by apply SEQ with (j := j0) (t := t).
              rewrite 2!mem_enum in IN1 IN2.
              exploit (WORK cpu1); first by apply SUB; rewrite ?FROMTS ?JOBtsk.
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
              apply platform_at_most_one_pending_job_of_each_task with (task_cost0 := task_cost)
              (task_period0 := task_period) (task_deadline0 := task_deadline) (tsk0 := tsk)
              (job_cost0 := job_cost) (job_task0 := job_task) (sched0 := sched) (j0 := j) (t0 := t)
              (job_arrival0 := job_arrival) (arr_seq0 := arr_seq);
                rewrite ?JOBtsk ?SAMEtsk //; first by apply PARAMS; rewrite -JOBtsk FROMTS.
              intros j0 tsk0 ARR0 TSK0 LE.
              by apply (COMP t); rewrite ?TSK0.
            }
          }
          {
            move => tsk' /mapP [j' IN EQtsk'].
            rewrite mem_pmap in IN.
            move: IN => /mapP [cpu INcpu SCHED'].
            rewrite mem_enum in INcpu.
            rewrite mem_filter; apply/andP; split.
            {
              apply/existsP; exists cpu; apply/andP; split;
                 first by apply SUB; rewrite -?JOBtsk ?FROMTS ?JOBtsk.
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
            {
              apply/eqP; intro SAMEtsk.
              move: BACK => /andP [PENDING NOTSCHED].
              assert (SCHEDULED': scheduled sched j' t).
              {
                by apply/existsP; exists cpu; rewrite /scheduled_on -SCHED'.
              }
              move: (SCHEDULED') => PENDING'.
              apply scheduled_implies_pending with (job_cost0 := job_cost) (job_arrival0:=job_arrival)
                in PENDING'; try by done.
              assert (BUG: j = j').
              {
                apply platform_at_most_one_pending_job_of_each_task with (task_cost0 := task_cost)
                (task_period0 := task_period) (task_deadline0 := task_deadline) (tsk0 := tsk)
                (job_cost0 := job_cost) (job_task0 := job_task) (sched0 := sched) (j0 := j) (t0 := t)
                (job_arrival0 := job_arrival) (arr_seq0 := arr_seq);
                  rewrite ?JOBtsk ?SAMEtsk //; first by apply PARAMS; rewrite -JOBtsk FROMTS.
                intros j0 tsk0 ARR0 TSK0 LE.
                by apply (COMP t); rewrite ?TSK0.
              }
              by rewrite BUG SCHEDULED' in NOTSCHED.
            }
          }
        }
      Qed.

      (* Before stating the next lemma, let (num_tasks_exceeding delta) be the
         number of interfering tasks that can execute on (alpha' tsk) whose
         interference x is larger than delta. *)
      Let num_tasks_exceeding delta := count (fun i => x i >= delta) (other_tasks_in alpha').

      (* 6) Now we prove that, for any delta, if (num_task_exceeding delta > 0), then the
            cumulative interference caused by the complementary set of interfering tasks fills
            the remaining, not-completely-full (#|alpha' tsk| - num_tasks_exceeding delta)
            processors. *)
      Lemma bertogna_edf_interference_in_non_full_processors :
        forall delta,
          0 < num_tasks_exceeding delta < #|alpha' tsk| ->
          \sum_(i <- other_tasks_in alpha' | x i < delta) x i >= delta * (#|alpha' tsk| - num_tasks_exceeding delta).
      Proof.
        have COMP := bertogna_edf_all_previous_jobs_complete_by_their_period.
        have ATMOST := platform_at_most_one_pending_job_of_each_task.
        have INV := bertogna_edf_alpha'_is_full.
        rename H_all_jobs_from_taskset into FROMTS,
               H_valid_task_parameters into PARAMS,
               H_job_of_tsk into JOBtsk, H_jobs_come_from_arrival_sequence into FROMSEQ,
               H_sporadic_tasks into SPO,
               H_tsk_R_in_rt_bounds into INbounds,
               H_all_previous_jobs_completed_on_time into BEFOREok,
               H_tasks_miss_no_deadlines into NOMISS,
               H_constrained_deadlines into RESTR,
               H_sequential_jobs into SEQ.
        unfold sporadic_task_model in *.
        move => delta /andP [HAS LT]. 
        rewrite -has_count in HAS.

        set some_interference_A := fun t =>
          has (fun tsk_k => backlogged job_arrival job_cost sched j t &&
                            (x tsk_k >= delta) &&
                            scheduled_on_alpha_tsk t tsk_k)
            (other_tasks_in alpha').
        set total_interference_B := fun t =>
            backlogged job_arrival job_cost sched j t *
            count (fun tsk_k => (x tsk_k < delta) &&
                  scheduled_on_alpha_tsk t tsk_k) (other_tasks_in alpha').

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
            apply platform_at_most_one_pending_job_of_each_task with (task_cost0 := task_cost)
              (task_period0 := task_period) (task_deadline0 := task_deadline) (tsk0 := tsk)
              (job_cost0 := job_cost) (job_task0 := job_task) (sched0 := sched) (j0 := j) (t0 := t)
              (job_arrival0 := job_arrival) (arr_seq0 := arr_seq);
              rewrite ?JOBtsk ?SAMEtsk //; first by apply PARAMS; rewrite -JOBtsk FROMTS.
            intros j0 tsk0 ARR0 TSK0 LE.
            by apply (COMP t); rewrite ?TSK0.
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
                     scheduled_on_alpha_tsk t tsk_k) (other_tasks_in alpha')) eqn:HAS';
            last by done.
          rewrite mul1n; move: HAS => /hasP [tsk_k INk LEk].
          unfold num_tasks_exceeding.
          apply leq_trans with (n := #|alpha' tsk| -
                       count (fun i => (x i >= delta) &&
                          scheduled_on_alpha_tsk t i) (other_tasks_in alpha')).
          {
            apply leq_sub2l.
            rewrite -2!sum1_count big_mkcond /=.
            rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
            apply leq_sum; intros i _.
            by destruct (scheduled_on_alpha_tsk t i);
              [by rewrite andbT | by rewrite andbF].
          }
          rewrite -count_filter -[count _ (other_tasks_in _)]count_filter.
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
          rewrite big_mkcond [\sum_(i <- other_tasks_in alpha' | _ < _) _]big_mkcond /=.
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
      Lemma bertogna_edf_minimum_exceeds_interference :
        forall delta,
          \sum_(tsk_k <- other_tasks_in alpha') x tsk_k >= delta * #|alpha' tsk| ->
             \sum_(tsk_k <- other_tasks_in alpha') minn (x tsk_k) delta >=
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
        destruct (~~ has (fun i => delta <= x i) (other_tasks_in alpha')) eqn:HASa.
        {
          rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
          rewrite big_seq_cond; move: HASa => /hasPn HASa.
          rewrite add0n (eq_bigl (fun i => (i \in other_tasks_in alpha') && true));
            last by red; intros tsk_k; destruct (tsk_k \in other_tasks_in alpha') eqn:INk;
              [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
          by rewrite -big_seq_cond.
        } apply negbFE in HASa.
        
        (* Case 2: num_tasks_exceeding >= #|alpha' tsk| *)
        destruct (num_tasks_exceeding delta >= #|alpha' tsk|) eqn:CARD.
        {
          apply leq_trans with (delta * num_tasks_exceeding delta);
            first by rewrite leq_mul2l; apply/orP; right.
          unfold num_tasks_exceeding; rewrite -sum1_count big_distrr /=.
          rewrite -[\sum_(_ <- _ | _) _]addn0.
          by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
        } apply negbT in CARD; rewrite -ltnNge in CARD.

        (* Case 3: num_tasks_exceeding < #|alpha' tsk| *)
        rewrite big_const_seq iter_addn addn0; fold num_tasks_exceeding.
        apply leq_trans with (n := delta * num_tasks_exceeding delta +
                                   delta * (#|alpha' tsk| - num_tasks_exceeding delta));
          first by rewrite -mulnDr subnKC //; apply ltnW.
        rewrite leq_add2l bertogna_edf_interference_in_non_full_processors //.
        by apply/andP; split; [by rewrite -has_count | by done].
      Qed.

      (* 8) Note that lemma (7) only refers to interference within subaffinity (alpha' tsk).
            To reason about the interference incurred by job j in its complete affinity,
            we prove that an exceeding interference on affinity (alpha tsk) also
            implies an exceeding interference on the subaffinity (alpha' tsk). *)
      Lemma bertogna_edf_interference_on_subaffinity :
        forall delta,
          \sum_(tsk_k <- other_tasks_in alpha) x tsk_k >= delta * #|alpha tsk| ->
          \sum_(tsk_k <- other_tasks_in alpha') x tsk_k >= delta * #|alpha' tsk|.
      Proof.
        have ALL := bertogna_edf_all_cpus_in_affinity_busy.
        have SUB := bertogna_edf_all_cpus_in_subaffinity_busy.
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
      Lemma bertogna_edf_sum_exceeds_total_interference:
        \sum_((tsk_other, R_other) <- rt_bounds | other_task_in (alpha' tsk) tsk_other)
          minn (x tsk_other) (R - task_cost tsk + 1) > I tsk R.
      Proof.
        have GE_COST := bertogna_edf_R_other_ge_cost.
        have EXCEEDS := bertogna_edf_minimum_exceeds_interference.
        have SUB := bertogna_edf_interference_on_subaffinity.
        have ALLBUSY := bertogna_edf_all_cpus_in_affinity_busy.
        have TOOMUCH := bertogna_edf_too_much_interference.
        rename H_rt_bounds_contains_all_tasks into UNZIP,
               H_job_of_tsk into JOBtsk,
               H_all_jobs_from_taskset into FROMTS,
               H_response_time_is_fixed_point into REC.
        apply leq_trans with (n := \sum_(tsk_other <- other_tasks_in alpha')
                                     minn (x tsk_other) (R - task_cost tsk + 1));
          last first.
        {
          rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
            last by ins; destruct i.
          assert (FILTER: filter (other_task_in (alpha' tsk)) (unzip1 rt_bounds) =
                          filter (other_task_in (alpha' tsk)) ts).
            by f_equal.
          unfold other_tasks_in; rewrite -FILTER; clear FILTER.
          rewrite -[\sum_(_ <- rt_bounds | _)_]big_filter.
          assert (SUBST: [seq i <- rt_bounds
                 | let '(tsk_other, _) := i in
                   other_task_in (alpha' tsk) tsk_other] =
                         [seq i <- rt_bounds
                           | other_task_in (alpha' tsk) (fst i)]).
          {
            by apply eq_filter; red; intro i; destruct i.
          } rewrite SUBST; clear SUBST.         
          have MAP := big_map (fun x => fst x) (fun i => true)
                              (fun i => minn (x i) (R - task_cost tsk + 1)).
          by rewrite -MAP; apply eq_leq; f_equal; rewrite filter_map.
        }
        
        apply ltn_div_trunc with (d := #|alpha' tsk|);
          first by apply H_at_least_one_cpu; rewrite -JOBtsk FROMTS.
        rewrite -(ltn_add2l (task_cost tsk)) -REC; last first. by done.
        rewrite -addn1 -leq_subLR.
        rewrite -[R + 1 - _]subh1; last by apply GE_COST.
        rewrite leq_divRL;
          last by apply H_at_least_one_cpu; rewrite -JOBtsk FROMTS.
        apply EXCEEDS, SUB.
        apply leq_trans with (n := X * #|alpha tsk|); last by rewrite ALLBUSY.
        by rewrite leq_mul2r; apply/orP; right; apply TOOMUCH.
      Qed.

      (* 10) After concluding that the sum of the minima exceeds (R - e_i + 1),
            we prove that there exists a tuple (tsk_k, R_k) that satisfies
            min (x_k, R - e_i + 1) > min (W_k, I_edf, R - e_i + 1).
            This implies that either x_k > W_k or x_k > I_edf, which is a contradiction,
            since both W_k and I_edf are valid task interference bounds. *)
      Lemma bertogna_edf_exists_task_that_exceeds_bound :
        exists tsk_other R_other,
          (tsk_other, R_other) \in rt_bounds /\
          (minn (x tsk_other) (R - task_cost tsk + 1) > interference_bound tsk_other R_other).
      Proof.
        have SUM := bertogna_edf_sum_exceeds_total_interference.
        have BOUND := bertogna_edf_workload_bounds_interference.
        have EDFBOUND := bertogna_edf_specific_bound_holds.
        rename H_rt_bounds_contains_all_tasks into UNZIP.
        assert (HAS: has (fun tup : task_with_response_time =>
                            let (tsk_other, R_other) := tup in
                (tsk_other \in ts) && other_task_in (alpha' tsk) tsk_other &&
                (minn (x tsk_other) (R - task_cost tsk + 1)  > interference_bound tsk_other R_other))
                         rt_bounds).
        {
          apply/negP; unfold not; intro NOTHAS.
          move: NOTHAS => /negP /hasPn ALL.
          rewrite -[_ < _]negbK in SUM.
          move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
          unfold I, total_interference_bound_edf.
          rewrite big_seq_cond [X in _ <= X]big_seq_cond.
          apply leq_sum; move => tsk_k /andP [INBOUNDSk INTERFk]; destruct tsk_k as [tsk_k R_k].
          specialize (ALL (tsk_k, R_k) INBOUNDSk).
          unfold interference_bound_edf; simpl in *.
          rewrite leq_min; apply/andP; split.
          {
            unfold interference_bound; rewrite leq_min; apply/andP; split;
              last by rewrite geq_minr.
            by apply leq_trans with (n := x tsk_k);
              [by rewrite geq_minl | by apply BOUND].
          }
          {
            apply leq_trans with (n := x tsk_k);
              [by rewrite geq_minl | by apply EDFBOUND].
          }
        }
        move: HAS => /hasP HAS; destruct HAS as [[tsk_k R_k] HPk MIN].
        move: MIN => /andP [/andP [INts INTERFk] MINk].
        by exists tsk_k, R_k; repeat split.
      Qed.

      End DerivingContradiction.
      
    End Lemmas.

    (* Using the lemmas above, we now prove that any response-time bound
       obtained from the analysis is safe. *)
    Section MainProof.
      
      (* Let (tsk, R) be any task to be analyzed, with its response-time bound R. *)
      Variable tsk: sporadic_task.
      Variable R: time.
      Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

      (* Then, R bounds the response-time of tsk. *)
      Theorem bertogna_cirinei_response_time_bound_edf :
        response_time_bounded_by tsk R.
      Proof.
        intros j ARRj JOBtsk.
       
        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        remember (job_arrival j + R) as ctime.

        revert H_tsk_R_in_rt_bounds.
        generalize dependent R; generalize dependent tsk; generalize dependent j.
      
        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime IH] using strong_ind.

        intros j ARRj tsk' JOBtsk R' EQc INbounds; subst ctime.

        (* First, let's simplify the induction hypothesis. *)
        assert (BEFOREok: forall j0 tsk R0,
                            arrives_in arr_seq j0 ->
                            job_task j0 = tsk ->
                            (tsk, R0) \in rt_bounds ->
                            job_arrival j0 + R0 < job_arrival j + R' ->
                            service sched j0 (job_arrival j0 + R0) >= job_cost j0).
        {
            by ins; apply IH with (tsk := tsk0) (R := R0).
        }
        clear IH.
        
        (* The proof follows by contradiction. Assume that job j does not complete by its
           response-time bound. By the induction hypothesis, all jobs with absolute
           response-time bound t < (job_arrival j + R) have correct response-time bounds. *)
        destruct (completed job_cost sched j (job_arrival j + R')) eqn:NOTCOMP;
          first by done.
        apply negbT in NOTCOMP; exfalso.
        
        (* Next, we derive a contradiction using the previous lemmas. *)
        exploit (bertogna_edf_exists_task_that_exceeds_bound tsk' R' INbounds j ARRj JOBtsk NOTCOMP).
        {
          by ins; apply IH with (tsk := tsk_other) (R := R_other).
        } 
        intro EX; destruct EX as [tsk_other [R_other [HP LTmin]]].
        unfold interference_bound_edf, interference_bound_generic in LTmin.
        rewrite minnAC in LTmin; apply min_lt_same in LTmin.
        have BASICBOUND := bertogna_edf_workload_bounds_interference R' j BEFOREok tsk_other R_other HP.
        have EDFBOUND := (bertogna_edf_specific_bound_holds tsk' R' j ARRj JOBtsk BEFOREok tsk_other R_other HP).
        unfold minn in LTmin; clear -LTmin HP BASICBOUND EDFBOUND tsk; desf.
        {
          by apply (leq_ltn_trans BASICBOUND) in LTmin; rewrite ltnn in LTmin. 
        }
        {
          by apply (leq_ltn_trans EDFBOUND) in LTmin; rewrite ltnn in LTmin.
        }
      Qed.

    End MainProof.
    
  End ResponseTimeBound.

End ResponseTimeAnalysisEDF.