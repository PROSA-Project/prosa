Require Import prosa.classic.util.all prosa.classic.util.find_seq
               .
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.schedule.uni.basic.platform_tdma
               prosa.classic.model.arrival.basic.task prosa.classic.model.policy_tdma.
Require Import prosa.classic.model.schedule.uni.schedule prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.priority
               prosa.classic.analysis.uni.basic.tdma_rta_theory
               prosa.classic.analysis.uni.basic.tdma_wcrt_analysis.
Require Import prosa.classic.implementation.job prosa.classic.implementation.task
               prosa.classic.implementation.arrival_sequence
               prosa.classic.implementation.uni.basic.schedule_tdma.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Set Bullet Behavior "Strict Subproofs".
Module ResponseTimeAnalysisExemple.

  Import Job ArrivalSequence UniprocessorSchedule SporadicTaskset Schedulability Priority
         ResponseTimeAnalysisTDMA PolicyTDMA  Platform_TDMA.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence  BigOp
         ConcreteSchedulerTDMA WCRT_OneJobTDMA.
 

  Section ExampleTDMA.

    Context {Job: eqType}.

    Let tsk1 := {| task_id := 1; task_cost := 1; task_period := 16; task_deadline := 15|}.
    Let tsk2 := {| task_id := 2; task_cost := 1; task_period := 8; task_deadline := 5|}.
    Let tsk3 := {| task_id := 3; task_cost := 1; task_period := 9; task_deadline := 6|}.



    Let time_slot1 := 1.
    Let time_slot2 := 4.
    Let time_slot3 := 3.

    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.

    Let slot_seq := [::(tsk1,time_slot1);(tsk2,time_slot2);(tsk3,time_slot3)].

    Fact ts_has_valid_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Proof.
      intros tsk tskIN.
      repeat (move: tskIN => /orP [/eqP EQ | tskIN]; subst; compute); by done.
    Qed.

    Let arr_seq := periodic_arrival_sequence ts.

    Fact job_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Proof.
    apply periodic_arrivals_are_consistent.
    Qed.


    Definition time_slot task:=
      if task \in (map fst slot_seq) then 
      let  n:= find (fun tsk => tsk==task)(map fst slot_seq) in
       nth n (map snd slot_seq) n else 0. 


    Fact valid_time_slots:
      forall tsk, tsk \in ts ->
        is_valid_time_slot tsk time_slot.
    Proof.
    apply/allP. by cbn.
    Qed.

    Definition slot_order task1 task2:=
      task_id task1 >= task_id task2.


    Let sched:=
      scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order.

    Let job_in_time_slot t j:=
      Task_in_time_slot ts slot_order (job_task j) time_slot t.

    Fact slot_order_total:
      slot_order_is_total_over_task_set ts slot_order.
    Proof.
    intros t1 t2 IN1 IN2. rewrite /slot_order.
    case LEQ: (_ <= _);first by left. 
    right;move/negP /negP in LEQ;rewrite -ltnNge in LEQ;auto.
    Qed.

    Fact slot_order_transitive:
      slot_order_is_transitive slot_order.
    Proof.
    rewrite /slot_order.
    intros t1 t2 t3 IN1 IN2. ssromega.
    Qed.

    Fact slot_order_antisymmetric:
      slot_order_is_antisymmetric_over_task_set ts slot_order.
    Proof.
    intros x y IN1 IN2. rewrite /slot_order. intros O1 O2.
    have EQ: task_id x = task_id y by ssromega.
    case (x==y)eqn:XY;move/eqP in XY;auto.
    repeat (move:IN2=> /orP [/eqP TSK2 |IN2]); repeat (move:IN1=>/orP [/eqP TSK1|IN1];subst);compute ;try done.
    Qed.

    Fact respects_TDMA_policy:
      Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts time_slot slot_order.
    Proof.
    intros j t ARRJ.
    split.
    - rewrite /sched_implies_in_slot /scheduled_at /sched scheduler_uses_construction_function /job_to_schedule.
      move => /eqP FUN. unfold job_in_time_slot.
      apply findP_in_seq in FUN.
      by destruct FUN as [ TskInSlot _].
      apply job_arrival_times_are_consistent.
    - rewrite /backlogged_implies_not_in_slot_or_other_job_sched /backlogged /scheduled_at /sched scheduler_uses_construction_function /job_to_schedule.
      move => /andP [PEN NOSCHED]. have NSJ:= NOSCHED.
      apply findP_notSome_in_seq in NOSCHED.
      destruct NOSCHED as [NOIN |EXIST].
      + by left.
      + case (Task_in_time_slot ts slot_order (job_task j) time_slot t) eqn:INSLOT;last by left.
        right. destruct EXIST as [y SOMEY]. exists y. have FIND:=SOMEY. apply findP_in_seq in SOMEY.
        move:SOMEY => [SLOTY YIN]. have ARRY: arrives_in arr_seq y
        by apply pendinglist_jobs_in_arr_seq in YIN.
        have SAMETSK: job_task j = job_task y.
        have EQ:Task_in_time_slot ts slot_order (job_task y) time_slot t =
                  Task_in_time_slot ts slot_order (job_task j) time_slot t by rewrite INSLOT. 
        apply task_in_time_slot_uniq with (ts0:= ts) (t0:=t) (slot_order:=slot_order) (task_time_slot:=time_slot);auto.
        intros;by apply slot_order_total.
        by apply slot_order_antisymmetric.
        by apply slot_order_transitive.
        by apply periodic_arrivals_all_jobs_from_taskset.
        by apply valid_time_slots,periodic_arrivals_all_jobs_from_taskset.
        by apply periodic_arrivals_all_jobs_from_taskset.
        by apply valid_time_slots ,periodic_arrivals_all_jobs_from_taskset.
        split;auto.
        * split;case (y==j)eqn:YJ;move/eqP in YJ;try by rewrite FIND YJ in NSJ;move/eqP in NSJ;auto.
          apply pending_job_in_penging_list with (arr_seq0:=arr_seq) in PEN;auto
          ;last apply job_arrival_times_are_consistent.
          apply findP_FIFO with (y0:=j) in FIND;auto. fold sched in FIND.
          apply (respects_FIFO ) in FIND;auto.
          apply periodic_arrivals_are_sporadic with (ts:=ts) in FIND;auto.
          have PERIODY:task_period (job_task y)>0 by
          apply ts_has_valid_parameters,periodic_arrivals_all_jobs_from_taskset. ssromega.  
          apply  job_arrival_times_are_consistent.
          apply periodic_arrivals_is_a_set,ts_has_valid_parameters.
          split;auto.
          by apply/eqP.
      + apply pending_job_in_penging_list;trivial.
        * by apply job_arrival_times_are_consistent.
      + by apply job_arrival_times_are_consistent.
    Qed.


    Fact job_cost_le_task_cost:
      forall j : concrete_job_eqType,
      arrives_in arr_seq j ->
      job_cost_le_task_cost task_cost job_cost job_task j.
    Proof.
    intros JOB ARR.
    apply periodic_arrivals_valid_job_parameters in ARR.
    apply ARR. by apply ts_has_valid_parameters.
    Qed.


    Let tdma_claimed_bound task:= 
      WCRT task_cost time_slot ts task.
    Let tdma_valid_bound task := is_valid_tdma_bound task_deadline task (tdma_claimed_bound task).

    Fact valid_tdma_bounds:
      forall tsk, tsk \in ts ->
        tdma_valid_bound tsk = true.
    Proof.
    apply/allP.
    rewrite /tdma_valid_bound /tdma_claimed_bound /WCRT /TDMA_cycle.
    rewrite bigopE. by compute.
    Qed.

    Fact WCRT_le_period:
      forall tsk, tsk \in ts ->
      WCRT task_cost time_slot ts tsk <= task_period tsk.
    Proof.
    apply/allP.
    rewrite /tdma_valid_bound /tdma_claimed_bound /WCRT /TDMA_cycle.
    rewrite bigopE. by compute.
    Qed.


    Let no_deadline_missed_by :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.

    Theorem ts_is_schedulable_by_tdma :
      forall tsk, tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
    intros tsk tskIN.
    have VALID_JOB := periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters.
    apply taskset_schedulable_by_tdma with (task_deadline:=task_deadline)(task_period:=task_period) 
    (tsk0:=tsk)(ts0:=ts)(task_cost:=task_cost)
    (task_time_slot:=time_slot) (slot_order:= slot_order)
    (arr_seq0:=arr_seq).
    - apply job_arrival_times_are_consistent.
    - apply periodic_arrivals_are_sporadic.
    - apply scheduler_jobs_must_arrive_to_execute.
      apply job_arrival_times_are_consistent.
    - apply scheduler_completed_jobs_dont_execute.
      apply job_arrival_times_are_consistent.
    - assumption.
    - by apply WCRT_le_period.
    - by apply respects_TDMA_policy.
    - by apply valid_time_slots.
    - assumption.
    - by apply job_cost_le_task_cost.
    - apply valid_tdma_bounds;auto.
    Qed.

  End ExampleTDMA.

End ResponseTimeAnalysisExemple.




