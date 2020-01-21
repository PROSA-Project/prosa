Require Import  prosa.classic.util.all.
Require Import  prosa.classic.model.time
                prosa.classic.model.arrival.basic.task 
                prosa.classic.model.arrival.basic.job.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.

Module PolicyTDMA.

  Import Time.

  (** In this section, we define the TDMA policy.*)
  Section TDMA.
    (* The TDMA policy is based on two properties.
      (1) Each task has a fixed, reserved time slot for execution;
      (2) These time slots are ordered in sequence to form a TDMA cycle, which repeats along the timeline.
      An example of TDMA schedule is illustrated in the following.
      ______________________________
      | s1 |  s2  |s3| s1 |  s2  |s3|...
      --------------------------------------------->
      0                                            t
    *)
    Variable Task: eqType.
    (* With each task, we associate the duration of the corresponding TDMA slot. *)
    Definition TDMA_slot:= Task -> duration.
    (* Moreover, within each TDMA cycle, task slots are ordered according to some relation. *)
    Definition TDMA_slot_order:= rel Task.

  End TDMA.

  (** In this section, we define the properties of TDMA and prove some basic lemmas. *)
  Section PropertiesTDMA.

    Context {Task:eqType}.

    (* Consider any task set ts... *)
    Variable ts: {set Task}.

    (* ...and any slot order (i.e, slot_order slot1 slot2 means that slot1 comes before slot2 in a TDMA cycle). *)
    Variable slot_order: TDMA_slot_order Task.

    (* First, we define the properties of a valid time slot order. *)
    Section Relation.
      (* Time slot order must transitive... *)
      Definition slot_order_is_transitive:= transitive slot_order.

      (* ..., totally ordered over the task set... *)
      Definition slot_order_is_total_over_task_set :=
        total_over_list slot_order ts.

      (* ... and antisymmetric over task set. *)
      Definition slot_order_is_antisymmetric_over_task_set :=
        antisymmetric_over_list slot_order ts. 

    End Relation.

    (* Next, we define some properties of task time slots *)
    Section TimeSlot.

      (* Consider any task in task set ts*)
      Variable task: Task.
      Hypothesis H_task_in_ts: task \in ts. 

      (* Consider any TDMA slot assignment for these tasks *)
      Variable task_time_slot: TDMA_slot Task.

      (* A valid time slot must be positive *)
      Definition is_valid_time_slot:=
        task_time_slot task > 0.

      (* We define the TDMA cycle as the sum of all the tasks' time slots *)
      Definition TDMA_cycle:= 
        \sum_(tsk <- ts) task_time_slot tsk.

       (* We define the function returning the slot offset for each task: 
         i.e., the distance between the start of the TDMA cycle and 
         the start of the task time slot *)
      Definition Task_slot_offset:= 
        \sum_(prev_task <- ts | slot_order prev_task task && (prev_task != task)) task_time_slot prev_task.

      (* The following function tests whether a task is in its time slot at instant t *)
      Definition Task_in_time_slot (t:time):=
       ((t + TDMA_cycle - (Task_slot_offset)%% TDMA_cycle) %% TDMA_cycle) 
        < (task_time_slot task).

      Section BasicLemmas.

        (* Assume task_time_slot is valid time slot*)
        Hypothesis time_slot_positive:
          is_valid_time_slot.

        (* Obviously, the TDMA cycle is greater or equal than any task time slot which is 
          in TDMA cycle *)
        Lemma TDMA_cycle_ge_each_time_slot:
          TDMA_cycle >= task_time_slot task.
        Proof. 
        rewrite /TDMA_cycle (big_rem task) //.
        apply:leq_trans; last by exact: leq_addr.
        by apply leqnn.
        Qed.

        (* Thus, a TDMA cycle is always positive *)
        Lemma TDMA_cycle_positive:
          TDMA_cycle > 0.
        Proof.
        move:time_slot_positive. move/leq_trans;apply;apply TDMA_cycle_ge_each_time_slot.
        Qed.

        (* Slot offset is less then cycle *)
        Lemma Offset_lt_cycle:
          Task_slot_offset < TDMA_cycle.
        Proof.
        rewrite /Task_slot_offset /TDMA_cycle big_mkcond.
        apply leq_ltn_trans with (n:=\sum_(prev_task <- ts )if prev_task!=task then task_time_slot prev_task else 0).
        - apply leq_sum. intros* T. case (slot_order i task);auto.
        - rewrite -big_mkcond. rewrite-> bigD1_seq with (j:=task);auto.
          rewrite -subn_gt0 -addnBA. rewrite subnn addn0 //.
          trivial. apply (set_uniq ts).
        Qed.

        (* For a task, the sum of its slot offset and its time slot is 
          less then or equal to cycle. *)
        Lemma Offset_add_slot_leq_cycle:
          Task_slot_offset + task_time_slot task <= TDMA_cycle.
        Proof.
        rewrite /Task_slot_offset /TDMA_cycle.
        rewrite addnC (bigD1_seq task) //=. rewrite leq_add2l.
        rewrite big_mkcond.
        replace (\sum_(i <- ts | i != task) task_time_slot i)
        with (\sum_(i <- ts ) if i != task then task_time_slot i else 0).
        apply leq_sum. intros*T. case (slot_order i task);auto.
        by rewrite -big_mkcond. apply (set_uniq ts).
        Qed.

      End BasicLemmas.

    End TimeSlot.

    (* In this section, we prove that no two tasks share the same time slot at any time. *)
    Section InTimeSlotUniq.

      (* Consider any TDMA slot assignment for these tasks *)
      Variable task_time_slot: TDMA_slot Task.

      (* Assume that slot order is total... *)
      Hypothesis slot_order_total:
        slot_order_is_total_over_task_set.

      (*..., antisymmetric... *)
      Hypothesis slot_order_antisymmetric:
        slot_order_is_antisymmetric_over_task_set.

      (*... and transitive. *)
      Hypothesis slot_order_transitive:
        slot_order_is_transitive.

      (* Then, we can prove that the difference value between two offsets is
        at least a slot *)
      Lemma relation_offset:
        forall tsk1 tsk2, tsk1 \in ts -> tsk2 \in ts ->
        slot_order tsk1 tsk2 -> tsk1 != tsk2 ->
        Task_slot_offset tsk2 task_time_slot >= Task_slot_offset tsk1 task_time_slot + task_time_slot tsk1 .
      Proof.
      intros* IN1 IN2 ORDER NEQ.
      rewrite /Task_slot_offset big_mkcond addnC.
      replace (\sum_(tsk <- ts | slot_order tsk tsk2 && (tsk != tsk2)) task_time_slot tsk)
        with (task_time_slot tsk1 + \sum_(tsk <- ts )if slot_order tsk tsk2 && (tsk != tsk1) && (tsk!=tsk2) then task_time_slot tsk else O).
      rewrite leq_add2l. apply leq_sum_seq. intros* IN T.
      case (slot_order i tsk1)eqn:SI2;auto. case (i==tsk1)eqn:IT2;auto;simpl.
      case (i==tsk2)eqn:IT1;simpl;auto.
      - by move/eqP in IT1;rewrite IT1 in SI2;apply slot_order_antisymmetric in ORDER;auto;apply ORDER in SI2;move/eqP in NEQ.
      - by rewrite (slot_order_transitive _ _ _ SI2 ORDER).
      - symmetry. rewrite big_mkcond /=. rewrite->bigD1_seq with (j:=tsk1);auto;last by apply (set_uniq ts).
        move/eqP /eqP in ORDER. move/eqP in NEQ. rewrite ORDER //=. apply /eqP.
        have TS2: (tsk1 != tsk2) = true . apply /eqP;auto. rewrite TS2.
        rewrite eqn_add2l. rewrite big_mkcond. apply/eqP. apply eq_bigr;auto.
        intros* T. case(i!=tsk1);case (slot_order i tsk2);case (i!=tsk2) ;auto.
      Qed.

      (* Then, we proved that no two tasks share the same time slot at any time. *)
      Lemma task_in_time_slot_uniq:
        forall tsk1 tsk2 t, tsk1 \in ts -> task_time_slot tsk1 > 0 ->
        tsk2 \in ts -> task_time_slot tsk2 > 0 ->
        Task_in_time_slot tsk1 task_time_slot t ->
        Task_in_time_slot tsk2 task_time_slot t ->
        tsk1 = tsk2.
      Proof.
      intros* IN1 SLOT1 IN2 SLOT2.
      rewrite /Task_in_time_slot.
      set cycle:=TDMA_cycle task_time_slot.
      set O1:= Task_slot_offset tsk1 task_time_slot.
      set O2:= Task_slot_offset tsk2 task_time_slot.
      have CO1: O1 < cycle by apply Offset_lt_cycle.
      have CO2: O2 < cycle by apply Offset_lt_cycle.
      have C: cycle > 0 by apply (TDMA_cycle_positive tsk1).
      have GO1:O1 %% cycle = O1 by apply modn_small,Offset_lt_cycle. rewrite GO1.
      have GO2:O2 %% cycle = O2 by apply modn_small,Offset_lt_cycle. rewrite GO2.
      have SO1:O1 + task_time_slot tsk1 <= cycle by apply (Offset_add_slot_leq_cycle tsk1).
      have SO2:O2 + task_time_slot tsk2 <= cycle by apply (Offset_add_slot_leq_cycle tsk2).
      repeat rewrite mod_elim;auto.
      case (O1 <= t%%cycle)eqn:O1T;case (O2 <= t %%cycle)eqn:O2T;intros G1 G2;try ssromega.
      apply util.nat.ltn_subLR in G1;apply util.nat.ltn_subLR in G2. case (tsk1==tsk2) eqn:NEQ;move/eqP in NEQ;auto.
      destruct (slot_order_total tsk1 tsk2) as [order |order];auto;apply relation_offset in order;
      fold O1 O2 in order;try ssromega;auto. by move/eqP in NEQ. apply /eqP;auto.
      Qed.

    End InTimeSlotUniq.

  End PropertiesTDMA.

End PolicyTDMA.



