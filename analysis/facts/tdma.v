Require Export prosa.model.schedule.tdma.
Require Import prosa.util.all.
From mathcomp Require Import div.

(** In this section, we define the properties of TDMA and prove some basic lemmas. *)
Section TDMAFacts.
  Context {Task:eqType}.

  (** Consider any task set ts... *)
  Variable ts: {set Task}.

  (** ... with a TDMA policy *)
  Context `{TDMAPolicy Task}.

  Section TimeSlotFacts.
    (** Consider any task in ts*)
    Variable task: Task.
    Hypothesis H_task_in_ts: task \in ts.

    (** Assume task_time_slot is valid time slot*)
    Hypothesis time_slot_positive:
      valid_time_slot ts.

    (** Obviously, the TDMA cycle is greater or equal than any task time slot which is
          in TDMA cycle *)
    Lemma TDMA_cycle_ge_each_time_slot:
      TDMA_cycle ts >= task_time_slot task.
    Proof.
      rewrite /TDMA_cycle (big_rem task) //.
      apply:leq_trans; last by exact: leq_addr.
        by apply leqnn.
    Qed.

    (** Thus, a TDMA cycle is always positive *)
    Lemma TDMA_cycle_positive:
      TDMA_cycle ts > 0.
    Proof.
      move:time_slot_positive=>/(_ task H_task_in_ts)/leq_trans;apply;apply TDMA_cycle_ge_each_time_slot.
    Qed.

    (** Slot offset is less then cycle *)
    Lemma Offset_lt_cycle:
      task_slot_offset ts task < TDMA_cycle ts.
    Proof.
      rewrite /task_slot_offset /TDMA_cycle big_mkcond.
      apply leq_ltn_trans with (n:=\sum_(prev_task <- ts )if prev_task!=task then task_time_slot prev_task else 0).
      - apply leq_sum. intros* T. case (slot_order i task);auto.
      - rewrite -big_mkcond (bigD1_seq task)?set_uniq//=.
        rewrite -subn_gt0 -addnBA. rewrite subnn addn0 //.
        exact: time_slot_positive.
        easy.
    Qed.

    (** For a task, the sum of its slot offset and its time slot is
          less then or equal to cycle. *)
    Lemma Offset_add_slot_leq_cycle:
      task_slot_offset ts task + task_time_slot task <= TDMA_cycle ts.
    Proof.
      rewrite /task_slot_offset /TDMA_cycle.
      rewrite addnC (bigD1_seq task) //=. rewrite leq_add2l.
      rewrite big_mkcond.
      replace (\sum_(i <- ts | i != task) task_time_slot i)
        with (\sum_(i <- ts ) if i != task then task_time_slot i else 0).
      apply leq_sum. intros*T. case (slot_order i task);auto.
        by rewrite -big_mkcond. apply (set_uniq ts).
    Qed.
  End TimeSlotFacts.

  (** Now we prove that no two tasks share the same time slot at any time. *)
  Section TimeSlotOrderFacts.
    (** Consider any task in ts*)
    Variable task: Task.
    Hypothesis H_task_in_ts: task \in ts.

    (** Assume task_time_slot is valid time slot*)
    Hypothesis time_slot_positive:
      valid_time_slot ts.

    (** Assume that slot order is total... *)
    Hypothesis slot_order_total:
      total_slot_order ts.

    (*..., antisymmetric... *)
    Hypothesis slot_order_antisymmetric:
      antisymmetric_slot_order ts.

    (*... and transitive. *)
    Hypothesis slot_order_transitive:
      transitive_slot_order.

    (** Then, we can prove that the difference value between two offsets is
        at least a slot *)
    Lemma relation_offset:
      forall tsk1 tsk2, tsk1 \in ts ->
                                 tsk2 \in ts ->
                                          slot_order tsk1 tsk2 ->
                                          tsk1 != tsk2 ->
                                          task_slot_offset ts tsk2 >=
                                          task_slot_offset ts tsk1 + task_time_slot tsk1 .
    Proof.
      intros* IN1 IN2 ORDER NEQ.
      rewrite /task_slot_offset big_mkcond addnC/=.
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

    (** Then, we proved that no two tasks share the same time slot at any time. *)
    Lemma task_in_time_slot_uniq:
      forall tsk1 tsk2 t, tsk1 \in ts -> task_time_slot tsk1 > 0 ->
                                   tsk2 \in ts -> task_time_slot tsk2 > 0 ->
                                            task_in_time_slot ts tsk1 t ->
                                            task_in_time_slot ts tsk2 t ->
                                            tsk1 = tsk2.
    Proof.
      intros* IN1 SLOT1 IN2 SLOT2.
      rewrite /task_in_time_slot.
      set cycle:=TDMA_cycle ts.
      set O1:= task_slot_offset ts tsk1.
      set O2:= task_slot_offset ts tsk2.
      have CO1: O1 < cycle by apply Offset_lt_cycle.
      have CO2: O2 < cycle by apply Offset_lt_cycle.
      have C: cycle > 0 by apply (TDMA_cycle_positive tsk1).
      have GO1:O1 %% cycle = O1 by apply modn_small,Offset_lt_cycle. rewrite GO1.
      have GO2:O2 %% cycle = O2 by apply modn_small,Offset_lt_cycle. rewrite GO2.
      have SO1:O1 + task_time_slot tsk1 <= cycle by apply (Offset_add_slot_leq_cycle tsk1).
      have SO2:O2 + task_time_slot tsk2 <= cycle by apply (Offset_add_slot_leq_cycle tsk2).
      repeat rewrite mod_elim;auto.
      case (O1 <= t%%cycle)eqn:O1T;case (O2 <= t %%cycle)eqn:O2T;intros G1 G2;try ssromega.
      apply ltn_subLR in G1;apply ltn_subLR in G2. case (tsk1==tsk2) eqn:NEQ;move/eqP in NEQ;auto.
      destruct (slot_order_total tsk1 tsk2) as [order |order];auto;apply relation_offset in order;
      fold O1 O2 in order;try ssromega;auto. by move/eqP in NEQ. apply /eqP;auto.
    Qed.

  End TimeSlotOrderFacts.
End TDMAFacts.
