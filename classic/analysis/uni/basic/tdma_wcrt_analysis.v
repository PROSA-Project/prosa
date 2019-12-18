Require Import Arith Omega Nat.
Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.schedule.uni.schedulability
               prosa.classic.model.schedule.uni.schedule_of_task 
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.basic.platform_tdma
               prosa.classic.model.schedule.uni.end_time.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

Set Bullet Behavior "Strict Subproofs".

Module WCRT_OneJobTDMA.

Import Job  TaskArrival ScheduleOfTask  ResponseTime Platform_TDMA end_time Schedulability.

  (* In this section, we prove that any job j of task tsk will be completed by
     the computed value WCRT of the exact response-time analysis under TDMA scheduling policy
     on an uniprocessor, assuming that all its previous jobs have been completed by its arrival time. *)
  Section WCRT_analysis.

    (** System model *)
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_sporadic_tasks:
    sporadic_task_model task_period job_arrival job_task arr_seq.

    (* ..., any uniprocessor... *)
    Variable sched: schedule Job.
    (* ... where jobs do not execute before their arrival times nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Consider any TDMA slot assignment... *)
    Variable task_time_slot: TDMA_slot sporadic_task.
    (* ... and any slot order. *)
    Variable slot_order: TDMA_slot_order sporadic_task.

    (* ... and any sporadic task set. *)
    Variable ts: {set sporadic_task}.
    Hypothesis H_valid_task_parameters:
    valid_sporadic_taskset task_cost task_period task_deadline ts.

    (* Consider any task in task set... *)
    Variable tsk:sporadic_task.
    Hypothesis H_task_in_task_set: tsk \in ts.

    (* ... and any job belongs to it. *)
    Variable j:Job.
    Hypothesis H_job_task: job_task j =tsk.
    Hypothesis job_in_arr_seq: arrives_in arr_seq j.
    Hypothesis H_valid_job:
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* For simplicity, let us use local names for some definitions and refer them to local variables. *)
    Let time_slot:= task_time_slot tsk.
    Let slot_offset:= Task_slot_offset ts slot_order tsk task_time_slot.
    Let tdma_cycle:= TDMA_cycle ts task_time_slot.
    Let is_scheduled_at t:= 
      scheduled_at sched j t.
    Let in_time_slot_at t:= 
        Task_in_time_slot ts slot_order tsk task_time_slot t.
    Let pending_at:=
      pending job_arrival job_cost sched j.

    (* Recall definitions of end time predicate... *)
    Let job_end_time_predicate:= end_time_predicate sched j.
    (* ... and completes_at *)
    Let job_completes_at:=
    completes_at job_arrival job_cost sched j.

    (* Then, let's give some local definition for clarity. *)
    (* We define a formula that allows to calculate the distance 
      between time t and the previous start of tsk's time slot *)
    Let from_start_of_slot t:= 
      ( t + tdma_cycle- slot_offset %% tdma_cycle) %% tdma_cycle.

    (* ... and a formula that allows to calculate the distance 
      between time t and the next start of its time slot *)
    Let to_next_slot t:= 
      tdma_cycle - from_start_of_slot t.

    (* and a formula that allows to calculate the duration to finish
      a job if it is right at the start of its time slot and has 
      an execution cost c *)
    Let duration_to_finish_from_start_of_slot_with c:duration := 
      (div_ceil c time_slot -1) * (tdma_cycle - time_slot) + c.

    (* a formula that allows to calculate the duration between time t and the end of slot
       in case of time t in time slot *)
    Let to_end_of_slot t:=
      time_slot - from_start_of_slot t.

    (* Given the arrival time arr and job cost c, we define a formula for calculating the response time.
       This formula will be shown to be correct w.r.t. end_time_predicate *)
    Definition formula_rt (arr:instant) (c:duration):=
      if c ==0 then 0 else
      if in_time_slot_at arr then
              if c <= to_end_of_slot arr then
                   c
              else to_next_slot arr + 
                    duration_to_finish_from_start_of_slot_with (c - to_end_of_slot arr)
        else 
            to_next_slot arr + duration_to_finish_from_start_of_slot_with c.

    (* and the response time formula for job *)
    Definition job_response_time_tdma_in_at_most_one_job_is_pending:= 
      formula_rt (job_arrival j) (job_cost j).

    (* Now, let's assume that task time slot is valid, and... *)
    Hypothesis H_valid_time_slot: is_valid_time_slot tsk task_time_slot.

    (* ... the schedule respects TDMA scheduling policy. *)
    Hypothesis TDMA_policy:
      Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order.


    (* Assume that all previous jobs of same task have completed 
        before the arrive of this job of this task *)
    Hypothesis all_previous_jobs_of_same_task_completed :
      forall j_other,
        arrives_in arr_seq j_other ->
        job_task j = job_task j_other ->
        job_arrival j_other < job_arrival j ->
        completed_by job_cost sched j_other (job_arrival j).

    (** First, we prove some basic lemmas about pending. *)
    Section BasicLemmas.
      (* We can prove that there is at most one job of a task is pending at
        any instant t *)
      Lemma at_most_one_job_is_pending:
        forall j_other (t : time),
          arrives_in arr_seq j_other ->
          job_arrival j_other < job_arrival j ->
          pending job_arrival job_cost sched j t ->
          pending job_arrival job_cost sched j_other t ->
          job_task j = job_task j_other -> j = j_other.
      Proof.
        move=> j_other t ARRJO ARRBF /andP [ARREDJ /negP NCOMJ] /andP [ARREDJO /negP NCOMJO] EQTSK.
        apply all_previous_jobs_of_same_task_completed in ARRBF;auto;
        apply completion_monotonic with (t':=t) in ARRBF;auto;try contradiction;
        apply scheduler_completed_jobs_dont_execute,job_arrival_times_are_consistent.
      Qed.

      (*Lemma: it respects TDMA policy for a particular case (job must be 
        finished before the next job's arrival), that is, the job can be always 
        scheduled at time t iff it is in its time slot at time t *)
      Lemma TDMA_policy_case_RT_le_Period:
        forall t,
          pending_at t ->
          reflect (in_time_slot_at  t) (is_scheduled_at t).
      Proof.
      intros* PEN.
      apply/introP.
      - rewrite /is_scheduled_at /in_time_slot_at -H_job_task. 
        by apply TDMA_policy.
      - intro NSCHED. have BACKLOG:backlogged job_arrival job_cost sched j t by apply/andP.
        apply TDMA_policy in BACKLOG;auto.
        destruct BACKLOG as [NINSLOT | SCHED].
        + by rewrite H_job_task in NINSLOT.
        + destruct SCHED as [j_other [ARRJO [ARRBF [SAME SCHEDJO]]]].
          apply (at_most_one_job_is_pending _ t) in ARRJO;trivial.
          * by rewrite -ARRJO in SCHEDJO;move/negP in NSCHED.
          * by apply scheduled_implies_pending.
      Qed.

      (* Job is pending at its arrival *)
      Lemma pendingArrival: pending_at (job_arrival j).
      Proof.
        rewrite /pending_at /pending.
        apply /andP. split.
        - rewrite /has_arrived. auto.
        - rewrite /completed_by /service /service_during.
          rewrite ->cumulative_service_before_job_arrival_zero
          with (job_arrival0:=job_arrival). rewrite -ltnNge. 
          apply H_valid_job. apply H_jobs_must_arrive_to_execute. auto.
      Qed.

      (* Job is pending at t.+1 if 
          it is pending but isn't scheduled at t *)
      Lemma pendingSt:
        forall t, 
          pending_at t ->
          is_scheduled_at t = false ->
          pending_at t.+1.
      Proof.
        rewrite /pending_at /pending.
        move=> t /andP [ARR NCOMP] NSCHED.
        apply /andP. split.
        - rewrite /has_arrived. auto.
        - rewrite /completed_by /service /service_during big_nat_recr /service_at /=. 
          rewrite /is_scheduled_at in NSCHED. rewrite NSCHED /= addn0. auto. auto.
      Qed.

      (* Job is pending at t.+1 if
         it is both pending and scheduled at instant t 
         but there are 2 cost left at instant t *)
      Lemma pendingSt_Sched:
        forall t c,
          pending_at t ->
          service sched j t + c.+2 =job_cost j ->
          is_scheduled_at t = true ->
          pending_at t.+1.
      Proof.
        rewrite /pending_at /pending.
        move=> t c /andP [ARR NCOMP] COST SCHED.
        apply /andP. split.
        - rewrite /has_arrived; auto.
        - rewrite /completed_by /service /service_during big_nat_recr /service_at /=; 
          rewrite /is_scheduled_at in SCHED. rewrite SCHED /= -COST; apply/eqP;
          rewrite /service /service_during /service_at;ssromega. trivial.
      Qed.

    End BasicLemmas.

    (** Next, we prove some generic lemmas about the response time formula and the end time predicate. *)
    Section formula_predicate_eq.

      (* Lemma: duration to next start of time slot is always positive *)
      Lemma to_next_slot_pos:
        forall t, to_next_slot t>0.
      Proof.
        intros t.
        rewrite /to_next_slot /from_start_of_slot ltn_subRL addn0.
        apply ltn_pmod. by apply (TDMA_cycle_positive ts tsk).
      Qed.

      (* Lemma: if the duration to next start of slot is a+1 at instant t
              imply the duration to next start of slot is a at instant t+1 *)
      Lemma lt_to_next_slot_1LR:
        forall a t, 
          a.+1 < to_next_slot t ->
          a < to_next_slot t.+1.
      Proof.
        intros*.
        rewrite /to_next_slot /from_start_of_slot.
        set cycle_sub:=tdma_cycle - slot_offset %% tdma_cycle.
        assert (H_tdma_cycle_p: tdma_cycle>0) by (apply (TDMA_cycle_positive ts tsk); done).
        repeat (rewrite -addnBA;last (apply ltnW; by apply ltn_pmod)). 
        fold cycle_sub. repeat rewrite ltn_subRL.
        rewrite addSn addnS.
        case (modulo_cases (t + cycle_sub) tdma_cycle.-1); intros h1 h2.
        - rewrite prednK // in h1. ssromega. 
        - destruct h1 as [h1 _]. rewrite prednK // in h1. ssromega. 
      Qed.

      (* Lemma: if the duration to next start of slot is a+b at instant t
              imply the duration to next start of slot is a at instant t+b *)
      Lemma lt_to_next_slot_LR:
        forall b a t, 
          a+b < to_next_slot t ->
          a < to_next_slot (t+b).
      Proof.
        intro b.
        induction b as [| b' IHb']; intros* h1.
        - rewrite addn0 in h1. rewrite addn0 //.
        - rewrite addnS. 
          apply lt_to_next_slot_1LR, IHb'.
          by rewrite addSn -addnS.
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and the duration to 
              next start is at least 1, thus the job cannot be scheduled at instant
              t+1 *)
      Lemma S_t_not_sched:
        forall t, pending_at t ->
         is_scheduled_at t = false ->
         1 < to_next_slot t ->
         is_scheduled_at t.+1 = false.
      Proof.
        intros* PEN NSCHED.
        assert (H_tdma_cycle_p: tdma_cycle>0). by apply (TDMA_cycle_positive ts tsk).
        have PEN2:pending_at t by trivial.
        apply TDMA_policy_case_RT_le_Period in PEN. move:NSCHED => h1 h2. have NSCHED :is_scheduled_at t = false by auto.
        move:h1=>/PEN /negP h1.
        apply/(TDMA_policy_case_RT_le_Period t.+1). by apply pendingSt.
        apply/negP. 
        revert h1. rewrite /in_time_slot_at /Task_in_time_slot.
        fold tdma_cycle slot_offset time_slot.
        repeat rewrite -leqNgt.
        set cycle_sub:=tdma_cycle - slot_offset %% tdma_cycle.
        repeat (rewrite -addnBA;last (by apply ltnW, ltn_pmod)). 
        fold cycle_sub.
        rewrite /to_next_slot /from_start_of_slot -addnBA in h2.
        - fold cycle_sub in h2. rewrite ltn_subRL in h2.
          case (modulo_cases (t + cycle_sub) tdma_cycle.-1).
          + intros h3 h4. rewrite prednK // in h3. rewrite h3. ssromega.
          + intros [h31 h32] h4. rewrite prednK // in h32. ssromega. 
        - by apply ltnW, ltn_pmod.
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and the duration to 
              next start is at least d, thus the job cannot be scheduled at instant
              t+d and is pending at t+d *)
      Lemma duration_not_sched:
        forall t,
          pending_at t ->
          is_scheduled_at t = false -> 
          forall d, d < to_next_slot t ->
                    is_scheduled_at (t+d) = false /\ pending_at (t+d).
      Proof.
        intros t PEN h1 d h2. generalize dependent t.
        induction d as [| d' IHd'];intros t PEN.
        - by rewrite addn0.
        - rewrite addnS -addSn. intros NSCHED SD. apply IHd'. by apply pendingSt.
          apply S_t_not_sched;auto. ssromega. by apply lt_to_next_slot_1LR.
      Qed.

      (* Lemma: if the job is pending but cannot be scheduled at instant t
        thus that the job is pending at t+ to_next_slot t *)
      Lemma pending_Nsched_sched:
        forall t,
          pending_at t ->
          is_scheduled_at t = false -> 
          pending_at (t+ to_next_slot t).
      Proof.
        intros* PEN NSCHED.
        have NEXT: to_next_slot t > 0 by apply to_next_slot_pos.
        apply duration_not_sched with (d:= (to_next_slot t).-1)in PEN.
        replace (to_next_slot t) with ((to_next_slot t).-1 .+1).
        rewrite addnS. apply pendingSt. apply PEN. apply PEN.
        ssromega. auto. ssromega.
      Qed.

      (* Lemma: It must be schedulable at next start of its time slot *)
      Lemma at_next_start_of_slot_schedulabe:
        forall t, 
          pending_at t ->
          is_scheduled_at t = false ->
          is_scheduled_at (t+to_next_slot t) = true.
      Proof.
        assert (H_tdma_cycle_p: tdma_cycle>0) by (apply (TDMA_cycle_positive ts tsk); done).
        intros* PEN NSCHED_t.
        apply/TDMA_policy_case_RT_le_Period. by apply pending_Nsched_sched.
        rewrite /in_time_slot_at /Task_in_time_slot /to_next_slot /from_start_of_slot.
        repeat rewrite -addnBA.
        - set haha:= t + (tdma_cycle - slot_offset %% tdma_cycle).
          rewrite addnAC -modnDml subnKC.
          + by rewrite modnn.
          + by apply ltnW, ltn_pmod.
        - by apply ltnW, ltn_pmod.
        - by apply ltnW, ltn_pmod.
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and its residue cost is not
              0, so it has the same residue cost at instant t+1.
              the end time of this job is fixed whenever we calculate it *)
      Lemma formula_not_sched_St: forall t c, pending_at t ->
            is_scheduled_at t = false -> 
            t + formula_rt t c.+1 = t.+1 + formula_rt t.+1 c.+1.
      Proof.
      intros* PEN h1.
      have PENS: pending_at t.+1 by apply pendingSt.
      assert (H_tdma_cycle_p: tdma_cycle>0). by apply (TDMA_cycle_positive ts tsk).
      assert (H_tdma_cycle_le_slot: tdma_cycle>= time_slot).
      by apply (TDMA_cycle_ge_each_time_slot ts tsk) with(task_time_slot:= task_time_slot).
      assert (Hoffset: slot_offset %% tdma_cycle <= tdma_cycle). by apply ltnW, ltn_pmod.
      have NSLOT: in_time_slot_at t = false. apply /negP /TDMA_policy_case_RT_le_Period;auto.
      by rewrite h1.
      rewrite /formula_rt /to_end_of_slot NSLOT gtn_eqF //. move:NSLOT. move /negP.
      rewrite /in_time_slot_at /Task_in_time_slot. 
      move/negP. rewrite -ltnNge -/time_slot -/tdma_cycle -/slot_offset. intro NSLOT.
      case_eq (in_time_slot_at t.+1);
           rewrite /in_time_slot_at /Task_in_time_slot -/time_slot -/tdma_cycle -/slot_offset; 
           intro Hcases.  
      - rewrite -addnBA // in NSLOT. rewrite -addnBA // in Hcases.
        case (modulo_cases (t + (tdma_cycle - slot_offset %% tdma_cycle)) tdma_cycle.-1); intro mod_case;
        repeat (rewrite prednK // in mod_case).
          + rewrite addSn mod_case in Hcases. ssromega.
          + destruct mod_case as [case1 case2].
            rewrite /to_next_slot  /from_start_of_slot. repeat (rewrite -addnBA //).
            rewrite case2 Hcases. repeat rewrite addSn case1 -subn1 subKn //.
            repeat rewrite subn0.
            case Hc_slot:(c < time_slot); rewrite /duration_to_finish_from_start_of_slot_with.
            * by rewrite ceil_eq1 //; ssromega.
            * rewrite ceil_suba //; try ssromega.
              rewrite subn1 mulnBl mul1n addnA -addSn addn1.
               apply/eqP. rewrite eqn_add2l subnBA // addnA. repeat rewrite addnBA; try ssromega.
              -- by rewrite addKn addnAC addnK.
              -- apply leq_trans with (n:=tdma_cycle - time_slot + time_slot).
                 ++ ssromega. 
                 ++ apply leq_add.
                    ** apply leq_pmull, ceil_neq0; try ssromega. rewrite ltn_subRL addn0. ssromega. 
                    ** apply leqnn.
      - rewrite Hcases. repeat rewrite addnA. apply/eqP. repeat rewrite eqn_add2r.
        rewrite -addn1 -addnA eqn_add2l /to_next_slot /from_start_of_slot.
        move:Hcases. repeat rewrite -addnBA //. intro Hcases.
        case (modulo_cases (t + (tdma_cycle - slot_offset %% tdma_cycle)) tdma_cycle.-1); 
        intro mod_case; rewrite prednK // in mod_case.
        + rewrite add1n addn1 addSn mod_case.
          do 2 rewrite -addn1.
          set nb:=t + (tdma_cycle - slot_offset %% tdma_cycle) .
          by rewrite subnDA subn1 addn1 prednK // ltn_subRL addn0 ltn_mod.
        + destruct mod_case as [case1 case2].
          rewrite addSn case1 in Hcases.
          assert (H_slot_pos: time_slot > 0) by assumption. ssromega.
      Qed.

      (* Lemma: if the job can be scheduled at instant t and its residue cost is not
              0 (c+1), so its residue cost will be consume 1 unit and remain c at
              instant t+1.
              the end time of this job is fixed whenever we calculate it *)

      Lemma formula_sched_St:
        forall t c, 
          is_scheduled_at t = true -> 
          t + formula_rt t c.+1 = t.+1 + formula_rt t.+1 c.
      Proof.
        assert (H_tdma_cycle_p: tdma_cycle>0). by apply (TDMA_cycle_positive ts tsk).
        assert (H_tdma_cycle_ge_slot: tdma_cycle>= time_slot). by apply (TDMA_cycle_ge_each_time_slot ts tsk).
        assert (Hoffset: slot_offset %% tdma_cycle <= tdma_cycle). by apply ltnW, ltn_pmod.
        intros* h1. have PEN:pending_at t by apply scheduled_implies_pending.
        have NSLOT: in_time_slot_at t = true. apply /TDMA_policy_case_RT_le_Period;auto.
        rewrite /formula_rt /to_end_of_slot NSLOT gtn_eqF //. move:NSLOT. 
        rewrite /in_time_slot_at /Task_in_time_slot. 
        rewrite -/time_slot -/tdma_cycle -/slot_offset. intro NSLOT.
        case (in_time_slot_at t.+1) eqn:Hcases; revert Hcases;
          rewrite /in_time_slot_at /Task_in_time_slot;
          fold time_slot tdma_cycle slot_offset; (rewrite -addnBA;last exact); intro Hcases;rewrite Hcases.
          rewrite /from_start_of_slot.
          case (c < time_slot - (t + tdma_cycle - slot_offset %% tdma_cycle) %% tdma_cycle) eqn: Hc.
            - destruct c; simpl. 
              + ssromega.
              + case (modulo_cases (t + (tdma_cycle - slot_offset %% tdma_cycle)) tdma_cycle.-1); intro mod_case.
                * repeat rewrite -addnBA //. rewrite prednK // in mod_case. repeat rewrite addSn mod_case.
                  case (c < time_slot - ((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+1) eqn:Hc1; try ssromega.
                  rewrite ltn_subRL addSn in Hc1. rewrite ltn_subRL addnS -addnBA // in Hc.
                  ssromega.
                * repeat rewrite -addnBA //.
                  case (c < time_slot - ((t.+1 + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle)) eqn:Hc1; try ssromega.
                  rewrite prednK // in mod_case. destruct mod_case.
                  rewrite addSn in Hc1. ssromega. 
            - destruct c; repeat rewrite -addnBA // in Hc;rewrite -addnBA // in NSLOT;simpl.
              + ssromega.
              + repeat rewrite -addnBA // addSn.
                case (modulo_cases (t + (tdma_cycle - slot_offset %% tdma_cycle)) tdma_cycle.-1); 
                intro mod_case; rewrite prednK // in mod_case.
                * case (c < time_slot - ((t + (tdma_cycle - slot_offset %% tdma_cycle)).+1 %% tdma_cycle)) eqn:Hc1; try ssromega.
                  rewrite /to_next_slot /from_start_of_slot. repeat rewrite -addnBA //. rewrite addSn.
                  rewrite mod_case -addSn addnA addnA. 
                  replace (t.+1 +(tdma_cycle - ((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+1)) with
                  (t + (tdma_cycle - (t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle)).
                  -- apply/eqP. rewrite eqn_add2l. 
                     replace (c.+2 - (time_slot - (t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle)) with
                     (c.+1 - (time_slot - ((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+1)); trivial.
                     symmetry.
                     replace ((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+1 with
                              (((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle)+1) by ssromega.
                     rewrite subnDA. repeat (rewrite subnBA;try ssromega).  
                     by rewrite addn1.
                  -- rewrite -addn1. apply/eqP. rewrite -addnA eqn_add2l. 
                     replace ((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+1 with
                             (((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle)+1) by ssromega.
                     rewrite subnDA addnC addnBA.
                     ++ rewrite add1n subn1 //.
                     ++ rewrite ltn_subRL addn0. by apply ltn_pmod.
                * case (c < time_slot - ((t + (tdma_cycle - slot_offset %% tdma_cycle)).+1 %% tdma_cycle)) eqn:Hc1;
                  destruct mod_case as [case1 case2].
                  -- rewrite leq_eqVlt in H_tdma_cycle_ge_slot. revert H_tdma_cycle_ge_slot.
                     move/orP. intros [Hts | Hts]; try ssromega.
                     move/eqP in Hts. rewrite case2.
                     rewrite /duration_to_finish_from_start_of_slot_with Hts.
                     replace (tdma_cycle - tdma_cycle) with 0 by ssromega.
                     rewrite muln0 /to_next_slot /from_start_of_slot -addnBA // case2. 
                     replace (tdma_cycle - tdma_cycle.-1)  with 1 by ssromega. ssromega.
                  -- rewrite case1 case2. rewrite leq_eqVlt in H_tdma_cycle_ge_slot.
                     revert H_tdma_cycle_ge_slot. move/orP. 
                     intros [Hts | Hts]; try ssromega. move/eqP in Hts. apply /eqP. 
                     rewrite -addnS eqn_add2l /duration_to_finish_from_start_of_slot_with /to_next_slot /from_start_of_slot.
                     repeat rewrite Hts. 
                     replace (tdma_cycle - tdma_cycle) with 0 by ssromega. 
                     repeat rewrite muln0 -addnBA //.
                     rewrite addSn case1 case2 add0n subn0 add0n.
                     replace (tdma_cycle - tdma_cycle.-1)  with 1 by ssromega.
                     rewrite add1n subn1 //= addnBA; try ssromega. 
                     by rewrite addKn.
          - move/negP /negP in Hcases. rewrite -ltnNge in Hcases. rewrite -addnBA in NSLOT.
            rewrite /from_start_of_slot.
            case (c < time_slot - (t + tdma_cycle - slot_offset %% tdma_cycle) %% tdma_cycle)eqn:Hc.
            + destruct c; simpl; try ssromega.
              rewrite /to_next_slot /from_start_of_slot.
             case (modulo_cases (t + (tdma_cycle - slot_offset %% tdma_cycle)) tdma_cycle.-1); intro mod_case;
             rewrite prednK // in mod_case. rewrite addSn mod_case leq_eqVlt in Hcases.
             move: Hcases => /orP [Hcase | Hcase]; try ssromega.
             * rewrite -addn1 in Hcase.
               replace ((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+2 with
                       (((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+1 +1) in Hcase; try ssromega.
               rewrite eqn_add2r in Hcase. move/eqP in Hcase. 
               rewrite Hcase -addnBA // subSnn in Hc. ssromega.
             * destruct mod_case as [case1 case2]. 
               rewrite addSn case1 in Hcases. ssromega.
           + destruct c; simpl. 
             * rewrite ltn_subRL addn0 -addnBA // in Hc. ssromega.
             * rewrite /to_next_slot /from_start_of_slot.
               case (modulo_cases (t + (tdma_cycle - slot_offset %% tdma_cycle)) tdma_cycle.-1) ;intro mod_case;
               rewrite prednK // in mod_case.
               -- rewrite addSn mod_case leq_eqVlt in Hcases.
                  move:Hcases =>/orP [Hcase|Hcase]; try ssromega.
                  rewrite -addn1 in Hcase. 
                  replace ((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+2 with
                          (((t + (tdma_cycle - slot_offset %% tdma_cycle)) %% tdma_cycle).+1 +1) in Hcase; try ssromega.
                  rewrite eqn_add2r in Hcase.
                  move/eqP in Hcase. 
                  repeat rewrite -addnBA //. 
                  rewrite addSn addSn mod_case Hcase subSnn subn1 /= subnS -addnS -addSn prednK // ltn_subRL addn0.
                  by apply ltn_pmod.
               -- destruct mod_case as [case1 _]. rewrite addSn case1 in Hcases. ssromega.
            + trivial.
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and its cost is not
                null, it will have the same cost at instant t+d, where 
                d < the duration to the start of the next slot from t *)
      Lemma formula_not_sched_interval:
        forall t c,
          pending_at t ->
          is_scheduled_at t = false ->
          forall d, d < to_next_slot t ->
                    t + formula_rt t c.+1 = t + d + formula_rt (t + d) c.+1.
      Proof.
        intros* h1.
        induction d as [| d' IHd']; intro h2.
        - by repeat rewrite addn0.
        - rewrite addnS -formula_not_sched_St.
          + auto. 
          + apply duration_not_sched; auto.
          + apply duration_not_sched; auto.
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and its cost is not
                null, then its cost will be the same at the start of the next slot *)
      Lemma formula_not_sched_to_next_slot:
        forall t c, pending_at t ->
          is_scheduled_at t = false -> 
          t + formula_rt t c.+1 = t + to_next_slot t + formula_rt (t + to_next_slot t) c.+1.
      Proof.
        intros* PEN h1.
        assert (H2ns:to_next_slot t>0) by apply to_next_slot_pos.
        rewrite (formula_not_sched_interval _ _ _ _ (to_next_slot t).-1) //.
        - rewrite formula_not_sched_St. 
          + replace (t + (to_next_slot t).-1).+1 with (t + to_next_slot t).
            * reflexivity.
            * rewrite -addnS. ssromega.
          + apply duration_not_sched;auto. ssromega.
          + apply duration_not_sched;auto. ssromega.
         - ssromega. 
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and its residue cost is not
                null, and it will remain the same at the next start of slot + 1 *)
      Lemma job_not_sched_to_cunsume_1unit:
        forall t c, pending_at t ->
          is_scheduled_at t = false ->
          t + formula_rt t c.+1 = (t + to_next_slot t).+1 + formula_rt (t + to_next_slot t).+1 c.
      Proof.
        intros* PEN h1.
        assert (Hsched:is_scheduled_at (t+to_next_slot t) = true)
            . apply at_next_start_of_slot_schedulabe;auto. 
        apply formula_sched_St with (c:=c) in Hsched.
        rewrite -Hsched formula_not_sched_to_next_slot //. 
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and its cost is not
                null, it will have the same cost at instant t+d, where 
                d < the duration to the start of the next slot from t.
                lemma on end time predicate with forward direction *)
      Lemma end_time_predicate_not_sched_eq:
        forall d c t e ,
          pending_at t ->
          is_scheduled_at t = false ->
          job_end_time_predicate t c.+1 e -> 
          d < to_next_slot t ->
          job_end_time_predicate (t+d) c.+1 e.
      Proof.
        intro d.
        induction d as [| d' IHd'];intros c t e PEN h1 h2 h3.
        - by rewrite addn0.
        - rewrite addnS. apply end_time_predicate_not_sched.
          + apply duration_not_sched with (d:=d')in h1.
            * rewrite /is_scheduled_at in h1. destruct h1 as [h11 h12]. by rewrite h11.
            * auto. 
            * auto.
          + apply IHd'; auto.
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and its cost is not
                null, it will have the same cost at instant t+d, where 
                d < the duration to the start of the next slot from t.
                lemma on end time predicate with reverse direction *)
      Lemma end_time_predicate_not_sched_eq_rev:
        forall d c t e ,
          pending_at t ->
          is_scheduled_at t = false ->
          job_end_time_predicate (t+d) (S c) e -> 
          d < to_next_slot t ->
          job_end_time_predicate t (S c) e.
      Proof.
        intro d.
        induction d as [| d' IHd'];intros c t e PEN h1 h2 h3.
        - by rewrite addn0 in h2.
        - rewrite addnS in h2. apply S_C_not_sched in h2.
          + apply IHd'; auto.
          + apply duration_not_sched with (d:=d') in h1; auto.
            rewrite /is_scheduled_at in h1. destruct h1 as [h11 h12].
            by rewrite h11.
      Qed.

      (* Lemma: if the job cannot be scheduled at instant t and its cost is not
                null, it will have the same cost at instant t+d, where 
                d < the duration to the start of the next slot from t.
               lemma on end time predicate *)
      Lemma end_time_predicate_eq:
        forall t c e,
          pending_at t ->
          is_scheduled_at t = false ->
            job_end_time_predicate t c.+1 e <->
            job_end_time_predicate ((t+to_next_slot t).+1) c e.
      Proof.
        intros t c e PEN h1.
        assert (H1:is_scheduled_at t = false) by assumption.
        assert (H2ns:to_next_slot t>0) by apply to_next_slot_pos.
        assert (Hfact: (to_next_slot t).-1 < to_next_slot t). by rewrite prednK.
        split; intro h2.
        - apply (end_time_predicate_sched j sched (t + to_next_slot t) c e).
          by apply at_next_start_of_slot_schedulabe.
          apply duration_not_sched with (d:=(to_next_slot t).-1) in h1; try done.
          replace (t + to_next_slot t) with (t + (to_next_slot t).-1.+1) by (rewrite prednK; done).
          rewrite addnS.
          apply end_time_predicate_not_sched. 
          + rewrite /is_scheduled_at in h1. destruct h1 as [h11 h12]. by rewrite h11.
          + by apply end_time_predicate_not_sched_eq.
        - apply S_C_sched in h2.
          + replace (t + to_next_slot t) with (t + (to_next_slot t).-1.+1) in h2 by (rewrite prednK; done).
            rewrite addnS in h2. apply S_C_not_sched in h2.
            * by apply end_time_predicate_not_sched_eq_rev with (d:=(to_next_slot t).-1) in h2. 
            * apply duration_not_sched with (d:=(to_next_slot t).-1) in h1; try done.
              rewrite /is_scheduled_at in h1. destruct h1 as [h11 h12]. by rewrite h11.
           + by apply at_next_start_of_slot_schedulabe.
      Qed.

      (* Lemma: service received dont change if the job isn't scheduled *)
      Lemma service_is_zero_in_Nsched_duration:
        forall d t,
          pending_at t ->
          scheduled_at sched j t = false ->
          d <= to_next_slot t ->
          service sched j ( t + d) = service sched j t.
      Proof.
        intro d.
        induction d as [| d GD];intros* PEN NSCHED D.
        - by rewrite addn0.
        - have NSTD: scheduled_at sched j (t+d) = false by apply duration_not_sched.
          rewrite addnS /service /service_during big_nat_recr /service_at;trivial. rewrite NSTD /= addn0.
          apply GD;auto.
      Qed.

      (* Lemma: job completes at end time
        this lemma allows to valide the response time formula defined above *)
      Lemma completes_at_end_time_pre:
        forall c t , pending_at t -> service sched j t + c = job_cost j ->
        end_time_predicate sched j t c (t + formula_rt t c).
      Proof.
        intro c.
        induction c as [| c IHc];intros ARR PEN SC.
        - rewrite /formula_rt /= addn0; apply (C0_ sched j).
        - case l:(is_scheduled_at ARR).
          + destruct c as [|c];apply (S_C_sched sched j);rewrite // formula_sched_St //.
            * rewrite  /formula_rt /= addn0;apply C0_.
            * apply IHc.
                -- by apply pendingSt_Sched with (c:=c).
                -- rewrite /is_scheduled_at in l;
                   rewrite -SC /service /service_during /service_at big_nat_recr //.
                   rewrite l /=;ssromega.
          + apply end_time_predicate_eq;try exact l. 
            * exact PEN. 
            * destruct c as [|c];rewrite job_not_sched_to_cunsume_1unit //.
              -- rewrite  /formula_rt /= addn0; apply C0_.
              -- have SCHED: scheduled_at sched j (ARR + to_next_slot ARR) = true
                 by apply at_next_start_of_slot_schedulabe. apply IHc.
                ++ have PENX: pending_at (ARR+to_next_slot ARR) by apply pending_Nsched_sched.
                   apply pendingSt_Sched with (c:=c);try trivial.
                   by rewrite service_is_zero_in_Nsched_duration.
                ++ rewrite <-service_is_zero_in_Nsched_duration with (d:=to_next_slot ARR) in SC;auto.
                   rewrite -SC /service /service_during /service_at big_nat_recr;auto. rewrite SCHED /=.
                   ssromega.
      Qed.

    End formula_predicate_eq.

    (** Then we prove that job j completes at instant (arrival + response time) by
       (1) assuming that all its previous jobs have been completed by its arrival time and
       (2) basing on the basic and generic lemmas above. *)
    Lemma completes_at_end_time:
          job_completes_at (job_arrival j + job_response_time_tdma_in_at_most_one_job_is_pending).
    Proof.
    apply completes_at_end_time_pre.
    by apply pendingArrival.
    rewrite /service /service_during.
    by rewrite ->cumulative_service_before_job_arrival_zero with (job_arrival0:=job_arrival).
    Qed.

    (** Finally, we prove that job can be finished within the formula WCRT. *)
    Section ValidWCRT.

      (* Recall the definition of task_cost is exactly WCET, which is the worst-case execution time
          with respect to a job *)
      Let WCET := task_cost tsk.

      (* We define a formula for calculating the worst-case response time, which means
        job arrives at the end of its time slot with WCET *)
      Definition WCRT_formula cycle s wcet:=
        (div_ceil wcet s)*(cycle - s) + wcet.
      Definition WCRT:=
        WCRT_formula tdma_cycle time_slot WCET.

      (* Assume that job cost is always less than or equal to its task cost *)
      Hypothesis H_job_cost_le_task_cost: job_cost_le_task_cost task_cost job_cost job_task j.

      (* We prove that response time is always less than or equal to WCRT *)
      Lemma response_time_le_WCRT:
        job_response_time_tdma_in_at_most_one_job_is_pending <= WCRT.
      Proof.
        rewrite /job_response_time_tdma_in_at_most_one_job_is_pending /WCRT /formula_rt /to_end_of_slot.
        unfold Task_in_time_slot in in_time_slot_at. 
        fold  tdma_cycle in in_time_slot_at. fold time_slot in in_time_slot_at. fold slot_offset in in_time_slot_at.
        have cost_pos: job_cost j > 0 by apply H_valid_job.
        case test_in_slot:(in_time_slot_at (job_arrival j)).
        - case test_cost:(job_cost j <= time_slot - from_start_of_slot (job_arrival j)).
          + set other := div_ceil (job_cost j) time_slot * (tdma_cycle - time_slot).
            apply leq_trans with (n:=div_ceil WCET time_slot * (tdma_cycle - time_slot) + job_cost j). 
            * rewrite gtn_eqF //. apply leq_addl.
            * rewrite leq_add2l /WCET -H_job_task //.
          + assert (Hmod:(job_arrival j + tdma_cycle - slot_offset %% tdma_cycle)%% tdma_cycle < tdma_cycle)
            by (apply ltn_pmod; apply TDMA_cycle_positive with (task:=tsk); done).
            assert (hcm:tdma_cycle - time_slot <=div_ceil (job_cost j - (time_slot -
            from_start_of_slot (job_arrival j))) time_slot * (tdma_cycle - time_slot)).
            * apply leq_pmull, ceil_neq0; try apply H_valid_time_slot.
              apply negbT in test_cost; rewrite<-ltnNge in test_cost; by rewrite subn_gt0.
            * unfold duration_to_finish_from_start_of_slot_with. 
              rewrite addnA mulnBl mul1n. 
              set cost_sub_end:=job_cost j - (time_slot - from_start_of_slot (job_arrival j)). 
              rewrite addnBA; try apply hcm.
              rewrite addnC;rewrite addnBA.
              -- rewrite addnA.
                 assert (h1:cost_sub_end + to_next_slot (job_arrival j) = job_cost j + (tdma_cycle - time_slot)).
                 ++ rewrite /cost_sub_end /to_next_slot addnC subnBA.
                    ** rewrite addnBA. 
                       --- rewrite addnC -addnA subnKC; try auto.
                           rewrite addnBA //.
                           by apply TDMA_cycle_ge_each_time_slot with (task:=tsk).
                       --- apply negbT in test_cost. rewrite -ltnNge in test_cost.
                           rewrite addnC -leq_subLR. auto.  
                     ** destruct (TDMA_policy_case_RT_le_Period (job_arrival j)) as [hj |hj]. apply pendingArrival.
                          unfold in_time_slot_at in hj; auto. unfold in_time_slot_at in hj; auto.
                 ++ rewrite h1 -addnBA ; try apply hcm.
                    rewrite -addnA subnKC; try apply hcm.
                    rewrite addnC gtn_eqF //. 
                    apply leq_add.
                    ** rewrite leq_mul2r. apply /orP. right. apply leq_divceil2r; auto.
                       apply leq_trans with (n:=job_cost j); try apply leq_subr. 
                       rewrite /WCET -H_job_task //.
                    ** rewrite /WCET -H_job_task //.
             -- rewrite <-add0n. apply leq_add; auto.
        - unfold duration_to_finish_from_start_of_slot_with. 
          rewrite addnA gtn_eqF //. 
          apply leq_add; try (rewrite /WCET -H_job_task //).
          rewrite mulnBl mul1n addnBA.
          + rewrite leq_subLR. apply leq_add. 
            * unfold to_next_slot. apply leq_sub2l. move/negP in test_in_slot.
              apply /leP. apply not_gt. apply /ltP. by apply/negP. 
            * rewrite leq_mul2r. apply /orP. right. apply leq_divceil2r; try done.
          + apply leq_pmull, ceil_neq0.
            * apply H_valid_job.
            * apply H_valid_time_slot.
      Qed.

      (* We show that this analysis is exact: job j's response time is equal to WCRT when
         (1) the job cost is equal to WCER; and
         (2) the job arrives right at the end of its time slot. *)
      Lemma exists_WCRT:
        job_cost j = WCET /\ from_start_of_slot (job_arrival j)=time_slot ->
        job_response_time_tdma_in_at_most_one_job_is_pending = WCRT.
      Proof.
        intros [COST_WCET EXISTS].
        rewrite /job_response_time_tdma_in_at_most_one_job_is_pending /WCRT /formula_rt.
        unfold Task_in_time_slot in in_time_slot_at.
        have cost_pos: job_cost j>0 by apply H_valid_job.
        fold tdma_cycle in in_time_slot_at. fold time_slot in in_time_slot_at. 
        fold slot_offset in in_time_slot_at. fold from_start_of_slot in in_time_slot_at.
        assert (gt_ref: reflect (time_slot> from_start_of_slot (job_arrival j))%coq_nat 
        (time_slot >from_start_of_slot (job_arrival j))) by apply ltP.
        case hgt:(time_slot > from_start_of_slot (job_arrival j)).
        - apply decPcases in gt_ref. rewrite EXISTS ltnn in hgt. done. 
        - apply decPcases in gt_ref.
          destruct (TDMA_policy_case_RT_le_Period (job_arrival j)) as [hj |hj]. apply pendingArrival.
          unfold in_time_slot_at in hj.
          + rewrite /from_start_of_slot in gt_ref. rewrite /from_start_of_slot in EXISTS. case (_ < _) in gt_ref;try ssromega.
          + have F:in_time_slot_at (job_arrival j) = false by auto. rewrite F.
            rewrite /to_next_slot EXISTS /duration_to_finish_from_start_of_slot_with.
            rewrite mulnBl mul1n addnA  {1}gtn_eqF // -COST_WCET.
            apply /eqP. rewrite eqn_add2r addnC subh1.
            * by rewrite addnK. 
            * by apply leq_pmull, ceil_neq0.
      Qed.

      (** Main Theorem *)
      (* We prove that any job j of task tsk will be completed by the computed value WCRT,
         assuming that all its previous jobs have been completed by its arrival time. *)
      Theorem job_completed_by_WCRT:
        completed_by job_cost sched j (job_arrival j + WCRT).
      Proof.
        apply completion_monotonic with (t:= job_arrival j + job_response_time_tdma_in_at_most_one_job_is_pending);auto.
        rewrite leq_add2l.
        apply response_time_le_WCRT.
        apply completed_by_end_time with (job_arrival0:=job_arrival);auto.
        apply completes_at_end_time.
      Qed.

    End ValidWCRT.

  End WCRT_analysis.

End WCRT_OneJobTDMA.
