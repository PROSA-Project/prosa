Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import Job ArrivalSequence UniprocessorSchedule PlatformWithSuspensions Priority
         ScheduleConstruction.

  (* In this section, we implement a priority-based uniprocessor scheduler *)
  Section Implementation.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Let arr_seq be any consistent job arrival sequence...*)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    
    (* ...that is subject to job suspensions. *)
    Variable next_suspension: job_suspension Job.
    
    (* Also, assume that a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy Job.

    (* Next, we show how to recursively construct the schedule. *)
    Section ScheduleConstruction.

      (* For any time t, suppose that we have generated the schedule prefix in the
         interval [0, t). Then, we must define what should be scheduled at time t. *)
      Variable sched_prefix: schedule Job.
      Variable t: time.
      
      (* For simplicity, let's use some local names. *)
      Let is_pending := pending job_arrival job_cost sched_prefix.
      Let is_suspended :=
        suspended_at job_arrival job_cost next_suspension sched_prefix.

      (* Consider the list of pending, non-suspended jobs at time t. *)
      Definition pending_jobs :=
        [seq j <- jobs_arrived_up_to arr_seq t | is_pending j t && ~~ is_suspended j t].

      (* To make the scheduling decision, we just pick one of the highest-priority jobs
         that are pending (if it exists). *)
      Definition highest_priority_job :=
        seq_min (higher_eq_priority t) pending_jobs.

    End ScheduleConstruction.

    (* Starting from the empty schedule, the final schedule is obtained by iteratively
       picking the highest-priority job. *)
    Let empty_schedule : schedule Job := fun t => None.
    Definition scheduler :=
      build_schedule_from_prefixes highest_priority_job empty_schedule.

    (* Then, by showing that the construction function depends only on the prefix, ... *)
    Lemma scheduler_depends_only_on_prefix:
      forall sched1 sched2 t,
        (forall t0, t0 < t -> sched1 t0 = sched2 t0) ->
        highest_priority_job sched1 t = highest_priority_job sched2 t.
    Proof.
      intros sched1 sched2 t ALL.
      rewrite /highest_priority_job.
      suff SAME: pending_jobs sched1 t = pending_jobs sched2 t by rewrite SAME.
      apply eq_in_filter.
      rewrite /jobs_arrived_up_to; intros j IN.
      apply in_arrivals_implies_arrived_before with (job_arrival0 := job_arrival) in IN;
        last by done.
      rewrite /arrived_before ltnS in IN.
      rewrite /pending /has_arrived IN 2!andTb.
      have COMP: completed_by job_cost sched1 j t =
                 completed_by job_cost sched2 j t.
      {
        rewrite /completed_by.
        rewrite /completed_by; f_equal.
        apply eq_big_nat; move => i /= LTi.
        by rewrite /service_at /scheduled_at ALL.
      }
      rewrite COMP; do 2 f_equal.
      rewrite /suspended_at; f_equal; first by rewrite COMP.
      have EX: [exists t0: 'I_t, scheduled_at sched1 j t0] =
               [exists t0: 'I_t, scheduled_at sched2 j t0].
      {
        apply/idP/idP.
        {
          move => /existsP [t0 SCHED].
          by apply/existsP; exists t0; rewrite /scheduled_at -ALL.
        }
        {
          move => /existsP [t0 SCHED].
          by apply/existsP; exists t0; rewrite /scheduled_at ALL.
        }
      }
      have BEG: time_after_last_execution job_arrival sched1 j t =
                time_after_last_execution job_arrival sched2 j t.
      {
        rewrite /time_after_last_execution EX.
        case: ifP => _; last by done.
        f_equal; apply eq_bigl.
        by intros t0; rewrite /scheduled_at ALL.
      }
      have SUSP: suspension_duration job_arrival next_suspension sched1 j t =
                 suspension_duration job_arrival next_suspension sched2 j t.
      {
        rewrite /suspension_duration BEG; f_equal.
        rewrite /service /service_during big_nat_cond [in RHS]big_nat_cond.
        apply congr_big; try (by done).
        move => i /= /andP [LTi _].
        rewrite /service_at /scheduled_at ALL //.
        apply: (leq_trans LTi).
        by apply last_execution_bounded_by_identity.
      }
      by rewrite BEG SUSP.
    Qed.
      
    (* ...we infer that the generated schedule is indeed based on the construction function. *)
    Corollary scheduler_uses_construction_function:
      forall t, scheduler t = highest_priority_job scheduler t.
    Proof.
      by ins; apply prefix_dependent_schedule_construction,
                    scheduler_depends_only_on_prefix.
    Qed.
    
  End Implementation.

  (* In this section, we prove the properties of the scheduler that are used
     as hypotheses in the analyses. *)
  Section Proofs.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Assume any job arrival sequence with consistent, duplicate-free arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_no_duplicate_arrivals: arrival_sequence_is_a_set arr_seq.

    (* ...that is subject to suspension times. *)
    Variable next_suspension: job_suspension Job.

    (* Consider any JLDP policy that is reflexive, transitive and total. *)
    Variable higher_eq_priority: JLDP_policy Job.
    Hypothesis H_priority_is_transitive: JLDP_is_transitive higher_eq_priority. 
    Hypothesis H_priority_is_total: JLDP_is_total arr_seq higher_eq_priority. 

    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority.

    (* To conclude, we prove the important properties of the scheduler implementation. *)
    
    (* First, we show that scheduled jobs come from the arrival sequence. *)
      Lemma scheduler_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched arr_seq.
      Proof.
        move => j t /eqP SCHED.
        rewrite /sched scheduler_uses_construction_function // /highest_priority_job in SCHED.
        apply seq_min_in_seq in SCHED.
        rewrite mem_filter in SCHED.
        move: SCHED => /andP [_ ARR].
        by eapply in_arrivals_implies_arrived, ARR.
      Qed.

    (* Next, we show that jobs do not execute before they arrive...*)
    Theorem scheduler_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Proof.
      move => j t /eqP SCHED.
      rewrite /sched scheduler_uses_construction_function // /highest_priority_job in SCHED.
      apply seq_min_in_seq in SCHED.
      rewrite mem_filter in SCHED.
      by move: SCHED => /andP [/andP [/andP [ARR _] _] _].
    Qed.

    (* ... nor after completion. *)
    Theorem scheduler_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.
    Proof.
      intros j t.
      induction t;
        first by rewrite /service /service_during big_geq //.
      rewrite /service /service_during big_nat_recr //=.
      rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LT]; last first.
      {
        apply: leq_trans LT; rewrite -addn1.
          by apply leq_add; last by apply leq_b1.
      }
      rewrite -[job_cost _]addn0; apply leq_add; first by rewrite -EQ.
      rewrite leqn0 eqb0 /scheduled_at.
      rewrite /sched scheduler_uses_construction_function //.
      rewrite /highest_priority_job.
      apply/eqP; intro HP.
      apply seq_min_in_seq in HP.
      by rewrite mem_filter /pending /completed_by -EQ leqnn andbF 2!andFb in HP.
    Qed.

    (* In addition, the scheduler is work conserving, ... *)
    Theorem scheduler_work_conserving:
      work_conserving job_arrival job_cost next_suspension arr_seq sched. 
    Proof.
      intros j t IN BACK.
      move: BACK => /andP [/andP [/andP [ARR NOTCOMP] NOTSCHED] NOTSUSP].
      rewrite /scheduled_at /sched scheduler_uses_construction_function // in NOTSCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function //.
      case HP: (highest_priority_job _ _ _ _ _ ) => [j_hp|]; first by exists j_hp.
      set hp := highest_priority_job _ _ _ _ _ _ _ in NOTSCHED HP.
      suff BUG: hp != None by rewrite HP in BUG.
      apply seq_min_exists with (x := j).
      rewrite mem_filter /pending NOTSUSP ARR NOTCOMP /=.
      by eapply arrived_between_implies_in_arrivals, ARR.
    Qed.

    (* ... respects the JLDP policy..., *)
    Theorem scheduler_respects_policy :
      respects_JLDP_policy job_arrival job_cost next_suspension arr_seq sched higher_eq_priority.
    Proof.
      rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL.
      move => j1 j2 t ARR1 BACK /eqP SCHED.
      move: BACK => /andP [/andP [/andP [ARR NOTCOMP] NOTSCHED] NOTSUSP].
      rewrite /scheduled_at /sched scheduler_uses_construction_function // in NOTSCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function // in SCHED.
      rewrite /highest_priority_job in SCHED NOTSCHED.
      set jobs := pending_jobs _ _ _ _ _ _ in SCHED NOTSCHED.
      have IN: j1 \in jobs.
      {
        rewrite mem_filter /pending ARR NOTCOMP NOTSUSP /=.
        by eapply arrived_between_implies_in_arrivals, ARR.
      }
      apply seq_min_computes_min with (y := j1) in SCHED; try (by done).
      by intros x y; rewrite 2!mem_filter; move => /andP [_ INx] /andP [_ INy];
         apply TOTAL; eapply in_arrivals_implies_arrived; eauto 2.
    Qed.

    (* ... and respects self-suspensions. *)
    Theorem scheduler_respects_self_suspensions:
      respects_self_suspensions job_arrival job_cost next_suspension sched.
    Proof.
      move => j t /eqP SCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function // in SCHED.
      rewrite /highest_priority_job in SCHED; apply seq_min_in_seq in SCHED.
      rewrite mem_filter in SCHED.
      by move: SCHED => /andP [/andP [_ NOTSUSP] _]; apply/negP.
    Qed.
    
  End Proofs.
    
End ConcreteScheduler.