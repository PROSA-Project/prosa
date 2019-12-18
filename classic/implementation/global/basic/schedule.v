Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform.
Require Import prosa.classic.model.schedule.global.transformation.construction.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import ArrivalSequence Schedule Platform Priority ScheduleConstruction.
  
  Section Implementation.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Let num_cpus denote the number of processors, ...*)
    Variable num_cpus: nat.

    (* ... and let arr_seq be any arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.

    (* Assume a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy Job.

    (* Next, we show how to recursively construct the schedule. *)
    Section ScheduleConstruction.

      (* For any time t, suppose that we have generated the schedule prefix in the
         interval [0, t). Then, we must define what should be scheduled at time t. *)
      Variable sched_prefix: schedule Job num_cpus.
      Variable cpu: processor num_cpus.
      Variable t: time.

      (* For simplicity, let's use some local names. *)
      Let is_pending := pending job_arrival job_cost sched_prefix.
      Let arrivals := jobs_arrived_up_to arr_seq.
      
      (* Consider the list of pending jobs at time t, ... *)
      Definition pending_jobs := [seq j <- arrivals t | is_pending j t].

      (* ...which we sort by priority. *)
      Definition sorted_pending_jobs :=
        sort (higher_eq_priority t) pending_jobs.

      (* Then, we take the n-th highest-priority job from the list. *)
      Definition nth_highest_priority_job :=
        nth_or_none sorted_pending_jobs cpu.
      
    End ScheduleConstruction.

    (* Starting from the empty schedule, the final schedule is obtained by iteratively
       picking the highest-priority job. *)
    Let empty_schedule : schedule Job num_cpus := fun cpu t => None.
    Definition scheduler :=
      build_schedule_from_prefixes num_cpus nth_highest_priority_job empty_schedule.

    (* Then, by showing that the construction function depends only on the prefix, ... *)
    Lemma scheduler_depends_only_on_prefix:
      forall sched1 sched2 cpu t,
        (forall t0 cpu0, t0 < t -> sched1 cpu0 t0 = sched2 cpu0 t0) ->
        nth_highest_priority_job sched1 cpu t = nth_highest_priority_job sched2 cpu t.
    Proof.
      intros sched1 sched2 cpu t ALL.
      rewrite /nth_highest_priority_job.
      suff SAME: sorted_pending_jobs sched1 t = sorted_pending_jobs sched2 t by rewrite SAME.
      rewrite /sorted_pending_jobs; f_equal.
      apply eq_in_filter.
      intros j ARR.
      rewrite /pending; do 2 f_equal.
      rewrite /completed; f_equal.
      apply eq_big_nat; move => i /= LTi.
      rewrite /service_at /scheduled_on; apply eq_bigl; move => cpu'.
      by rewrite ALL.
    Qed.
      
    (* ...we infer that the generated schedule is indeed based on the construction function. *)
    Corollary scheduler_uses_construction_function:
      forall t cpu, scheduler cpu t = nth_highest_priority_job scheduler cpu t.
    Proof.
      by ins; apply prefix_dependent_schedule_construction,
                    scheduler_depends_only_on_prefix.
    Qed.
    
  End Implementation.

  Section Proofs.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Assume a positive number of processors. *)
    Variable num_cpus: nat.
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Let arr_seq be any job arrival sequence with consistent, duplicate-free arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* Consider any JLDP policy higher_eq_priority that is transitive and total. *)
    Variable higher_eq_priority: JLDP_policy Job.
    Hypothesis H_priority_transitive: JLDP_is_transitive higher_eq_priority.
    Hypothesis H_priority_total: forall t, total (higher_eq_priority t).

    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority.

    (* Next, we provide some helper lemmas about the scheduler construction. *)
    Section HelperLemmas.

      Let sorted_jobs :=
        sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority sched.

      (* First, we recall that the schedule picks the nth highest-priority job. *)
      Corollary scheduler_nth_or_none_mapping :
        forall t cpu,
          sched cpu t = nth_or_none (sorted_jobs t) cpu.
      Proof.
        intros t cpu.
        by rewrite /sched scheduler_uses_construction_function.
      Qed.
      
      (* We also prove that a backlogged job has priority larger than or equal to the number
         of processors. *)
      Lemma scheduler_nth_or_none_backlogged :
        forall j t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          exists i,
            nth_or_none (sorted_jobs t) i = Some j /\ i >= num_cpus.
      Proof.
        intros j t ARRj BACK.
        move: BACK => /andP [PENDING /negP NOTCOMP].
        assert (IN: j \in sorted_jobs t).
        {
          rewrite mem_sort mem_filter PENDING andTb.
          move: PENDING => /andP [ARRIVED _].
          by apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival).
        }
        apply nth_or_none_mem_exists in IN; des.
        exists n; split; first by done.
        rewrite leqNgt; apply/negP; red; intro LT.
        apply NOTCOMP; clear NOTCOMP PENDING.
        apply/existsP; exists (Ordinal LT); apply/eqP.
        by rewrite scheduler_nth_or_none_mapping.
      Qed.

    End HelperLemmas.

    (* First, we show that scheduled jobs come from the arrival sequence. *)
      Lemma scheduler_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched arr_seq.
      Proof.
        move => j t /existsP [cpu /eqP SCHED].
        rewrite scheduler_nth_or_none_mapping in SCHED.
        apply nth_or_none_mem in SCHED.
        rewrite mem_sort mem_filter in SCHED.
        move: SCHED => /andP [_ ARR].
        rewrite /jobs_arrived_up_to in ARR.
        by eapply in_arrivals_implies_arrived; eauto 1.
      Qed.

    (* Next, we show that jobs do not execute before their arrival times... *)
    Theorem scheduler_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Proof.
      move => j t /existsP [cpu /eqP SCHED].
      rewrite scheduler_nth_or_none_mapping in SCHED.
      apply nth_or_none_mem in SCHED.
      rewrite mem_sort mem_filter in SCHED.
      by move: SCHED => /andP [/andP [ARR _] _].
    Qed.

    (* ...jobs are sequential, ... *)
    Theorem scheduler_sequential_jobs: sequential_jobs sched.
    Proof.
      intros j t cpu1 cpu2 SCHED1 SCHED2.
      rewrite 2!scheduler_nth_or_none_mapping in SCHED1 SCHED2.
      set l := sorted_pending_jobs _ _ _ _ _ _ _ in SCHED1 SCHED2.
      apply ord_inj, nth_or_none_uniq with (l0 := l) (x := j); try (by done).
      by rewrite sort_uniq filter_uniq //; eapply arrivals_uniq; eauto 1.
    Qed.
    
    (* ... and jobs do not execute after completion. *)
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
        apply leq_add; first by done.
        rewrite /service_at.
        case (boolP ([exists cpu, scheduled_on sched j cpu t])) => [EX | ALL]; last first.
        {
          rewrite negb_exists in ALL; move: ALL => /forallP ALL.
          rewrite big1 //; intros cpu SCHED.
          by specialize (ALL cpu); rewrite SCHED in ALL.
        }
        move: EX => /existsP [cpu SCHED].
        rewrite (bigD1 cpu) /=; last by done.
        rewrite big1; first by rewrite addn0.
        move => cpu' /andP [SCHED' NEQ].
        move: NEQ => /eqP NEQ; exfalso; apply NEQ, ord_inj.
        move: SCHED SCHED' => /eqP SCHED /eqP SCHED'.
        rewrite 2!scheduler_nth_or_none_mapping in SCHED SCHED'.
        set l := sorted_pending_jobs _ _ _ _ _ _ _ in SCHED SCHED'.
        apply nth_or_none_uniq with (l0 := l) (x := j); try (by done).
        by rewrite sort_uniq filter_uniq //; eapply arrivals_uniq; eauto 1.
      }
      rewrite -[job_cost _]addn0; apply leq_add; first by rewrite -EQ.
      rewrite leqn0 /service_at big1 // /scheduled_on.
      move => cpu /eqP SCHED.
      rewrite scheduler_nth_or_none_mapping in SCHED.
      apply nth_or_none_mem in SCHED.
      rewrite mem_sort mem_filter in SCHED.
      move: SCHED => /andP [/andP [_ NOTCOMP] _].
      by rewrite /completed EQ leqnn in NOTCOMP.
    Qed.
    
    (* In addition, the scheduler is work conserving, ... *)
    Theorem scheduler_work_conserving:
      work_conserving job_arrival job_cost arr_seq sched. 
    Proof.
      intros j t ARRj BACK cpu.
      set jobs := sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority sched t.
      destruct (sched cpu t) as [j0 |] eqn:SCHED; first by exists j0; apply/eqP.
      apply scheduler_nth_or_none_backlogged in BACK; last by done.
      destruct BACK as [cpu_out [NTH GE]].
      exfalso; rewrite leqNgt in GE; move: GE => /negP GE; apply GE.
      apply leq_ltn_trans with (n := cpu); last by done.
      rewrite scheduler_nth_or_none_mapping in SCHED.
      apply nth_or_none_size_none in SCHED.
      apply leq_trans with (n := size jobs); last by done.
      by apply nth_or_none_size_some in NTH; apply ltnW.
    Qed.

    (* ...and respects the JLDP policy. *)
    Theorem scheduler_respects_policy :
      respects_JLDP_policy job_arrival job_cost arr_seq sched higher_eq_priority.
    Proof.
      move => j j_hp t ARRj BACK /existsP [cpu /eqP SCHED].
      apply scheduler_nth_or_none_backlogged in BACK; last by done.
      set jobs := sorted_pending_jobs _ _ _ _ _ _ _ in BACK.
      destruct BACK as [cpu_out [SOME GE]].
      rewrite scheduler_nth_or_none_mapping in SCHED. 
      have EQ1 := nth_or_none_nth jobs cpu j_hp j SCHED.
      have EQ2 := nth_or_none_nth jobs cpu_out j j SOME.
      rewrite -EQ1 -{2}EQ2.
      apply sorted_lt_idx_implies_rel; try (by done); last 2 first.
      - by apply leq_trans with (n := num_cpus).
      - by apply nth_or_none_size_some in SOME.
      - by apply sort_sorted, H_priority_total.
    Qed.

  End Proofs.

End ConcreteScheduler.