Require Export prosa.model.schedule.work_conserving.
Require Export prosa.analysis.facts.model.ideal_schedule.
Require Export prosa.analysis.transform.wc_trans.
Require Export prosa.analysis.facts.transform.swaps.
Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.util.list.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** * Correctness of the work-conservation transformation *)
(** This file contains the main argument of the work-conservation proof,
    starting with an analysis of the individual functions that drive
    the work-conservation transformation of a given reference schedule 
    and ending with the proofs of individual properties of the obtained
    work-conserving schedule. *)

(** Throughout this file, we assume ideal uniprocessor schedules and
    the basic (i.e., Liu & Layland) readiness model under which any
    pending job is ready. *)
Require Import prosa.model.processor.ideal.
Require Import prosa.model.readiness.basic.

(** In order to discuss the correctness of the work-conservation transformation at a high level,
    we first need a set of lemmas about the inner parts of the procedure. *)
Section AuxiliaryLemmasWorkConservingTransformation.
  
  (** Consider any type of jobs with arrival times, costs, and deadlines... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobDeadline Job}.
  
  (** ...and an arbitrary arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** We introduce the notion of work-conservation at a 
      given time [t]. The definition is based on the concept of readiness
      of a job, and states that the presence of a ready job implies that
      the processor is not idle. *)
  Definition is_work_conserving_at sched t :=
    (exists j, arrives_in arr_seq j /\ job_ready sched j t) ->
    exists j, sched t = Some j.

  (** First, we prove some useful properties about the most fundamental
      operation of the work-conservation transformation: swapping two processor
      states [t1] and [fsc], with [fsc] being a valid swap candidate of [t1]. *)
  Section JobsMustBeReadyFindSwapCandidate.

    (** Consider an ideal uniprocessor schedule... *)
    Variable sched: schedule (ideal.processor_state Job).

    (** ...in which jobs must be ready to execute. *)
    Hypothesis H_jobs_must_be_ready: jobs_must_be_ready_to_execute sched.

    (** Consider an arbitrary time instant [t1]. *)
    Variable t1: instant.

    (** Let us define [fsc] as the result of the search for a swap candidate 
        starting from [t1]... *)
    Let fsc := find_swap_candidate arr_seq sched t1.

    (** ...and [sched'] as the schedule resulting from the swap. *)
    Let sched' := swapped sched t1 fsc.

    (** First, we show that, in any case, the result of the search will yield an
        instant that is in the future (or, in case of failure, equal to [t1]). *)
    Lemma swap_candidate_is_in_future:
      t1 <= fsc.
    Proof.
      rewrite /fsc /find_swap_candidate.
      destruct search_arg as [n|] eqn:search_result; last by done.
      apply search_arg_in_range in search_result.
        by move:search_result => /andP [LEQ LMAX].
    Qed.

    (** Also, we show that the search will not yield jobs that arrive later than the 
        given reference time. *)
    Lemma fsc_respects_has_arrived:
      forall j t,
        sched (find_swap_candidate arr_seq sched t) == Some j ->
        has_arrived j t.
    Proof.
      move=> j t.
      rewrite /find_swap_candidate.
      destruct search_arg eqn:RES; last first.
      { move: (H_jobs_must_be_ready j t).
        rewrite /scheduled_at scheduled_in_def => READY SCHED_J.
        apply READY in SCHED_J.
        by apply (ready_implies_arrived sched). }
      { move=> /eqP SCHED_J.
        move: RES => /search_arg_pred.
        rewrite SCHED_J //. }
    Qed.

    (** Next, we extend the previous lemma by stating that no job in the transformed
        schedule is scheduled before its arrival. *)
    Lemma swap_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched'.
    Proof.
      move=> j t SCHED_AT.
      move: (swap_job_scheduled_cases _ _ _ _ _ SCHED_AT)=> [OTHER |[AT_T1 | AT_T2]].
      { have READY: job_ready sched j t by apply H_jobs_must_be_ready; rewrite -OTHER //.
          by apply (ready_implies_arrived sched). }
      { set t2 := find_swap_candidate arr_seq sched t1 in AT_T1.
        move: AT_T1 => [EQ_T1 SCHED_AT'].
        apply fsc_respects_has_arrived.
        move: SCHED_AT.
        rewrite EQ_T1 /SCHED_AT' /sched' -/t2.
        rewrite EQ_T1 in SCHED_AT'.
        rewrite SCHED_AT' /scheduled_at.
        by rewrite scheduled_in_def. }
      { set t2 := find_swap_candidate arr_seq sched t1 in AT_T2.
        move: AT_T2 => [EQ_T2 SCHED_AT'].
        have ORDER: t1<=t2 by apply swap_candidate_is_in_future.
        have READY: job_ready sched j t1 by apply H_jobs_must_be_ready; rewrite -SCHED_AT' //.
        rewrite /job_ready /basic_ready_instance /pending /completed_by in READY.
        move: READY => /andP [ARR _].
        rewrite EQ_T2.
        rewrite /has_arrived in ARR.
        apply leq_trans with (n := t1) => //. }
    Qed.

    (** Finally we show that, in the transformed schedule, jobs are scheduled 
        only if they are ready. *)
    Lemma fsc_jobs_must_be_ready_to_execute:
      jobs_must_be_ready_to_execute sched'.
    Proof.
      move=> j t SCHED_AT.
      rewrite /sched'.
      set t2 := find_swap_candidate arr_seq sched t1.
      rewrite /job_ready /basic_ready_instance /pending.
      apply /andP; split; first by apply swap_jobs_must_arrive_to_execute.
      rewrite /completed_by; rewrite -ltnNge.
      apply swapped_completed_jobs_dont_execute => //.
      - by apply swap_candidate_is_in_future.
      - by apply ideal_proc_model_provides_unit_service.
      - by apply ideal_proc_model_ensures_ideal_progress.
      - by eapply completed_jobs_are_not_ready.
    Qed.

  End JobsMustBeReadyFindSwapCandidate.

  (** In the following section, we put our attention on the point-wise 
      transformation performed at each point in time prior to the horizon. *)
  Section MakeWCAtFacts.

    (** Consider an ideal uniprocessor schedule... *)
    Variable sched: schedule (ideal.processor_state Job).

    (** ...and take an arbitrary point in time... *)
    Variable t: instant.

    (** ...we define [sched'] as the resulting schedule after one point-wise transformation. *)
    Let sched' := make_wc_at arr_seq sched t.

    (** We start by proving that the point-wise transformation can only lead
        to higher service for a job at a given time. This is true because we
        swap only idle processor states with ones in which a job is scheduled. *)
    Lemma mwa_service_bound:
      forall j t, service sched j t <= service sched' j t.
    Proof.
      intros j t'.
      rewrite /sched' /make_wc_at.
      destruct (sched t) eqn:PSTATE => //.
      set t2:= (find_swap_candidate arr_seq sched t).
      move: (swap_candidate_is_in_future sched t) => ORDER.
      destruct (leqP t' t) as [BOUND1|BOUND1];
        first by rewrite (service_before_swap_invariant _ t t2) => //.
      destruct (ltnP t2 t') as [BOUND2 | BOUND2];
        first by rewrite (service_after_swap_invariant  _ t t2) => //.
      destruct (scheduled_at sched j t) eqn:SCHED_AT_T1;
        first by move:SCHED_AT_T1; rewrite scheduled_at_def PSTATE => /eqP.
      move: SCHED_AT_T1 => /negbT NOT_AT_t1.
      destruct (scheduled_at sched j t2) eqn:SCHED_AT_T2;
        last by move: SCHED_AT_T2 => /negbT NOT_AT_t2; rewrite (service_of_others_invariant _ t t2).
      rewrite /swapped /service -service_at_other_times_invariant; last by left.
      rewrite service_in_replaced; last by apply /andP; split => //.
      rewrite (not_scheduled_implies_no_service _ _ _  NOT_AT_t1) subn0.
        by apply leq_addr.
    Qed.

    (** Next, we show that any ready job in the transformed schedule must be ready also in
        the original one, since the transformation can only lead to higher service. *)
    Lemma mwa_ready_job_also_ready_in_original_schedule:  
      forall j t, job_ready sched' j t -> job_ready sched j t.
    Proof.
      intros j t'. 
      rewrite /job_ready /basic_ready_instance /pending.
      move=> /andP [ARR COMP_BY].
      rewrite ARR Bool.andb_true_l //.
      move: COMP_BY; apply contra.
      rewrite /completed_by.
      have LEQ: (service sched j t') <= (service sched' j t') by apply mwa_service_bound.
      move=> LEQ'; move:LEQ; move: LEQ'.
        by apply leq_trans.
    Qed.

    (** Since the search for a swap candidate is performed until the latest deadline
        among all the jobs arrived before the reference time, we need to show that the computed
        deadline is indeed the latest. *)
    Lemma max_dl_is_greatest_dl:
      forall j t,
        arrives_in arr_seq j ->
        job_arrival j <= t ->
        job_deadline j <= max_deadline_for_jobs_arrived_before arr_seq t.
    Proof.
      move=> j t' ARR_IN ARR.
      rewrite /max_deadline_for_jobs_arrived_before.
      apply in_max0_le; apply map_f.
      rewrite /arrivals_up_to.
      apply arrived_between_implies_in_arrivals;
        by move:H_arr_seq_valid => [CONS UNIQ].
    Qed.

    (** Next, we want to show that, if a job arriving from the arrival
       sequence is ready at some instant, then the point-wise transformation
       is guaranteed to find a job to swap with. We will proceed by doing a case 
       analysis, and show that it is impossible that a swap candidate is not found. *)
    Section MakeWCAtFindsReadyJobs.

      (** We need to assume that, in the original schedule, all the deadlines of 
          the jobs coming from the arrival sequence are met, in order to be sure that 
          a ready job will be eventually scheduled. *)
      Hypothesis H_all_deadlines_of_arrivals_met: all_deadlines_of_arrivals_met arr_seq sched.

      (** We define [max_dl] as the maximum deadline for all jobs arrived before [t]. *)
      Let max_dl := max_deadline_for_jobs_arrived_before arr_seq t.

      (** Next, we define [search_result] as the result of the search for a swap candidate.
          In order to take the first result, it is sufficient to define the ordering function
          as a constant false. *)
      Definition order (_ _ : nat) := false.
      Definition search_result := search_arg sched (relevant_pstate t) order t max_dl.
      
      (** First, we consider the case in which the procedure finds a job to swap with. *) 
      Section MakeWCAtFindsReadyJobs_CaseResultFound.

        (** Assuming that the processor is idle at time t... *)
        Hypothesis H_sched_t_idle: is_idle sched t.
        
        (** ...let [t_swap] be a time instant found by the search procedure. *)
        Variable t_swap: instant.
        Hypothesis search_result_found: search_result = Some t_swap.

        (** We show that, since the search only yields relevant processor states, a job is found. *)
        Lemma make_wc_at_case_result_found: 
          exists j: Job,
            swapped sched t t_swap t = Some j. 
        Proof.
          apply search_arg_pred in search_result_found.
          move:search_result_found; rewrite /relevant_pstate.
          destruct (sched t_swap) as [j_swap|] eqn:SCHED; last by done.
          move=>ARR. rewrite /swapped /replace_at.
          destruct (t_swap == t) eqn:SAME_SWAP.
          + move:SAME_SWAP => /eqP SAME_SWAP; subst t_swap.
            move:H_sched_t_idle => /eqP SCHED_NONE.
              by rewrite SCHED_NONE in SCHED; discriminate.
          + exists j_swap.
              by rewrite eq_refl; apply SCHED.
        Qed.
        
      End MakeWCAtFindsReadyJobs_CaseResultFound.

      (** Conversely, we prove that assuming that the search yields no
          result brings to a contradiction. *)
      Section MakeWCAtFindsReadyJobs_CaseResultNone.

        (** Consider a job that arrives in the arrival sequence, and assume that
            it is ready at time [t] in the transformed schedule. *)
        Variable j: Job.
        Hypothesis H_arrives_in: arrives_in arr_seq j.
        Hypothesis H_job_ready_sched': job_ready sched' j t.
        
        (** Moreover, assume the search for a swap candidate yields nothing. *)
        Hypothesis H_search_result_none: search_result = None.

        (** First, note that, since nothing was found, it means there is no relevant
           processor state between [t] and [max_dl]. *)
        Lemma no_relevant_state_in_range:
          forall t',
            t <= t' < max_dl ->
            ~~ (relevant_pstate t) (sched t').
        Proof.
            by apply (search_arg_none _ _ (fun _ _ => false)).
        Qed.

        (** Since [j] is ready at time [t], then it must be incomplete. *)
        Lemma service_of_j_is_less_than_cost: service sched j t < job_cost j.
        Proof.
          have READY_ORIG: job_ready sched j t
            by apply (mwa_ready_job_also_ready_in_original_schedule _ _); apply H_job_ready_sched'.
          rewrite /job_ready /basic_ready_instance /pending.
          move:READY_ORIG => /andP [ARR_ NOT_COMPL_ORIG].
          rewrite /completed_by in NOT_COMPL_ORIG.
            by rewrite leqNgt; apply NOT_COMPL_ORIG.
        Qed.

        (** And since [j] is incomplete and meets its deadline, the deadline of [j] 
            is in the future. *)        
        Lemma t_is_less_than_deadline_of_j: t <= job_deadline j. 
        Proof.
          move: (H_all_deadlines_of_arrivals_met j H_arrives_in)=> MEETS_DL_j.
          move_neq_up LEQ_t1.
          unfold job_meets_deadline, completed_by in MEETS_DL_j; move_neq_down MEETS_DL_j.
          eapply leq_ltn_trans; last apply service_of_j_is_less_than_cost.
            by apply service_monotonic, ltnW. 
        Qed.

        (** On the other hand, since we know that there is no relevant state between [t] and [max_dl], 
            then it must be the case that [j] is never scheduled in this period, and hence gets no 
            service. *) 
        Lemma equal_service_t_max_dl: service sched j t = service sched j max_dl.
        Proof.
          move:(H_job_ready_sched') => /andP [ARR NOT_COMPL_sched'].
          rewrite -(service_cat sched j t max_dl);
            last by apply (leq_trans t_is_less_than_deadline_of_j), max_dl_is_greatest_dl.
          have ZERO_SERVICE: service_during sched j t max_dl = 0.
          { apply not_scheduled_during_implies_zero_service.
            apply ideal_proc_model_ensures_ideal_progress.
            move=> t_at RANGE.
            move:(no_relevant_state_in_range t_at RANGE) => NOT_REL.
            rewrite scheduled_at_def. 
            apply/negP; move => /eqP EQ.
              by move: NOT_REL => /negP T; apply: T; rewrite EQ.
          }
            by rewrite ZERO_SERVICE; rewrite addn0.
        Qed.

        (** Combining the previous lemmas, we can deduce that [j] misses its deadline. *)
        Lemma j_misses_deadline: service sched j (job_deadline j) < job_cost j.
        Proof.
          move:(H_job_ready_sched') => /andP [ARR NOT_COMPL_sched'].
          have J_LESS := service_of_j_is_less_than_cost.
          rewrite equal_service_t_max_dl in J_LESS.
          specialize (H_all_deadlines_of_arrivals_met j H_arrives_in).
          unfold job_meets_deadline, completed_by in H_all_deadlines_of_arrivals_met.
          eapply leq_ltn_trans.
          - by apply service_monotonic, (max_dl_is_greatest_dl _ _ H_arrives_in ARR).
          - by apply J_LESS.
        Qed.

        (** The fact that [j] misses its deadline contradicts the fact that all deadlines 
            of jobs coming from the arrival sequence are met. We have a contradiction. *)
        Lemma make_wc_at_case_result_none: False.
        Proof.
          move: (H_all_deadlines_of_arrivals_met j H_arrives_in) => NEQ.
          unfold job_meets_deadline, completed_by in NEQ.
          move_neq_down NEQ.
            by apply j_misses_deadline.
        Qed.

      End MakeWCAtFindsReadyJobs_CaseResultNone. 

      (** Next, we show that [make_wc_at] always manages to establish the work-conservation property
          at the given time. Using the above case analysis, we can conclude that the presence of a 
          ready job always leads to a valid swap. *)
      Lemma mwa_finds_ready_jobs:
        all_deadlines_of_arrivals_met arr_seq sched ->
        is_work_conserving_at sched' t.
      Proof.
        move=> ALL_DL_MET P_PREFIX. 
        destruct (sched t) as [j'|] eqn:SCHED_WC_t;
          first by rewrite /sched' /make_wc_at SCHED_WC_t; exists j'.
        move: P_PREFIX => [j [ARR_IN READY]].
        rewrite /sched' /make_wc_at.
        rewrite SCHED_WC_t /find_swap_candidate.
        destruct search_arg as [t_swap| ] eqn:SEARCH_RES.
        - by apply make_wc_at_case_result_found; move:SCHED_WC_t => /eqP.
        - by exfalso; apply (make_wc_at_case_result_none j); eauto. 
      Qed.
      
    End MakeWCAtFindsReadyJobs.

    (** Next we prove that, given a schedule that respects the work-conservation property until [t-1],
        applying the point-wise transformation at time [t] will extend the property until [t]. *)
    Lemma mwa_establishes_wc:
      all_deadlines_of_arrivals_met arr_seq sched ->
      (forall t_l, t_l < t -> is_work_conserving_at sched t_l) ->
      forall t_l, t_l <= t -> is_work_conserving_at sched' t_l.
    Proof.
      move=> PROP P_PREFIX t' T_MIN [j [ARR_IN READY]].
      set fsc := find_swap_candidate arr_seq sched t.
      have LEQ_fsc: t <= fsc by apply swap_candidate_is_in_future.
      destruct (ltnP t' t) as [tLT | tGE]. 
      { have SAME: sched' t' = sched t'.
        { rewrite /sched' /make_wc_at.
          destruct (sched t); first by done.
            by rewrite (swap_before_invariant sched t fsc) //. }
        rewrite SAME.
        apply P_PREFIX; eauto.
        exists j; split; auto.
          by eapply mwa_ready_job_also_ready_in_original_schedule, READY.
      }
      { have EQ: t' = t.
        { by apply /eqP; rewrite eqn_leq; apply /andP; split. } 
        subst t'; clear T_MIN tGE.
        apply mwa_finds_ready_jobs => //.
          by exists j; split; eauto. 
      } 
    Qed.

    (** We now show that the point-wise transformation does not introduce any new job
        that does not come from the arrival sequence. *)
    Lemma mwa_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq ->
      jobs_come_from_arrival_sequence sched' arr_seq.
    Proof.
      rewrite /sched' /make_wc_at.
      destruct (sched t) as [j_orig|] eqn:SCHED_orig; first by done.
      by apply swapped_jobs_come_from_arrival_sequence.
    Qed.

    (** We also show that the point-wise transformation does not schedule jobs in instants
        in which they are not ready. *)
    Lemma mwa_jobs_must_be_ready_to_execute:
      jobs_must_be_ready_to_execute sched ->
      jobs_must_be_ready_to_execute sched'.
    Proof.
      move=> READY.
      rewrite /sched' /make_wc_at.
      destruct (sched t) as [j_orig|] eqn:SCHED_orig; first by done.
      by apply fsc_jobs_must_be_ready_to_execute.
    Qed.      

    (** Finally, we show that the point-wise transformation does not introduce deadline misses. *)
    Lemma mwa_all_deadlines_of_arrivals_met:
      all_deadlines_of_arrivals_met arr_seq sched ->
      all_deadlines_of_arrivals_met arr_seq sched'.
    Proof.
      move=> ALL j ARR.
      specialize (ALL j ARR).
      unfold job_meets_deadline, completed_by in *.
      by apply (leq_trans ALL (mwa_service_bound _ _)).
    Qed.
    
  End MakeWCAtFacts.

  (** In the following section, we proceed by proving some useful properties respected by 
      the partial schedule obtained by applying the work-conservation transformation up to 
      an arbitrary horizon. *)
  Section PrefixFacts.
    
    (** Consider an ideal uniprocessor schedule. *)
    Variable sched: schedule (ideal.processor_state Job).

    (** We start by proving that the transformation performed with two different horizons 
        will yield two schedules that are identical until the earlier horizon. *) 
    Section PrefixInclusion.

      (** Consider two horizons... *)
      Variable h1 h2: instant.

      (** ...and assume w.l.o.g. that they are ordered... *)
      Hypothesis H_horizon_order: h1 <= h2.

      (** ...we define two schedules, resulting from the transformation 
          performed, respectively, until the first and the second horizon. *)
      Let sched1 := wc_transform_prefix arr_seq sched h1.
      Let sched2 := wc_transform_prefix arr_seq sched h2.

      (** Then, we show that the two schedules are guaranteed to be equal until the
          earlier horizon. *)
      Lemma wc_transform_prefix_inclusion:
        forall t, t < h1 -> sched1 t = sched2 t.
      Proof.
        move=> t before_horizon.
        rewrite /sched1 /sched2.
        induction h2; first by move: (ltn_leq_trans before_horizon H_horizon_order).
        move: H_horizon_order. rewrite leq_eqVlt => /orP [/eqP ->|LT]; first by done.
        move: LT. rewrite ltnS => H_horizon_order_lt.
        rewrite [RHS]/wc_transform_prefix /prefix_map -/prefix_map IHi //.
        rewrite {1}/make_wc_at.
        destruct (prefix_map sched (make_wc_at arr_seq) i i) as [j|] eqn:SCHED; first by done.   
        rewrite -(swap_before_invariant _ i (find_swap_candidate arr_seq (wc_transform_prefix arr_seq sched i) i));
          last by apply ltn_leq_trans with (n := h1).
        rewrite //.
        apply swap_candidate_is_in_future.
      Qed.
    
    End PrefixInclusion.

    (** Next, we show that repeating the point-wise transformation up to a given horizon
        does not introduce any deadline miss. *)
    Section JobsMeetDeadlinePrefix.
      
      (** Assuming that all deadlines of jobs coming from the arrival sequence are met... *)
      Hypothesis H_all_deadlines_of_arrivals_met: all_deadlines_of_arrivals_met arr_seq sched.
      
      (** ...let us define [sched'] as the schedule resulting from the 
          full work-conservation transformation. Note that, if the schedule is sampled at time
          [t], the transformation is performed until [t+1]. *)
      Let sched' := wc_transform arr_seq sched.
      
      (** Consider a job from the arrival sequence. *)
      Variable j: Job.
      Hypothesis H_arrives_in: arrives_in arr_seq j.      

      (** We show that, in the transformed schedule, the service of the job
          is always greater or equal than in the original one, at any given time. *)
      Lemma wc_prefix_service_bound:
        forall t, service sched j t <= service sched' j t.
      Proof.
        move=> t.
        rewrite /sched' /wc_transform.
        set serv := service (fun t0 : instant => wc_transform_prefix arr_seq sched t0.+1 t0) j t.
        set servp := service (wc_transform_prefix arr_seq sched t.+1) j t.
        have ->: serv = servp. 
        { rewrite /serv /servp /service /service_during.
          apply eq_big_nat => t' /andP [_ LT_t].
          rewrite /service_at.
          rewrite (wc_transform_prefix_inclusion t'.+1 t.+1)=> //.
          by auto. }
        rewrite /servp /wc_transform_prefix.
        clear serv servp.
        apply prefix_map_property_invariance; last by done.
        intros. apply leq_trans with (service sched0 j t)=> //.
        by intros; apply mwa_service_bound.
      Qed.

      (** Finally, it follows directly that the transformed schedule cannot introduce 
          a deadline miss for any job from the arrival sequence. *)
      Lemma wc_prefix_job_meets_deadline:
        job_meets_deadline sched' j.
      Proof.
        rewrite /job_meets_deadline /completed_by /sched'.
        apply leq_trans with (service sched j (job_deadline j));
          last by apply wc_prefix_service_bound.
        by apply H_all_deadlines_of_arrivals_met.
      Qed.
      
    End JobsMeetDeadlinePrefix.

    (** Next, consider a given time, used as horizon for the transformation... *)
    Variable h: instant.

    (** ...and let us call [sched'] the schedule resulting from the transformation
        performed until [h]. *)
    Let sched' := wc_transform_prefix arr_seq sched h.

    (** We prove that [sched'] will never introduce jobs not coming from the
        arrival sequence. *)
    Lemma wc_prefix_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq ->
      jobs_come_from_arrival_sequence sched' arr_seq.
    Proof.
      move=> FROM_ARR.
      rewrite /sched' /wc_transform_prefix.
      apply prefix_map_property_invariance; last by done.
      move => schedX t ARR.
      by apply mwa_jobs_come_from_arrival_sequence.
    Qed.
    
    (** Similarly, we can show that [sched'] will only schedule jobs if they are
        ready. *)
    Lemma wc_prefix_jobs_must_be_ready_to_execute:
      jobs_must_be_ready_to_execute sched ->
      jobs_must_be_ready_to_execute sched'.
    Proof.
      move=> READY.
      rewrite /sched' /wc_transform_prefix.
      apply prefix_map_property_invariance; last by done.
      move=> schedX t ARR.
      by apply mwa_jobs_must_be_ready_to_execute.
    Qed.  
    
  End PrefixFacts.
  
End AuxiliaryLemmasWorkConservingTransformation.

(** Finally, we can leverage all the previous results to prove statements about the full
    work-conservation transformation. *)
Section WorkConservingTransformation.
  
  (** Consider any type of jobs with arrival times, costs, and deadlines... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobDeadline Job}.
  
  (** ...an arbitrary valid arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ...and an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...in which jobs come from the arrival sequence, and must be ready to execute...  *)
  Hypothesis H_sched_valid: valid_schedule sched arr_seq.

  (** ...and in which no job misses a deadline. *)
  Hypothesis H_all_deadlines_of_arrivals_met: all_deadlines_of_arrivals_met arr_seq sched.

  (** Let us call [sched_wc] the schedule obtained after applying the work-conservation transformation. *)
  Let sched_wc := wc_transform arr_seq sched.

  (** First, we show that any scheduled job still comes from the arrival sequence. *)
  Lemma wc_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched_wc arr_seq.
  Proof.
    rewrite /sched_wc /wc_transform.
    move=> j t.
    move: H_sched_valid => [ARR READY].
    rewrite /scheduled_at -/(scheduled_at _ j t).
    by apply (wc_prefix_jobs_come_from_arrival_sequence arr_seq sched t.+1 ARR).
  Qed.

  (** Similarly, jobs are only scheduled if they are ready. *)
  Lemma wc_jobs_must_be_ready_to_execute:
    jobs_must_be_ready_to_execute sched_wc.
  Proof.
    move=> j t.
    move: H_sched_valid => [ARR READY].
    rewrite /scheduled_at /sched_wc /wc_transform -/(scheduled_at _ j t) => SCHED_AT.
    have READY': job_ready (wc_transform_prefix arr_seq sched t.+1) j t
      by apply wc_prefix_jobs_must_be_ready_to_execute => //.
    move: READY'.
    rewrite /job_ready /basic.basic_ready_instance
            /pending /completed_by /service.
    rewrite (equal_prefix_implies_same_service_during sched_wc (wc_transform_prefix arr_seq sched t.+1)) //.
    move=> t' /andP [_ BOUND_t'].
    rewrite /sched_wc /wc_transform.
    by apply wc_transform_prefix_inclusion => //; rewrite ltnS; apply ltnW.
  Qed.

  (** Also, no deadline misses are introduced. *) 
  Lemma wc_all_deadlines_of_arrivals_met:
    all_deadlines_of_arrivals_met arr_seq sched_wc.
  Proof.
    move=> j ARR_IN.
    rewrite /sched_wc /wc_transform_prefix.
    by apply wc_prefix_job_meets_deadline.
  Qed.

  (** Finally, we can show that the transformation leads to a schedule in which
      the processor is not idle if a job is ready. *)
  Lemma wc_is_work_conserving_at:
    forall j t,
      job_ready sched_wc j t ->
      arrives_in arr_seq j ->
      exists j', sched_wc t = Some j'.
  Proof.
    move=> j t READY ARR_IN.
    rewrite /sched_wc /wc_transform /wc_transform_prefix.
    apply (prefix_map_pointwise_property (all_deadlines_of_arrivals_met arr_seq)
                                         (is_work_conserving_at arr_seq)
                                         (make_wc_at arr_seq)); rewrite //.
    { by apply mwa_all_deadlines_of_arrivals_met. }
    { by intros; apply mwa_establishes_wc. }
    { exists j.
      split; first by apply ARR_IN. 
      have EQ: job_ready sched_wc j t = job_ready (prefix_map sched (make_wc_at arr_seq) (succn t)) j t.
      {
        rewrite /sched_wc /wc_transform /job_ready
                /basic_ready_instance /pending /completed_by
                /service /service_during /service_at /wc_transform_prefix.
        destruct has_arrived; last by rewrite Bool.andb_false_l.
        have EQ_SUM: \sum_(0 <= t0 < t) service_in j (prefix_map sched (make_wc_at arr_seq) (succn t0) t0)
                  = \sum_(0 <= t0 < t) service_in j (prefix_map sched (make_wc_at arr_seq) (succn t) t0).
        {  apply eq_big_nat => t' /andP [_ LT_t].
           rewrite -/(wc_transform_prefix arr_seq sched _ _).
           rewrite -/(wc_transform_prefix arr_seq sched _ _).  
           rewrite (wc_transform_prefix_inclusion arr_seq sched t'.+1 t.+1)=> //.
           by auto. }
        by rewrite EQ_SUM. }
      move: READY. by rewrite EQ. }
  Qed.

  (** We can easily extend the previous lemma to obtain the definition 
      of a work-conserving schedule. *)
  Lemma wc_is_work_conserving:
    work_conserving arr_seq sched_wc.
  Proof.
    move=> j t ARR_IN.
    rewrite /backlogged => /andP [READY _].
    move: (wc_is_work_conserving_at j t READY ARR_IN) => [j' SCHED_wc].
    by exists j'; rewrite scheduled_at_def; apply /eqP.
  Qed.

  (** Ultimately, we can show that the work-conservation transformation maintains
      all the properties of validity, does not introduce new deadline misses, and
      establishes the work-conservation property. *)
  Theorem wc_transform_correctness:
    valid_schedule sched_wc arr_seq /\
    all_deadlines_of_arrivals_met arr_seq sched_wc /\
    work_conserving arr_seq sched_wc.
  Proof.
    repeat split.
    - apply wc_jobs_come_from_arrival_sequence.
    - apply wc_jobs_must_be_ready_to_execute.
    - apply wc_all_deadlines_of_arrivals_met.
    - apply wc_is_work_conserving.
  Qed.
  
End WorkConservingTransformation.
