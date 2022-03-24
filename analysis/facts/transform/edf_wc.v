Require Import prosa.model.readiness.basic.
Require Export prosa.analysis.facts.transform.edf_opt.
Require Export prosa.analysis.facts.transform.wc_correctness.
Require Export prosa.analysis.facts.behavior.deadlines.
Require Export prosa.analysis.facts.readiness.backlogged.


(** * Optimality of Work-Conserving EDF on Ideal Uniprocessors *)

(** In this file, we establish the foundation needed to connect the EDF and
    work-conservation optimality theorems: if there is any work-conserving way
    to meet all deadlines (assuming an ideal uniprocessor schedule), then there
    is also an (ideal) EDF schedule that is work-conserving in which all
    deadlines are met. *)

(** ** Non-Idle Swaps *)

(** We start by showing that [swapped], a function used in the inner-most level
    of [edf_transform], maintains work conservation if the two instants being
    swapped are not idle. *)
Section NonIdleSwapWorkConservationLemmas.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and any valid job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ...consider an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...that is well-behaved (i.e., in which jobs execute only after having
     arrived and only if they are not yet complete, and in which all jobs come
     from the arrival sequence). *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.
  Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

  (** Suppose we are given two specific times [t1] and [t2],... *)
  Variables t1 t2 : instant.

  (** ...which we assume to be ordered (to avoid dealing with symmetric cases),... *)
  Hypothesis H_well_ordered: t1 <= t2.

  (** ...and two jobs [j1] and [j2]... *)
  Variables j1 j2 : Job.

  (** ...such that [j2] arrives before time [t1],... *)
  Hypothesis H_arrival_j2 : job_arrival j2 <= t1.

  (** ...[j1] is scheduled at time [t1], and... *)
  Hypothesis H_t1_not_idle : scheduled_at sched j1 t1.

  (** ...[j2] is scheduled at time [t2]. *)
  Hypothesis H_t2_not_idle : scheduled_at sched j2 t2.

  (** We let [swap_sched] denote the schedule in which the allocations at
      [t1] and [t2] have been swapped. *)
  Let swap_sched := swapped sched t1 t2.

  (** Now consider an arbitrary job [j]... *)
  Variable j : Job.

  (** ...and an arbitrary instant [t]... *)
  Variable t : instant.

  (** ...such that [j] arrives in [arr_seq]... *)
  Hypothesis H_arrival_j : arrives_in arr_seq j.

  (** ...and is backlogged in [swap_sched] at instant [t]. *)
  Hypothesis H_backlogged_j_t : backlogged swap_sched j t.

  (** We proceed by case analysis. We first show that, if [t] equals [t1], then
      [swap_sched] maintains work conservation.  That is, there exists some job
      that's scheduled in [swap_sched] at instant [t] *)
  Lemma non_idle_swap_maintains_work_conservation_t1 :
    work_conserving arr_seq sched ->
    t = t1 ->
    exists j_other, scheduled_at swap_sched j_other t.
  Proof.
    move=> _ EQ; rewrite EQ; by exists j2; rewrite swap_job_scheduled_t1.
  Qed.

  (** Similarly, if [t] equals [t2] then then [swap_sched] maintains work conservation. *)
  Lemma non_idle_swap_maintains_work_conservation_t2 :
    work_conserving arr_seq sched ->
    t = t2 ->
    exists j_other, scheduled_at swap_sched j_other t.
  Proof.
    move=> _ EQ; rewrite EQ; by exists j1; rewrite swap_job_scheduled_t2.
  Qed.

  (** If [t] is less than or equal to [t1] then then then [swap_sched] maintains work conservation. *)
  Lemma non_idle_swap_maintains_work_conservation_LEQ_t1 :
    work_conserving arr_seq sched ->
    t <= t1 ->
    exists j_other, scheduled_at swap_sched j_other t.
  Proof.
    move=> WC_sched LEQ.
    case: (boolP(t == t1)) => [/eqP EQ| /eqP NEQ]; first by apply non_idle_swap_maintains_work_conservation_t1.
    case: (boolP(t == t2)) => [/eqP EQ'| /eqP NEQ']; first by apply non_idle_swap_maintains_work_conservation_t2.
    have [j_other j_other_scheduled] : exists j_other, scheduled_at sched j_other t.
    { rewrite /work_conserving in WC_sched. apply (WC_sched j) => //; move :H_backlogged_j_t.
      rewrite /backlogged/job_ready/basic_ready_instance/pending/completed_by.
      move /andP => [ARR_INCOMP scheduled]; move :ARR_INCOMP; move /andP => [arrive not_comp]. 
      apply /andP; split; first (apply /andP; split) => //.
      + by rewrite (service_before_swap_invariant sched t1 t2 _ t). 
      + by rewrite -(swap_job_scheduled_other_times _ t1 t2 j t) //; (apply /neqP; eauto).
    }
    exists j_other; by rewrite  (swap_job_scheduled_other_times) //; do 2! (apply /neqP; eauto).
  Qed.

  (** Similarly, if [t] is greater than [t2] then then then [swap_sched] maintains work conservation. *)
  Lemma non_idle_swap_maintains_work_conservation_GT_t2 :
    work_conserving arr_seq sched ->
    t2 < t ->
    exists j_other, scheduled_at swap_sched j_other t.
  Proof.
    move=> WC_sched GT.
    case: (boolP(t == t1)) => [/eqP EQ| /eqP NEQ]; first by apply non_idle_swap_maintains_work_conservation_t1.
    case: (boolP(t == t2)) => [/eqP EQ'| /eqP NEQ']; first by apply non_idle_swap_maintains_work_conservation_t2.
    have [j_other j_other_scheduled] : exists j_other, scheduled_at sched j_other t.
    { rewrite /work_conserving in WC_sched. apply (WC_sched j) => //; move :H_backlogged_j_t.
      rewrite /backlogged/job_ready/basic_ready_instance/pending/completed_by.
      move /andP => [ARR_INCOMP scheduled]; move :ARR_INCOMP; move /andP => [arrive not_comp].
      apply /andP; split; first (apply /andP; split) => //.
      + by rewrite (service_after_swap_invariant sched t1 t2 _ t) // /t2; apply fsc_range1.
      + by rewrite -(swap_job_scheduled_other_times _ t1 t2 j t) //; (apply /neqP; eauto).
    }
    exists j_other; by rewrite  (swap_job_scheduled_other_times) //; do 2! (apply /neqP; eauto).
  Qed.

  (** Lastly, we show that if [t] lies between [t1] and [t2] then work conservation is still maintained. *)
  Lemma non_idle_swap_maintains_work_conservation_BET_t1_t2 :
    work_conserving arr_seq sched ->
    t1 < t <= t2 ->
    exists j_other, scheduled_at swap_sched j_other t.
  Proof.
    move=> WC_sched H_range.
    case: (boolP(t == t1)) => [/eqP EQ| /eqP NEQ]; first by apply non_idle_swap_maintains_work_conservation_t1.
    case: (boolP(t == t2)) => [/eqP EQ'| /eqP NEQ']; first by apply non_idle_swap_maintains_work_conservation_t2.
    move: H_range. move /andP => [LT GE].
    case: (boolP(scheduled_at sched j2 t)) => Hj'.
    - exists j2; by rewrite (swap_job_scheduled_other_times _ t1 t2 j2 t) //; (apply /neqP; eauto).
    - have [j_other j_other_scheduled] : exists j_other, scheduled_at sched j_other t.
      { rewrite /work_conserving in WC_sched. apply (WC_sched j2).
        - by unfold jobs_come_from_arrival_sequence in H_from_arr_seq; apply (H_from_arr_seq _ t2) => //.
        - rewrite/backlogged/job_ready/basic_ready_instance/pending/completed_by.
          apply /andP; split; first (apply /andP; split) => //; last by done.
          + by rewrite /has_arrived; apply (leq_trans H_arrival_j2); apply ltnW.
          + rewrite -ltnNge. apply (leq_ltn_trans) with (service sched j2 t2).
            * by apply service_monotonic.
            * by apply H_completed_jobs_dont_execute. }
      exists j_other. now rewrite  (swap_job_scheduled_other_times) //; (apply /neqP; eauto).
  Qed.

End NonIdleSwapWorkConservationLemmas.

(** ** Work-Conserving Swap Candidates *)

(** Now, we show that work conservation is maintained by the inner-most level
    of [edf_transform], which is [find_swap_candidate]. *)
Section FSCWorkConservationLemmas.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ...and any valid job arrival sequence,... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ...consider an ideal uniprocessor schedule... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ...that is well-behaved (i.e., in which jobs execute only after having
      arrived and only if they are not yet complete)... *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** ...and in which all jobs come from the arrival sequence. *)
  Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

  (** Suppose we are given a job [j1]... *)
  Variable j1: Job.

  (** ...and a point in time [t1]... *)
  Variable t1: instant.

  (** ...at which [j1] is scheduled... *)
  Hypothesis H_not_idle: scheduled_at sched j1 t1.

  (** ...and that is before [j1]'s deadline. *)
  Hypothesis H_deadline_not_missed: t1 < job_deadline j1.

 (** We now show that, if [t2] is a swap candidate returned by
     [find_swap_candidate] for [t1], then swapping the processor allocations at
     the two instants maintains work conservation. *)
  Corollary fsc_swap_maintains_work_conservation :
    work_conserving arr_seq sched ->
    work_conserving arr_seq (swapped sched t1 (edf_trans.find_swap_candidate sched t1 j1)).
  Proof.
    set t2 := edf_trans.find_swap_candidate sched t1 j1.
    have [j2 [t2_not_idle t2_arrival]] : exists j2, scheduled_at sched j2 t2 /\ job_arrival j2 <= t1
        by apply fsc_not_idle.
    have H_range : t1 <= t2 by apply fsc_range1.
    move=> WC_sched j t ARR BL.
    case: (boolP(t == t1)) => [/eqP EQ| /eqP NEQ].
    - by apply (non_idle_swap_maintains_work_conservation_t1 arr_seq _ _ _ j2).
    - case: (boolP(t == t2)) => [/eqP EQ'| /eqP NEQ'].
      + by apply (non_idle_swap_maintains_work_conservation_t2 arr_seq _ _ _ j1).
      + case: (boolP((t <= t1) || (t2 < t))) => [NOT_BET | BET]. (* t <> t2 *)
        * move: NOT_BET; move/orP => [] => NOT_BET.
          { by apply (non_idle_swap_maintains_work_conservation_LEQ_t1 arr_seq _ _ _ H_range _ _ H_not_idle t2_not_idle j).  }
          { by apply (non_idle_swap_maintains_work_conservation_GT_t2 arr_seq _ _ _ H_range _ _ H_not_idle t2_not_idle j). }
        * move: BET; rewrite negb_or. move /andP. case; rewrite <- ltnNge => range1; rewrite <- leqNgt => range2.
          have BET: (t1 < t) && (t <= t2) by apply /andP.
          now apply (non_idle_swap_maintains_work_conservation_BET_t1_t2 arr_seq _ H_completed_jobs_dont_execute H_from_arr_seq _ _ _ _ t2_arrival H_not_idle t2_not_idle ).
  Qed.

End FSCWorkConservationLemmas.

(** ** Work-Conservation of the Point-Wise EDF Transformation *)

(** In the following section, we show that work conservation is maintained by the
    next level of [edf_transform], which is [make_edf_at]. *)
Section MakeEDFWorkConservationLemmas.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and any valid job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ... consider an ideal uniprocessor schedule ... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ... in which all jobs come from the arrival sequence, ... *)
  Hypothesis H_from_arr_seq: jobs_come_from_arrival_sequence sched arr_seq.

  (** ...that is well-behaved,...  *)
  Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** ...and in which no scheduled job misses a deadline. *)
  Hypothesis H_no_deadline_misses: all_deadlines_met sched.

  (** We analyze [make_edf_at] applied to an arbitrary point in time,
     which we denote [t_edf] in the following. *)
  Variable t_edf: instant.

  (** For brevity, let [sched'] denote the schedule obtained from
      [make_edf_at] applied to [sched] at time [t_edf]. *)
  Let sched' := make_edf_at sched t_edf.

  (** We show that, if a schedule is work-conserving, then applying
      [make_edf_at] to it at an arbitrary instant [t_edf] maintains work
      conservation. *)
  Lemma mea_maintains_work_conservation :
    work_conserving arr_seq sched -> work_conserving arr_seq sched'.
  Proof. rewrite /sched'/make_edf_at => WC_sched. destruct (sched t_edf) eqn:E => //.
         apply fsc_swap_maintains_work_conservation => //.
         -  by rewrite scheduled_at_def; apply /eqP => //.
         - apply (scheduled_at_implies_later_deadline sched) => //.
           + rewrite /all_deadlines_met in  (H_no_deadline_misses).
             now apply (H_no_deadline_misses s t_edf); rewrite scheduled_at_def; apply /eqP.
           + by rewrite scheduled_at_def; apply/eqP => //.
  Qed.

End MakeEDFWorkConservationLemmas.

(** ** Work-Conserving EDF Prefix *)

(** On to the next layer, we prove that the [transform_prefix] function at the
    core of the EDF transformation maintains work conservation *)
Section EDFPrefixWorkConservationLemmas.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For any given type of jobs, each characterized by execution
      costs, an arrival time, and an absolute deadline,... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and any valid job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ... consider an ideal uniprocessor schedule,... *)
  Variable sched: schedule (ideal.processor_state Job).

  (** ... an arbitrary finite [horizon], and ... *)
  Variable horizon: instant.

  (** ...let [sched_trans] denote the schedule obtained by transforming
      [sched] up to the horizon. *)
  Let sched_trans := edf_transform_prefix sched horizon.

  (** Let [schedule_behavior_premises] define the premise that a schedule is:
      1) well-behaved,
      2) has all jobs coming from the arrival sequence [arr_seq], and
      3) in which no scheduled job misses its deadline *)
  Definition scheduled_behavior_premises (sched : schedule (processor_state Job)) :=
    jobs_must_arrive_to_execute sched
    /\ completed_jobs_dont_execute sched
    /\ jobs_come_from_arrival_sequence sched arr_seq
    /\ all_deadlines_met sched.

  (** For brevity, let [P] denote the predicate that a schedule satisfies
      [scheduled_behavior_premises] and is work-conserving. *)
  Let P (sched : schedule (processor_state Job)) :=
    scheduled_behavior_premises sched /\ work_conserving arr_seq sched.

  (** We show that if [sched] is work-conserving, then so is [sched_trans]. *)
  Lemma edf_transform_prefix_maintains_work_conservation:
    P sched -> P sched_trans.
  Proof.
    rewrite/sched_trans/edf_transform_prefix. apply (prefix_map_property_invariance ). rewrite /P.
    move=> sched' t  [[H_ARR [H_COMPLETED [H_COME H_all_deadlines_met]]] H_wc_sched].
    rewrite/scheduled_behavior_premises/valid_schedule; split; first split. 
    - by apply mea_jobs_must_arrive.
    - split; last split.
      + by apply mea_completed_jobs.
      + by apply mea_jobs_come_from_arrival_sequence.
      + by apply mea_no_deadline_misses.
    - by apply mea_maintains_work_conservation.
  Qed.

End EDFPrefixWorkConservationLemmas.

(** ** Work-Conservation of the EDF Transformation *)

(** Finally, having established that [edf_transform_prefix] maintains work
    conservation, we go ahead and prove that [edf_transform] maintains work
    conservation, too. *)
Section EDFTransformWorkConservationLemmas.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For any given type of jobs, each characterized by execution
      costs, an arrival time, and an absolute deadline,... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... and any valid job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.
  Hypothesis H_arr_seq_valid: valid_arrival_sequence arr_seq.

  (** ... consider a valid ideal uniprocessor schedule ... *)
  Variable sched: schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid: valid_schedule sched arr_seq.

  (** ...and in which no scheduled job misses a deadline. *)
  Hypothesis H_no_deadline_misses: all_deadlines_met sched.

  (** We first note that [sched] satisfies [scheduled_behavior_premises]. *)
  Lemma sched_satisfies_behavior_premises : scheduled_behavior_premises arr_seq sched.
  Proof.
    split; [ apply (jobs_must_arrive_to_be_ready sched) | split; [ apply (completed_jobs_are_not_ready sched) | split]].
    all: by try apply H_sched_valid.
  Qed.

  (** We prove that, if the given schedule [sched] is work-conserving, then the
      schedule that results from transforming it into an EDF schedule is also
      work-conserving. *)
  Lemma edf_transform_maintains_work_conservation :
    work_conserving arr_seq sched -> work_conserving arr_seq (edf_transform sched).
  Proof.
    move=> WC_sched j t ARR.
    set sched_edf := edf_transform sched.
    have IDENT:  identical_prefix sched_edf (edf_transform_prefix sched t.+1) t.+1
      by rewrite /sched_edf/edf_transform => t' LE_t; apply (edf_prefix_inclusion) => //; apply sched_satisfies_behavior_premises.
    rewrite (backlogged_prefix_invariance _ _ (edf_transform_prefix sched t.+1) t.+1) // => BL;
            last by apply basic_readiness_nonclairvoyance.
    have WC_trans: work_conserving arr_seq  (edf_transform_prefix sched (succn t))
      by apply edf_transform_prefix_maintains_work_conservation; split => //; apply sched_satisfies_behavior_premises.
    move: (WC_trans _ _ ARR BL) => [j_other SCHED_AT].
    exists j_other.
    now rewrite (identical_prefix_scheduled_at _ (edf_transform_prefix sched t.+1) t.+1) //.
  Qed.

End EDFTransformWorkConservationLemmas.
