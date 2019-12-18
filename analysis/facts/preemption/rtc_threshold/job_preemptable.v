Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.facts.behavior.all.
Require Export prosa.model.task.preemption.parameters.

(** * Run-to-Completion Threshold *) 
(** In this section, we provide a few basic properties 
    of run-to-completion-threshold-compliant schedules. *)
Section RunToCompletionThreshold.

  (**  Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume existence of a function
      mapping jobs to theirs preemption points. *)
  Context `{JobPreemptable Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched: schedule PState.

  (** Assume that the preemption model is valid. *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.

  (** Consider an arbitrary job j from the arrival sequence. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  
  (** First we prove a few auxiliary lemmas about 
      [job_preemption_points]. *)
  Section AuxiliaryLemmas.
    
    (** We prove that the sequence of preemption points of a zero-cost
        job consists of one element -- 0. *)
    Lemma preemption_points_of_zero_cost_job:
      job_cost j = 0 -> 
      job_preemption_points j = [::0].
    Proof.
      intros ZERO.
      destruct (H_valid_preemption_model j) as [A1 [A2 [A3 A4]]]; auto.
      unfold job_preemption_points; rewrite ZERO; simpl.
      simpl; unfold job_cannot_become_nonpreemptive_before_execution in *.
        by rewrite A1.
    Qed.

    (** For a positive-cost job, 0 ... *)
    Lemma zero_in_preemption_points:
      0 < job_cost j -> 
      0 \in job_preemption_points j.
    Proof.
      intros POS.
      unfold job_preemption_points, range.
      destruct (H_valid_preemption_model j) as [A1 [A2 [A3 A4]]]; auto.
      unfold job_cannot_become_nonpreemptive_before_execution in *.
      rewrite index_iota_lt_step; last by done.
        by simpl; rewrite A1 in_cons eq_refl.
    Qed.
    
    (** ... and [job_cost] are in preemption points. *)
    Lemma job_cost_in_preemption_points:
      0 < job_cost j -> 
      job_cost j \in job_preemption_points j.
    Proof.
      intros POS.
      unfold job_preemption_points, range, index_iota; rewrite subn0 -addn1.
      rewrite iota_add add0n filter_cat mem_cat.
      apply/orP; right; simpl.
      destruct (H_valid_preemption_model j) as [A1 [A2 [A3 A4]]]; auto.
      unfold job_cannot_be_nonpreemptive_after_completion in *.
        by rewrite A2 in_cons eq_refl.
    Qed.

    (** Therefore, for a positive-cost job size of the sequence of
        preemption points is at least two. *)
    Lemma size_of_preemption_points:
      0 < job_cost j -> 
      2 <= size (job_preemption_points j).
    Proof.
      intros POS.
      replace 2 with (size [::0; job_cost j]); last by done.
      apply subseq_leq_size.
      - apply/andP; split. rewrite !in_cons Bool.negb_orb.
        + apply/andP; split. by rewrite neq_ltn POS. by done.
        + apply/andP; split; by done. 
      - intros ρ; rewrite !in_cons; move => /orP [/eqP EQ| /orP [/eqP Cost | C]].
        + by subst; apply zero_in_preemption_points.
        + by subst; apply job_cost_in_preemption_points.
        + by done.
    Qed.

    (** Next we show that the sequence of preemption points is a non-decreasing sequence. *)
    Lemma preemption_points_nondecreasing:
      nondecreasing_sequence (job_preemption_points j).
    Proof. by apply increasing_implies_nondecreasing, iota_is_increasing_sequence. Qed.

    (** Next, we prove that the last element of the sequence of
        preemption points is [job_cost]. *)
    Lemma job_cost_is_last_element_of_preemption_points:
      job_cost j = last0 (job_preemption_points j).
    Proof.
      unfold job_preemption_points.
      edestruct H_valid_preemption_model as [A1 [A2 [A3 A4]]]; eauto 2.
      erewrite last0_filter.
      + by apply/eqP; apply eq_refl.
      + unfold range, index_iota; rewrite subn0 -addn1.
          by rewrite iota_add; destruct (iota 0 (job_cost j)). 
      + unfold range, index_iota; rewrite subn0 -addn1.
          by rewrite iota_add last0_cat //. 
      + by apply A2.
    Qed.
    
    (** Last non-preemptive segment of a positive-cost job has positive length. *)
    Lemma job_last_nonpreemptive_segment_positive:
      job_cost_positive j ->
      0 < job_last_nonpreemptive_segment j.
    Proof.
      intros COST. unfold job_last_nonpreemptive_segment.
      rewrite last0_nth function_of_distances_is_correct subn_gt0.
      rewrite [size _]pred_Sn -addn1-addn1.
      rewrite -size_of_seq_of_distances ?addn1; last by apply size_of_preemption_points.
      rewrite prednK; last first.
      { rewrite -(leq_add2r 1) !addn1 prednK.
        - apply size_of_preemption_points; eauto.
        - rewrite ltnW //; apply size_of_preemption_points; eauto.
      }
      apply iota_is_increasing_sequence; apply/andP; split. 
      - rewrite -(leq_add2r 2) !addn2.
        rewrite prednK; first by done. 
        rewrite -(leq_add2r 1) !addn1.
        rewrite prednK.
        + by apply size_of_preemption_points.
        + by rewrite ltnW //; apply size_of_preemption_points.
      - rewrite -(leq_add2r 1) !addn1.
        unfold job_preemption_points, range.
        rewrite prednK ?ltnS; first by done. 
          by rewrite ltnW //; apply size_of_preemption_points.
    Qed.

    (** Max nonpreemptive segment of a positive-cost job has positive length. *)
    Lemma job_max_nonpreemptive_segment_positive:
      job_cost_positive j ->
      0 < job_max_nonpreemptive_segment j.
    Proof.
      intros COST.
      eapply leq_trans.
      - by apply job_last_nonpreemptive_segment_positive.
      - by apply last_of_seq_le_max_of_seq.        
    Qed.
    
    (** Next we show that max nonpreemptive segment is at most the
      cost of a job. *)
    Lemma job_max_nonpreemptive_segment_le_job_cost:
      job_max_nonpreemptive_segment j <= job_cost j.
    Proof.
      eapply leq_trans.
      apply max_distance_in_seq_le_last_element_of_seq; apply preemption_points_nondecreasing.
      destruct (H_valid_preemption_model j) as [A1 [A2 [A3 A4]]]; auto.
      case: (posnP (job_cost j)) => [ZERO|POSt].
      { unfold job_preemption_points; rewrite ZERO.
        simpl; unfold job_cannot_become_nonpreemptive_before_execution in *.
          by rewrite A1.
      }
      { eapply leq_trans; first apply last_of_seq_le_max_of_seq.
        rewrite job_cost_is_last_element_of_preemption_points.
        apply last_is_max_in_nondecreasing_seq; first by apply preemption_points_nondecreasing.
        apply max0_in_seq.
        have LL := size_of_preemption_points POSt.
          by destruct (job_preemption_points j). 
      } 
    Qed.

    (** We also show that last nonpreemptive segment is at most the
        cost of a job. *)
    Lemma job_last_nonpreemptive_segment_le_job_cost:
      job_last_nonpreemptive_segment j <= job_cost j.
    Proof.
      eapply leq_trans.
      - apply last_of_seq_le_max_of_seq.
      - apply job_max_nonpreemptive_segment_le_job_cost.
    Qed.

  End AuxiliaryLemmas.

  (** We prove that the run-to-completion threshold is positive for
        any job with positive cost. I.e., in order to become
        non-preemptive a job must receive at least one unit of
        service. *)
  Lemma job_run_to_completion_threshold_positive:
    job_cost_positive j ->
    0 < job_run_to_completion_threshold j.
  Proof.
    intros COST; unfold job_run_to_completion_threshold, ε.
    have N1 := job_last_nonpreemptive_segment_positive COST.
    have N2 := job_last_nonpreemptive_segment_le_job_cost.
    ssromega.
  Qed.
  
  (** Next we show that the run-to-completion threshold is at most
        the cost of a job. *)
  Lemma job_run_to_completion_threshold_le_job_cost:
    job_run_to_completion_threshold j <= job_cost j.
  Proof. by apply leq_subr. Qed.

  
  (** We prove that a job cannot be preempted 
        during execution of the last segment. *)
  Lemma job_cannot_be_preempted_within_last_segment:
    forall (ρ : duration), 
      job_run_to_completion_threshold j <= ρ < job_cost j ->
      ~~ job_preemptable j ρ.
  Proof.
    move => ρ /andP [GE LT].
    apply/negP; intros C.
    have POS : 0 < job_cost j; first by ssromega.
    rewrite /job_run_to_completion_threshold subnBA in GE; last by apply job_last_nonpreemptive_segment_positive.
    rewrite -subh1 in GE; [rewrite addn1 in GE | by apply job_last_nonpreemptive_segment_le_job_cost]. 
    rewrite job_cost_is_last_element_of_preemption_points in LT, GE.
    rewrite last_seq_minus_last_distance_seq in GE; last by apply preemption_points_nondecreasing.
    have EQ := antidensity_of_nondecreasing_seq.
    specialize (EQ (job_preemption_points j) ρ (size (job_preemption_points j)).-2 ).
    feed_n 2 EQ; first by apply preemption_points_nondecreasing.
    { apply/andP; split; first by done.
      rewrite prednK; first by rewrite -last0_nth.
      rewrite -(leq_add2r 1) !addn1 prednK.
      - by apply size_of_preemption_points.
      - by eapply leq_trans; last apply size_of_preemption_points.
    }
    move: EQ => /negP EQ; apply: EQ.
    apply conversion_preserves_equivalence; try done.
    eapply leq_trans; first by apply ltnW; exact LT.
      by rewrite job_cost_is_last_element_of_preemption_points.
  Qed.
  
  (** In order to get a consistent schedule, the scheduler should respect 
         the notion of run-to-completion threshold. We assume that, after 
         a job reaches its run-to-completion threshold, it cannot be preempted
         until its completion. *)
  Lemma job_nonpreemptive_after_run_to_completion_threshold: 
    forall t t',
      t <= t' ->
      job_run_to_completion_threshold j <= service sched j t ->
      ~~ completed_by sched j t' ->
      scheduled_at sched j t'.
  Proof.
    intros ? ? LE TH COM.
    apply H_valid_preemption_model; first by done.
    apply job_cannot_be_preempted_within_last_segment; apply/andP; split.
    - by apply leq_trans with (service sched j t); last apply service_monotonic.
    - by rewrite ltnNge.
  Qed.

End RunToCompletionThreshold.

(** We add the above lemmas into a "Hint Database" basic_facts, so Coq 
    will be able to apply them automatically. *)   
Hint Resolve job_run_to_completion_threshold_le_job_cost : basic_facts.
