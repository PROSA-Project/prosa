Require Export prosa.analysis.facts.preemption.job.limited.

(** Furthermore, we assume the task model with fixed preemption points. *)
Require Import prosa.model.task.preemption.limited_preemptive.
Require Import prosa.model.preemption.limited_preemptive.

(** * Platform for Models with Limited Preemptions *)
(** In this section, we prove that instantiation of functions
    [job_preemptable and task_preemption_points] to the
    limited preemptions model indeed defines a valid preemption model
    with bounded non-preemptive regions. *)
Section LimitedPreemptionsModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** In addition, we assume the existence of functions mapping a
      job and task to the sequence of its preemption points. *)
  Context `{JobPreemptionPoints Job}.
  Context `{TaskPreemptionPoints Task}.
  
  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** Next, consider any ideal uni-processor preemption-aware schedule
      of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_schedule_respects_preemption_model:
    schedule_respects_preemption_model arr_seq sched.  
    
  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider an arbitrary task set ts. *)     
  Variable ts : list Task.

  (** Next, we assume that preemption points are defined by the model
      with fixed preemption points. *)    
  Hypothesis H_valid_fixed_preemption_points_model:
    valid_fixed_preemption_points_model arr_seq ts.

  (** Then we prove that functions [job_preemptable and
      task_preemption_points] define a model with bounded non-preemptive
      regions. *)       
  Lemma fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions:
    model_with_bounded_nonpreemptive_segments arr_seq .
  Proof.
    intros j ARR.
    move: H_valid_fixed_preemption_points_model => [LIM FIX].
    move: (LIM) => [BEG [END NDEC]]; move: (FIX) => [A1 [A2 [A3 [A4 A5]]]].
    case: (posnP (job_cost j)) => [ZERO|POS].
    - split.
      rewrite /job_respects_max_nonpreemptive_segment /job_max_nonpreemptive_segment
              /lengths_of_segments /parameter.job_preemption_points; rewrite ZERO; simpl.
      rewrite /job_preemptable /limited_preemptions_model; erewrite zero_in_preemption_points; eauto 2.
      + move => progr; rewrite ZERO leqn0; move => /andP [_ /eqP LE].
        exists 0; rewrite LE; split; first by apply/andP; split.
          by eapply zero_in_preemption_points; eauto 2.
    - split; last (move => progr /andP [_ LE]; destruct (progr \in job_preemption_points j) eqn:NotIN).
      + rewrite /job_respects_max_nonpreemptive_segment
                /job_max_nonpreemptive_segment /lengths_of_segments; erewrite job_parameters_max_np_to_job_limited; eauto.
          by apply max_of_dominating_seq; intros; apply A5.
      + exists progr; split; first apply/andP; first split; rewrite ?leq_addr; by done. 
      + move: NotIN => /eqP; rewrite eqbF_neg; move => NotIN. 
        edestruct (work_belongs_to_some_nonpreemptive_segment arr_seq) as [x [SIZE2 N]]; eauto 2. move: N => /andP [N1 N2].
        set ptl := nth 0 (job_preemption_points j) x.
        set ptr := nth 0 (job_preemption_points j) x.+1.
        exists ptr; split; first last.
        * by unfold job_preemptable, limited_preemptions_model; apply mem_nth.
        * apply/andP; split; first by apply ltnW.
          apply leq_trans with (ptl + (job_max_nonpreemptive_segment j - ε) + 1); first last.
          -- rewrite addn1 ltn_add2r; apply N1. 
          -- unfold job_max_nonpreemptive_segment.
             rewrite -addnA -leq_subLR -(leq_add2r 1).
             rewrite [in X in _ <= X]addnC -leq_subLR.                
             rewrite !subn1 !addn1 prednK. 
             { rewrite -[_.+1.-1]pred_Sn. rewrite /lengths_of_segments.
               erewrite job_parameters_max_np_to_job_limited; eauto.
                 by apply distance_between_neighboring_elements_le_max_distance_in_seq. }
             { rewrite /lengths_of_segments; erewrite job_parameters_max_np_to_job_limited; eauto.
               apply max_distance_in_nontrivial_seq_is_positive; first by eauto 2.
               exists 0, (job_cost j); repeat split. 
               - by eapply zero_in_preemption_points; eauto. 
               - by eapply job_cost_in_nonpreemptive_points; eauto. 
               - by apply/eqP; rewrite eq_sym -lt0n; apply POS. 
             } 
  Qed.
  
  (** Which together with lemma [valid_fixed_preemption_points_model]
      gives us the fact that functions [job_preemptable and
      task_preemption_points] defines a valid preemption model with
      bounded non-preemptive regions. *) 
  Corollary fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.
  Proof.
    split.
    - by apply valid_fixed_preemption_points_model_lemma; destruct H_valid_fixed_preemption_points_model.
    - by apply fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions.
  Qed.
  
End LimitedPreemptionsModel. 

(** We add the above lemma into a "Hint Database" basic_facts, so Coq will be able to apply them automatically. *)
Hint Resolve
     valid_fixed_preemption_points_model_lemma
     fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
     fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions : basic_facts.
