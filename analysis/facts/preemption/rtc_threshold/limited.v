Require Export prosa.analysis.facts.preemption.task.limited.
Require Export prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.

(** Furthermore, we assume the task model with fixed preemption points. *)
Require Import prosa.model.task.preemption.limited_preemptive.
Require Import prosa.model.preemption.limited_preemptive.

(** * Task's Run to Completion Threshold *)
(** In this section, we prove that instantiation of function [task run
    to completion threshold] to the model with limited preemptions
    indeed defines a valid run-to-completion threshold function. *)
Section TaskRTCThresholdLimitedPreemptions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskPreemptionPoints Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptionPoints Job}.
  
  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any ideal uniprocessor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_schedule_respects_preemption_model:
    schedule_respects_preemption_model arr_seq sched.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider an arbitrary task set ts. *)
  Variable ts : seq Task.
  
  (** Assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Consider the model with fixed preemption points. I.e., each task
      is divided into a number of non-preemptive segments by inserting
      statically predefined preemption points. *)
  Hypothesis H_valid_fixed_preemption_points_model:
    valid_fixed_preemption_points_model arr_seq ts.

  (** And consider any task from task set ts with positive cost. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts. 
  Hypothesis H_positive_cost : 0 < task_cost tsk.

  (** We start by proving an auxiliary lemma. Note that since [tsk]
      has a positive cost, [task_preemption_points tsk] contains [0]
      and [task_cost tsk]. Thus, [2 <= size (task_preemption_points tsk)]. *)
  Remark number_of_preemption_points_in_task_at_least_two: 2 <= size (task_preemption_points tsk).
  Proof.
    move: (H_valid_fixed_preemption_points_model) => [MLP [BEG [END [INCR [HYP1 [HYP2 HYP3]]]]]].
    have Fact2: 0 < size (task_preemption_points tsk).
    { apply/negPn/negP; rewrite -eqn0Ngt; intros CONTR; move: CONTR => /eqP CONTR.
      move: (END _ H_tsk_in_ts) => EQ.
      move: EQ; rewrite /last0 -nth_last nth_default; last by rewrite CONTR.
        by intros; move: (H_positive_cost); rewrite EQ ltnn. 
    } 
    have EQ: 2 = size [::0; task_cost tsk]; first by done. 
    rewrite EQ; clear EQ.
    apply subseq_leq_size.
    rewrite !cons_uniq.
    { apply/andP; split.
      rewrite in_cons negb_or; apply/andP; split; last by done.
      rewrite neq_ltn; apply/orP; left; eauto 2.
      apply/andP; split; by done. } 
    intros t EQ; move: EQ; rewrite !in_cons.
    move => /orP [/eqP EQ| /orP [/eqP EQ|EQ]]; last by done.
    { rewrite EQ; clear EQ.
      move: (BEG _ H_tsk_in_ts) => EQ.
      rewrite -EQ; clear EQ.
      rewrite /first0 -nth0. 
      apply/(nthP 0).
      exists 0; by done.
    }
    { rewrite EQ; clear EQ.
      move: (END _ H_tsk_in_ts) => EQ.
      rewrite -EQ; clear EQ.
      rewrite /last0 -nth_last.
      apply/(nthP 0).
      exists ((size (task_preemption_points tsk)).-1); last by done. 
        by rewrite -(leq_add2r 1) !addn1 prednK //.
    }
  Qed.
    
  (** Then, we prove that [task_run_to_completion_threshold] function
      defines a valid task's run to completion threshold. *)   
  Lemma limited_valid_task_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.
  Proof.
    split; first by rewrite /task_rtc_bounded_by_cost leq_subr.
    intros ? ARR__j TSK__j. move: (H_valid_fixed_preemption_points_model) => [LJ LT].
    move: (LJ) (LT) => [ZERO__job [COST__job SORT__job]] [ZERO__task [COST__task [SORT__task [T4 [T5 T6]]]]].
    rewrite /job_run_to_completion_threshold /task_run_to_completion_threshold /limited_preemptions
            /job_last_nonpreemptive_segment /task_last_nonpr_segment /lengths_of_segments.
    case: (posnP (job_cost j)) => [Z|POS]; first by rewrite Z; compute.
    have J_RTCT__pos : 0 < job_last_nonpreemptive_segment j
      by eapply job_last_nonpreemptive_segment_positive; eauto using valid_fixed_preemption_points_model_lemma.
    have T_RTCT__pos : 0 < task_last_nonpr_segment tsk.
    { unfold job_respects_segment_lengths, task_last_nonpr_segment in *.
      rewrite last0_nth; apply T6; eauto 2.
      have F: 1 <= size (distances (task_preemption_points tsk)).
      { apply leq_trans with (size (task_preemption_points tsk) - 1). 
        - have F := number_of_preemption_points_in_task_at_least_two; ssromega.
        - rewrite [in X in X - 1]size_of_seq_of_distances; [ssromega | apply number_of_preemption_points_in_task_at_least_two].
      } ssromega.
    }    
    have J_RTCT__le : job_last_nonpreemptive_segment j <= job_cost j
      by eapply job_last_nonpreemptive_segment_le_job_cost; eauto using valid_fixed_preemption_points_model_lemma.
    have T_RTCT__le : task_last_nonpr_segment tsk <= task_cost tsk.
    { unfold task_last_nonpr_segment. rewrite -COST__task //.
      eapply leq_trans; last by apply max_distance_in_seq_le_last_element_of_seq; eauto 2.
        by apply last_of_seq_le_max_of_seq.
    } 
    rewrite subnBA // subnBA // -addnBAC // -addnBAC // !addn1 ltnS.
    erewrite job_parameters_last_np_to_job_limited; eauto 2.
    rewrite distances_positive_undup //; last by apply SORT__job. 
    have -> : job_cost j = last0 (undup (job_preemption_points j)) by rewrite last0_undup; [rewrite -COST__job | apply SORT__job].
    rewrite last_seq_minus_last_distance_seq; last by apply nondecreasing_sequence_undup, SORT__job. 
    apply leq_trans with( nth 0 (job_preemption_points j) ((size (job_preemption_points j)).-2)); first by apply undup_nth_le; eauto 2.
    have -> : task_cost tsk = last0 (task_preemption_points tsk) by rewrite COST__task. 
    rewrite last_seq_minus_last_distance_seq; last by apply SORT__task.
    rewrite -TSK__j.
    rewrite T4; last by done.
    apply domination_of_distances_implies_domination_of_seq; try eauto 2.
    - erewrite zero_is_first_element; eauto.
    - eapply number_of_preemption_points_at_least_two; eauto 2. 
    - by rewrite TSK__j; eapply number_of_preemption_points_in_task_at_least_two.  
    - by apply SORT__task; rewrite TSK__j.
  Qed.
  
End TaskRTCThresholdLimitedPreemptions.
Hint Resolve limited_valid_task_run_to_completion_threshold : basic_facts.
