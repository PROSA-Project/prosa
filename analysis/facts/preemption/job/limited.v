Require Export prosa.model.schedule.limited_preemptive.
Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.facts.behavior.all.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.facts.model.ideal_schedule.

(** Throughout this file, we assume the job model with limited
    preemption points. *)
Require Import prosa.model.preemption.limited_preemptive.

(** * Platform for Models with Limited Preemptions *)
(** In this section, we prove that instantiation of predicate
    [job_preemptable] to the model with limited preemptions
    indeed defines a valid preemption model. *)
Section ModelWithLimitedPreemptions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, assume the existence of a function that maps a job
      to the sequence of its preemption points. *)
  Context `{JobPreemptionPoints Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** Next, consider any limited ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_schedule_respects_preemption_model:
    schedule_respects_preemption_model arr_seq sched.
  
  (** ...where jobs do not execute after their completion. *)
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** Next, we assume that preemption points are defined by the
      job-level model with limited preemptions. *)
  Hypothesis H_valid_limited_preemptions_job_model:
    valid_limited_preemptions_job_model arr_seq.
  
  (** First, we prove a few auxiliary lemmas. *)
  Section AuxiliaryLemmas.

    (** Consider a job j. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.

    (** Recall that 0 is a preemption point. *)
    Remark zero_in_preemption_points: 0 \in job_preemption_points j.
    Proof. by apply H_valid_limited_preemptions_job_model. Qed.                
    
    (** Using the fact that [job_preemption_points] is a
        non-decreasing sequence, we prove that the first element of
        [job_preemption_points] is 0. *)
    Lemma zero_is_first_element: first0 (job_preemption_points j) = 0.
    Proof.
      have F := zero_in_preemption_points.
      destruct H_valid_limited_preemptions_job_model as [_ [_ C]]; specialize (C j H_j_arrives).
        by apply nondec_seq_zero_first.
    Qed.
    
    (** We prove that the list of preemption points is not empty. *)
    Lemma list_of_preemption_point_is_not_empty:
      0 < size (job_preemption_points j).
    Proof.
      move: H_valid_limited_preemptions_job_model => [BEG [END _]].
      apply/negPn/negP; rewrite -eqn0Ngt; intros CONTR; rewrite size_eq0 in CONTR.
      specialize (BEG j H_j_arrives).
        by rewrite /beginning_of_execution_in_preemption_points (eqbool_to_eqprop CONTR) in BEG.
    Qed.

    (** Next, we prove that the cost of a job is a preemption point. *)
    Lemma job_cost_in_nonpreemptive_points: job_cost j \in job_preemption_points j.
    Proof.
      move: H_valid_limited_preemptions_job_model => [BEG [END _]].
      move: (END _ H_j_arrives) => EQ.
      rewrite -EQ; clear EQ.
      rewrite /last0 -nth_last.
      apply/(nthP 0).
      exists ((size (job_preemption_points j)).-1); last by done. 
      rewrite -(leq_add2r 1) !addn1 prednK //.
        by apply list_of_preemption_point_is_not_empty.
    Qed.

    (** As a corollary, we prove that the sequence of non-preemptive
        points of a job with positive cost contains at least 2
        points. *)
    Corollary number_of_preemption_points_at_least_two:
      job_cost_positive j ->
      2 <= size (job_preemption_points j).
    Proof.
      intros POS.
      move: H_valid_limited_preemptions_job_model => [BEG [END _]]. 
      have EQ: 2 = size [::0; job_cost j]; first by done. 
      rewrite EQ; clear EQ.
      apply subseq_leq_size.
      rewrite !cons_uniq.
      { apply/andP; split.
        rewrite in_cons negb_or; apply/andP; split; last by done.
        rewrite neq_ltn; apply/orP; left; eauto 2.
        apply/andP; split; by done. } 
      intros t EQ; move: EQ; rewrite !in_cons.
      move => /orP [/eqP EQ| /orP [/eqP EQ|EQ]]; last by done.
      - by rewrite EQ; apply zero_in_preemption_points.
      - by rewrite EQ; apply job_cost_in_nonpreemptive_points.
    Qed.

    (** Next we prove that "anti-density" property (from
        [preemption.util] file) holds for [job_preemption_point j]. *)
    Lemma antidensity_of_preemption_points:
      forall (ρ : work),
        ρ <= job_cost j -> 
        ~~ (ρ \in job_preemption_points j) -> 
        first0 (job_preemption_points j) <= ρ < last0 (job_preemption_points j). 
    Proof.
      intros ρ LE NotIN.
      move: H_valid_limited_preemptions_job_model => [BEG [END NDEC]].
      apply/andP; split.
      - by rewrite zero_is_first_element.
      - rewrite END; last by done.
        rewrite ltn_neqAle; apply/andP; split; last by done.
        apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
        rewrite CONTR in NotIN.
        move: NotIN => /negP NIN; apply: NIN. 
          by apply job_cost_in_nonpreemptive_points.
    Qed.

    (** We also prove that any work that doesn't belong to
        preemption points of job j is placed strictly between two
        neighboring preemption points. *)
    Lemma work_belongs_to_some_nonpreemptive_segment:
      forall (ρ : work),
        ρ <= job_cost j ->
        ~~ (ρ \in job_preemption_points j)-> 
        exists n,
          n.+1 < size (job_preemption_points j) /\
          nth 0 (job_preemption_points j) n < ρ < nth 0 (job_preemption_points j) n.+1.
    Proof.
      intros ρ LE NotIN.
      case: (posnP (job_cost j)) => [ZERO|POS].
      { exfalso; move: NotIN => /negP NIN; apply: NIN.
        move: LE. rewrite ZERO leqn0; move => /eqP ->.
          by apply zero_in_preemption_points. }
      move: (belonging_to_segment_of_seq_is_total
               (job_preemption_points j) ρ (number_of_preemption_points_at_least_two POS)
               (antidensity_of_preemption_points _ LE NotIN)) => [n [SIZE2 /andP [N1 N2]]].
      exists n; split; first by done.
      apply/andP; split; last by done.
      move: N1; rewrite leq_eqVlt; move => /orP [/eqP EQ | G]; last by done.
      exfalso.
      move: NotIN => /negP CONTR; apply: CONTR.
      rewrite -EQ; clear EQ.
      rewrite mem_nth //.
        by apply ltnW. 
    Qed.

    (** Recall that file [job.parameters] also defines notion of
        preemption points.  And note that
        [job.parameter.job_preemption_points] cannot have a
        duplicating preemption points. Therefore, we need additional
        lemmas to relate [job.parameter.job_preemption_points] and
        [limited.job_preemption_points]]. *)

    (** First we show that the length of the last non-preemptive
        segment of [job.parameter.job_preemption_points] is equal to
        the length of the last non-empty non-preemptive segment of
        [limited.job_preemption_points]. *)
    Lemma job_parameters_last_np_to_job_limited:
        last0 (distances (parameter.job_preemption_points j)) =
        last0 (filter (fun x => 0 < x) (distances (job_preemption_points j))).
    Proof.
      destruct H_valid_limited_preemptions_job_model as [A1 [A2 A3]].
      unfold parameter.job_preemption_points, job_preemptable, limited_preemptions_model.
      intros; rewrite distances_iota_filtered; eauto.
      rewrite -A2 //.
        by intros; apply last_is_max_in_nondecreasing_seq; eauto 2.
    Qed.

    (** Next we show that the length of the max non-preemptive
        segment of [job.parameter.job_preemption_points] is equal to
        the length of the max non-preemptive segment of
        [limited.job_preemption_points]. *)
    Lemma job_parameters_max_np_to_job_limited:
      max0 (distances (parameter.job_preemption_points j)) =
      max0 (distances (job_preemption_points j)).
    Proof.
      destruct H_valid_limited_preemptions_job_model as [A1 [A2 A3]].
      unfold parameter.job_preemption_points, job_preemptable, limited_preemptions_model.
      intros; rewrite distances_iota_filtered; eauto 2.
      rewrite max0_rem0 //.
      rewrite -A2 //.
        by intros; apply last_is_max_in_nondecreasing_seq; eauto 2.      
    Qed.
    
  End AuxiliaryLemmas.

  (** We prove that the [fixed_preemption_point_model] function
      defines a valid preemption model. *)                 
  Lemma valid_fixed_preemption_points_model_lemma:
    valid_preemption_model arr_seq sched.
  Proof. 
    intros j ARR; repeat split. 
    { by apply zero_in_preemption_points. }
    { by apply job_cost_in_nonpreemptive_points. }
    { by move => t NPP; apply H_schedule_respects_preemption_model. }
    { intros t NSCHED SCHED. 
      have SERV: service sched j t = service sched j t.+1.
      { rewrite -[service sched j t]addn0 /service /service_during; apply/eqP. 
        rewrite big_nat_recr //=.
        rewrite eqn_add2l eq_sym.
        rewrite scheduled_at_def in NSCHED.
          by rewrite eqb0. }
      rewrite -[job_preemptable _ _]Bool.negb_involutive.
      apply/negP; intros CONTR.
      move: NSCHED => /negP NSCHED; apply: NSCHED.
      apply H_schedule_respects_preemption_model; first by done.
        by rewrite SERV.
    }            
  Qed.
  
End ModelWithLimitedPreemptions.
Hint Resolve valid_fixed_preemption_points_model_lemma : basic_facts.
