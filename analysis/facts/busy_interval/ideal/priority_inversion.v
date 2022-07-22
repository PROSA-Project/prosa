Require Export prosa.analysis.definitions.priority_inversion.
Require Export prosa.analysis.facts.busy_interval.priority_inversion.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.
Require Export prosa.analysis.facts.model.ideal.schedule.

(** * Lemmas about Priority Inversion for ideal uni-processors *)
(** In this section, we prove a few useful properties about the notion
    of priority inversion for ideal uni-processors. *)
Section PIIdealProcessorModelLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority relation,
     and assume that this relation is reflexive. *)
  Context `{JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.

  (** Let [tsk] be any task to be analyzed. *)
  Variable tsk : Task.

  (** Consider a job [j] of task [tsk]. In this subsection, job [j] is
      deemed to be the main job with respect to which the priority
      inversion is computed. *)
  Variable j : Job.
  Hypothesis H_j_tsk : job_of_task tsk j.

  (** Consider a time instant [t]. *)
  Variable t : instant.

  (** We prove that if the processor is idle at time [t], then there
      is no priority inversion. *)
  Lemma idle_implies_no_priority_inversion :
    is_idle sched t ->
    priority_inversion_dec arr_seq sched j t = false.
  Proof.
    unfold priority_inversion_dec; intros IDLE.
    apply/eqP; rewrite eqbF_neg negb_and Bool.negb_involutive; apply/orP; right.
    apply/hasPn; intros s IN.
    rewrite negb_and Bool.negb_involutive; apply/orP; left.
    by move: IDLE => /eqP; rewrite scheduled_at_def => ->.
  Qed.

  (** Next, consider an additional job [j'] and assume it is scheduled
      at time [t]. *)
  Variable j' : Job.
  Hypothesis H_j'_sched : scheduled_at sched j' t.

  (** Then, we prove that from point of view of job [j], priority
      inversion appears iff [s] has lower priority than job [j]. *)
  Lemma priority_inversion_equiv_sched_lower_priority :
    priority_inversion_dec arr_seq sched j t = ~~ hep_job j' j.
  Proof.
    rewrite /priority_inversion_dec.
    destruct (scheduled_at _ j _) eqn:SCHED2; rewrite //=.
    { have EQ: j = j' by eapply ideal_proc_model_is_a_uniprocessor_model; eauto.
      subst j'; symmetry; apply/eqP; rewrite eqbF_neg Bool.negb_involutive.
      by apply (H_priority_is_reflexive 0).
    }
    { destruct (hep_job) eqn:HEP; rewrite //=.
      - apply/eqP; rewrite eqbF_neg; apply/hasPn; intros l IN.
        destruct (scheduled_at _ l _) eqn:SCHED3; rewrite //=.
        have EQ: l = j' by eapply ideal_proc_model_is_a_uniprocessor_model; eauto.
        by subst j'; rewrite HEP.
      - apply/hasP; exists j'.  rt_eauto.
        by rewrite H_j'_sched HEP.
    }
  Qed.

  (** Assume that [j'] has higher-or-equal priority than job [j], then
      we prove that there is no priority inversion for job [j]. *)
  Lemma sched_hep_implies_no_priority_inversion :
    hep_job j' j ->
    priority_inversion_dec arr_seq sched j t = false.
  Proof.
    intros HEP.
    apply/negP; intros CONTR; move: CONTR => /andP [NSCHED /hasP [j'' _ /andP [SCHED PRIO]]].
    have HF := ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_j'_sched SCHED; subst j'.
    by rewrite HEP in PRIO.
  Qed.

  (** Assume that [j'] has lower priority than job [j], then
      we prove that [j] incurs priority inversion. *)
    Lemma sched_lp_implies_priority_inversion :
      ~~ hep_job j' j ->
      priority_inversion_dec arr_seq sched j t.
    Proof.
      intros LP.
      apply/andP; split.
      - apply/negP; intros SCHED.
        have HF := ideal_proc_model_is_a_uniprocessor_model _ _ _ _ H_j'_sched SCHED; subst j'.
        move: (LP) => /negP HH; apply: HH.
        specialize (H_priority_is_reflexive 0).
        unfold hep_job_at, JLFP_to_JLDP in *.
        by erewrite H_priority_is_reflexive; eauto 2.
      - apply/hasP.
        exists j'.
        + apply arrived_between_implies_in_arrivals; eauto 2.
          apply/andP; split; try done.
          by rewrite ltnS; apply H_jobs_must_arrive_to_execute.
        + by apply/andP; split.
    Qed.

End PIIdealProcessorModelLemmas.
