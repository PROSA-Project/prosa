Require Import prosa.model.readiness.basic.
Require Export prosa.model.task.sequentiality.
Require Export prosa.model.schedule.nonpreemptive.
Require Export prosa.model.priority.fifo.
Require Export prosa.analysis.facts.priority.sequential.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.preemption.job.nonpreemptive.

(** In this section, we prove some fundamental properties of the FIFO policy. *)
Section BasicLemmas.

  (** We assume the basic (i.e., Liu & Layland)
      readiness model under which any pending job is ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any type of jobs with arrival times and execution costs. *)
  Context `{Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job}.

  (** Consider any arrival sequence of such jobs ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and the resulting ideal uniprocessor schedule. We assume that the
      schedule is valid and work-conserving. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_schedule_is_valid : valid_schedule sched arr_seq.
  Hypothesis H_work_conservation : work_conserving arr_seq sched.

  (** Suppose jobs have preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ...and that the preemption model is valid. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Assume that the schedule respects the FIFO scheduling policy whenever jobs
      are preemptable. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).

  (** We observe that there is no priority inversion in a
      FIFO-compliant schedule. *)
  Lemma FIFO_implies_no_priority_inversion :
    forall j t,
      arrives_in arr_seq j ->
      pending sched j t ->
      ~~ is_priority_inversion sched j t.
  Proof.
    move => j t ARRIVES PENDINGj.
    rewrite /is_priority_inversion.
    move: (ideal_proc_model_sched_case_analysis sched t) => [/eqP -> //|[s INTER]].
    have -> : sched t = Some s; first by apply /eqP; rewrite -scheduled_at_def.
    apply /negP; apply /negPn.
    rewrite Bool.negb_involutive.
    destruct (s == j) eqn:EQ; first by move: EQ => /eqP ->; rewrite /hep_job /fifo.FIFO.
    destruct (hep_job s j) eqn:HEP; first by done.
    move : HEP => /negP/negP HEP.
    rewrite -ltnNge in HEP.
    contradict PENDINGj.
    apply /negP; rewrite negb_and.
    apply /orP; right; apply /negPn.
    have -> : scheduled_at sched s t -> completed_by sched j t => //.
    eapply (early_hep_job_is_scheduled); try rt_eauto.
    - by move=> ?; apply /andP; split; [apply ltnW | rewrite -ltnNge //=].
  Qed.

  (** We prove that in a FIFO-compliant schedule, if a job [j] is
      scheduled, then all jobs with higher priority than [j] have been
      completed. *)
  Lemma scheduled_implies_higher_priority_completed :
    forall j t,
      scheduled_at sched j t ->
      forall j_hp,
        arrives_in arr_seq j_hp ->
        ~~hep_job j j_hp ->
        completed_by sched j_hp t.
  Proof.
    move => j' t SCHED j_hp ARRjhp HEP.
    have EARLIER: job_arrival j_hp < job_arrival j' by rewrite -ltnNge in HEP.
    eapply (early_hep_job_is_scheduled arr_seq _ sched _ _ _ _ j_hp j' _ _ _ t).
    Unshelve. all : rt_eauto.
    move=> t'; apply /andP; split => //.
    by apply ltnW.
  Qed.

  (** The next lemma considers FIFO schedules in the context of tasks. *)
  Section SequentialTasks.

    (** If the scheduled jobs stem from a set of tasks, ... *)
    Context {Task : TaskType}.
    Context `{JobTask Job Task}.

    (** ... then the tasks in a FIFO-compliant schedule necessarily
        execute sequentially.  *)
    Lemma tasks_execute_sequentially : sequential_tasks arr_seq sched.
    Proof.
      move => j1 j2 t ARRj1 ARRj2 SAME_TASKx LT => //.
      eapply (early_hep_job_is_scheduled); try rt_eauto.
      by move=> ?; apply /andP; split; [apply ltnW | rewrite -ltnNge //=].
    Qed.

  End SequentialTasks.

  (** Finally, let us further assume that there are no needless
      preemptions among jobs of equal priority. *)
  Hypothesis H_no_superfluous_preemptions : no_superfluous_preemptions sched.

  (** In the absence of superfluous preemptions and under assumption
      of the basic readiness model, there are no preemptions at all in
      a FIFO-compliant schedule. *)
  Lemma no_preemptions_under_FIFO :
    forall j t,
      ~~ preempted_at sched j t.
  Proof.
    move => j t.
    apply /negP.
    intros CONTR.
    move: CONTR => /andP [/andP [SCHED1 NCOMPL] SCHED2].
    move : H_schedule_is_valid => [COME MUST].
    move: (ideal_proc_model_sched_case_analysis sched t) => [IDLE |[s INTER]].
    { specialize (H_work_conservation j t).
      destruct H_work_conservation as [j_other SCHEDj_other]; first by eapply (COME j t.-1 SCHED1).
      - do 2 (apply /andP; split; last by done).
        eapply scheduled_implies_pending in SCHED1; try rt_eauto.
        move : SCHED1 => /andP [HAS COMPL].
        by apply leq_trans with t.-1; [exact HAS| lia].
      - move: SCHEDj_other IDLE.
        rewrite scheduled_at_def => /eqP SCHED /eqP IDLE.
        by rewrite IDLE in SCHED. }
    { specialize (H_no_superfluous_preemptions t j s).
      have HEP : ~~ hep_job j s.
      {
        apply H_no_superfluous_preemptions; last by done.
        by repeat (apply /andP ; split; try by done).
      }
      rewrite /hep_job /fifo.FIFO -ltnNge in HEP. 
      eapply (early_hep_job_is_scheduled arr_seq ) in SCHED1; try rt_eauto.
      - apply scheduled_implies_not_completed in INTER; rt_eauto.
        by eapply (incompletion_monotonic sched s t.-1 t) in INTER; [move: INTER => /negP|lia].
      - by move=> ?; apply /andP; split; [apply ltnW | rewrite -ltnNge //=]. }
  Qed.

  (** It immediately follows that FIFO schedules are
      non-preemptive. *)
  Corollary FIFO_is_nonpreemptive : nonpreemptive_schedule sched.
  Proof.
    by rewrite -no_preemptions_equiv_nonpreemptive; apply no_preemptions_under_FIFO.
  Qed.

End BasicLemmas.
