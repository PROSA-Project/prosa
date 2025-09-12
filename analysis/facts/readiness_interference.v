Require Export prosa.analysis.definitions.readiness_interference.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.facts.interference.
Require Export prosa.analysis.definitions.service_inversion.readiness_aware.

(** In this file, we establish facts about readiness interference. *)

Section ReadinessInterference.
  (** Consider any kind of jobs with arrival times and execution costs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any processor state model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any notion of job readiness. *)
  Context `{!JobReady Job PState}.

  (** Consider any valid arrival sequence of jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any valid schedule of the given arrival sequence. *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Allow for any JLFP priority policy. *)
  Context {JLFP : JLFP_policy Job}.

  (** First, note that readiness interference is exclusive of the interference
      due to other higher-or-equal-priority jobs. *)
  Lemma no_hep_ready_implies_no_another_hep_interference :
    forall j t,
      ~~ some_hep_job_ready arr_seq sched j t ->
      ~~ another_hep_job_interference arr_seq sched j t.
  Proof.
    move=> j t /hasPn NO_HEP_READY.
    apply/negP => /hasP[jo INjo /andP[HEP NEQ]].
    move: INjo; rewrite mem_filter => /andP[SERVjo INjo].
    have SCHEDjo : scheduled_at sched jo t by apply service_at_implies_scheduled_at.
    have PENDjo : pending sched jo t by apply scheduled_implies_pending.
    have READYjo : job_ready sched jo t by done.
    have IN : jo \in [seq j' <- arrivals_up_to arr_seq t | hep_job j' j].
    { rewrite mem_filter.
      by do 2! [apply /andP; split; eauto]. }
    by move: (NO_HEP_READY jo IN); rewrite READYjo.
  Qed.

  (** Next, we observe that readiness interference is exclusive of service
      inversion. *)
  Lemma no_hep_ready_implies_no_service_inversion :
    forall j t,
      ~~ some_hep_job_ready arr_seq sched j t ->
      ~~ service_inversion arr_seq sched j t.
  Proof.
    move=> j t NO_HEP_READY.
    by rewrite /service_inversion; apply/nandP; left.
  Qed.

End ReadinessInterference.
