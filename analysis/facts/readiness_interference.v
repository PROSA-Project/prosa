Require Export prosa.analysis.definitions.readiness_interference.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.facts.interference.
Require Export prosa.analysis.definitions.service_inversion.readiness_aware.

Section ReadinessInterference.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  Context `{PState : ProcessorState Job}.

  Context `{!JobReady Job PState}.

  Variable arr_seq : arrival_sequence Job.

  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  Context {JLFP : JLFP_policy Job}. 

  Section BasicLemmas.
 
    Lemma no_hep_ready_implies_no_another_hep_interference :
      forall j t,
        no_hep_ready arr_seq sched j t ->
        ~~ another_hep_job_interference arr_seq sched j t.
    Proof.
      move=> j t /allP NO_HEP_READY.
      apply/negP => /hasP[jo INjo /andP[HEP NEQ]].
      move: INjo; rewrite mem_filter => /andP[SERVjo INjo].
      have SCHEDjo : scheduled_at sched jo t by apply service_at_implies_scheduled_at.
      have PENDjo : pending sched jo t by apply scheduled_implies_pending.
      have READYjo : job_ready sched jo t by done.
      have IN : jo \in [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j].
      { rewrite mem_filter. 
        by do 2! [apply /andP; split; eauto]. }
      by move: (NO_HEP_READY jo IN); rewrite READYjo.
    Qed.

    Lemma no_hep_ready_implies_no_service_inversion :
      forall j t,
        no_hep_ready arr_seq sched j t ->
        ~~ service_inversion arr_seq sched j t.
    Proof.
      move=> j t /allP NO_HEP_READY.
      apply /negP => /andP[/hasP[jo INjo HEPjo] LP_SERV].
      move: INjo; rewrite mem_filter => /andP[READYjo INjo].
      have PENDjo : pending sched jo t by done.
      have IN : jo \in [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j].
      { rewrite mem_filter. 
        by do 2! [apply /andP; split; eauto]. }
      by move: (NO_HEP_READY jo IN); rewrite READYjo.
    Qed.

  End BasicLemmas.
End ReadinessInterference.
