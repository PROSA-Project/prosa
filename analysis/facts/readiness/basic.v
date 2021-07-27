Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.definitions.readiness.
Require Export prosa.analysis.definitions.work_bearing_readiness.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.readiness.basic.

Section LiuAndLaylandReadiness.
  
  (** Consider any kind of jobs ... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Suppose jobs have an arrival time and a cost. *)
  Context `{JobArrival Job} `{JobCost Job}.

  (** The Liu & Layland readiness model is trivially non-clairvoyant. *)
  Fact basic_readiness_nonclairvoyance :
    nonclairvoyant_readiness basic_ready_instance.
  Proof.
    move=> sched sched' j h PREFIX t IN.
    rewrite /job_ready /basic_ready_instance.
    now apply (identical_prefix_pending _ _ h).
  Qed.

  (** Consider any job arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of these jobs. *)
  Variable sched : schedule PState.

  (** In the basic Liu & Layland model, a schedule satisfies that only ready 
      jobs execute as long as jobs must arrive to execute and completed jobs
      don't execute, which we note with the following theorem. *)
  Lemma basic_readiness_compliance :
    jobs_must_arrive_to_execute sched ->
    completed_jobs_dont_execute sched ->
    jobs_must_be_ready_to_execute sched.
  Proof.
    move=> ARR COMP.
    rewrite /jobs_must_be_ready_to_execute =>  j t SCHED.
    rewrite /job_ready /basic_ready_instance /pending.
    apply /andP; split.
    - by apply ARR.
    - rewrite -less_service_than_cost_is_incomplete.
      by apply COMP.
  Qed.

  (** Consider a JLFP policy that indicates a reflexive
      higher-or-equal priority relation. *)
  Context `{JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.

  (** We show that the basic readiness model is a work-bearing
      readiness model. That is, at any time instant [t], if a job [j]
      is pending, then there exists a job (namely [j] itself) with
      higher-or-equal priority that is ready at time [t]. *)
  Fact basic_readiness_is_work_bearing_readiness :
    work_bearing_readiness arr_seq sched.
  Proof.
    intros ? ? ARR PEND.
    exists j; repeat split => //.
    by eapply (H_priority_is_reflexive 0).
  Qed.

End LiuAndLaylandReadiness.
