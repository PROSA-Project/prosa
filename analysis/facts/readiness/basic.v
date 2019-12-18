Require Import prosa.analysis.facts.behavior.completion.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.readiness.basic.

Section LiuAndLaylandReadiness.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Suppose jobs have an arrival time and a cost. *)
  Context `{JobArrival Job} `{JobCost Job}.

  (** In the basic Liu & Layland model, a schedule satisfies that only ready 
      jobs execute as long as jobs must arrive to execute and completed jobs
      don't execute, which we note with the following theorem. *)
  Lemma basic_readiness_compliance:
    forall sched,
      jobs_must_arrive_to_execute sched ->
      completed_jobs_dont_execute sched ->
      jobs_must_be_ready_to_execute sched.
  Proof.
    move=> sched ARR COMP.
    rewrite /jobs_must_be_ready_to_execute =>  j t SCHED.
    rewrite /job_ready /basic_ready_instance /pending.
    apply /andP; split.
    - by apply ARR.
    - rewrite -less_service_than_cost_is_incomplete.
      by apply COMP.
  Qed.

End LiuAndLaylandReadiness.
