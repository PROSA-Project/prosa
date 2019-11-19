Require Export rt.restructuring.behavior.all.
Require Import rt.restructuring.analysis.basic_facts.completion.

(** We define the readiness indicator function for the classic Liu & Layland
   model without jitter and no self-suspensions, where jobs are always
   ready. *)

Section LiuAndLaylandReadiness.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Supose jobs have an arrival time and a cost. *)
  Context `{JobArrival Job} `{JobCost Job}.

  (** In the basic Liu & Layland model, a job is ready iff it is pending. *)
  Global Program Instance basic_ready_instance : JobReady Job PState :=
    {
      job_ready sched j t := pending sched j t
    }.


  (** Under this definition, a schedule satisfies that only ready jobs execute
     as long as jobs must arrive to execute and completed jobs don't execute,
     which we note with the following theorem. *)
  Theorem basic_readiness_compliance:
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

