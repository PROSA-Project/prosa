From rt.restructuring.behavior.schedule Require Import ideal.
(* Note: we do not re-export the basic definitions to avoid littering the global
   namespace with type class instances. *)

(* In this section we show that an ideal schedule is unique at any point. *)
Section OnlyOneJobScheduled.
  (* Consider any job type and the ideal processor
     model. *)
  Context {Job: JobType}.

  (* Consider an ideal schedule... *)
  Variable sched: schedule (processor_state Job).

  (* ...and two given jobs that are to be scheduled. *)
  Variable j1 j2: Job.

  (* At any time t, if both j1 and j2 are scheduled, then they must be the same
     job. *)
  Lemma only_one_job_scheduled:
    forall t,
      scheduled_at sched j1 t ->
      scheduled_at sched j2 t ->
      j1 = j2.
  Proof.
    by rewrite /scheduled_at=>t/eqP->/eqP[->].
  Qed.

End OnlyOneJobScheduled.
