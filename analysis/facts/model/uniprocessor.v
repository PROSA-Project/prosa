Require Export prosa.model.processor.platform_properties.
Require Export prosa.util.tactics.

(** This file serves to collect basic facts about uniprocessors. *)

Section UniquenessOfTheScheduledJob.
  (**  Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any _uniprocessor_ model, ... *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uni : uniprocessor_model PState.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** By definition, if one job is scheduled on a uniprocessor, then no other
      job is scheduled at the same time. *)
  Lemma scheduled_job_at_neq :
      forall j j' t,
        j != j' ->
        scheduled_at sched j t ->
        ~~ scheduled_at sched j' t.
  Proof.
    move=> j j' t /eqP NEQ SCHED; apply/negP => SCHED'.
    by have: j = j' by apply: H_uni.
  Qed.

End UniquenessOfTheScheduledJob.

