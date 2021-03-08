From mathcomp Require Export ssreflect seq ssrnat ssrbool eqtype.
Require Import prosa.behavior.service.

(** This module contains basic definitions and properties of job
    completion sequences. *)

(** * Notion of a Completion Sequence *)

(** We begin by defining a job completion sequence. *)
Section CompletionSequence.

  (** Consider any kind of jobs with a cost
     and any kind of processor state. *)
  Context {Job : JobType} `{JobCost Job} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** For each instant [t], the completion sequence returns all
     arrived jobs that have completed at [t]. *)
  Definition completion_sequence : arrival_sequence Job :=
    fun t => [seq j <- arrivals_up_to arr_seq t | completes_at sched j t].

End CompletionSequence.
