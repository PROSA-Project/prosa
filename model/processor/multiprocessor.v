From mathcomp Require Export fintype.
Require Export prosa.behavior.all.
Require Import prosa.analysis.facts.behavior.service.

(** * Multiprocessor State *)

(** In the following, we define a model of identical multiprocessors, i.e., of
    processors with multiple cores of identical capabilities. The
    multiprocessor model is generic in the type of processor state of the
    cores. That is, it is possible to combine any uniprocessor state (such as
    the ideal state) with the following generic multiprocessor
    construction. (In fact, by combining the below multiprocessor model with
    variable speed processors, it is even possible to obtain a so-called
    uniform multiprocessor model.)

    NB: For now, the definition serves only to document how this can be done;
        it is not actually used anywhere in the library.  *)

Section Schedule.

  (** Consider any types of jobs... *)
  Variable Job: JobType.

  (** ... and consider any type of per-processor state. *)
  Variable processor_state: Type.
  Context `{ProcessorState Job processor_state}.

  (** Given a desired number of processors [num_cpus], we define a finite type
      of integers from [0] to [num_cpus - 1]. The purpose of this definition is
      to obtain a finite type (i.e., set of values) that can be enumerated in a
      terminating computation.

      Syntax hint: the ['I_] before [num_cpus] is ssreflect syntax for the
      finite set of integers from zero to [num_cpus - 1]. *)
  Definition processor (num_cpus: nat) := 'I_num_cpus.

  (** Next, for any given number of processors [num_cpus]... *)
  Variable num_cpus : nat.

  (** ...we represent the type of the "multiprocessor state" as a function that
      maps processor IDs (as defined by [processor num_cpus], see above) to the
      given state on each core. *)
  Definition multiprocessor_state := processor num_cpus -> processor_state.

  (** Based on this notion of multiprocessor state, we say that a given job [j]
      is currently scheduled on a specific processor [cpu], according to the
      given multiprocessor state [mps], iff [j] is scheduled in the
      processor-local state [(mps cpu)]. *)
  Definition multiproc_scheduled_on
      (j : Job) (mps : multiprocessor_state) (cpu : processor num_cpus)
    := scheduled_in j (mps cpu).

  (** Similarly, the service received by a given job [j] in a given
      multiprocessor state [mps] on a given processor of ID [cpu] is exactly
      the service given by [j] in the processor-local state [(mps cpu)]. *)
  Definition multiproc_service_on
      (j : Job) (mps : multiprocessor_state) (cpu : processor num_cpus)
    := service_in j (mps cpu).

  (** Finally, we connect the above definitions with the generic Prosa
      interface for processor models. *)
  Global Program Instance multiproc_state : ProcessorState Job multiprocessor_state :=
    {
      scheduled_on := multiproc_scheduled_on;
      service_on := multiproc_service_on
    }.
  Next Obligation.
    move: j s r H0.
    move=> j mps cpu.
    by apply: service_in_implies_scheduled_in.
  Defined.

  (** From the instance [multiproc_state], we get the function [service_in].
      The service received by a given job [j] in a given multiprocessor state
      [mps] is given by the sum of the service received across all individual
      processors of the multiprocessor. *)
  Lemma multiproc_service_in_eq : forall (j : Job) (mps : multiprocessor_state),
    service_in j mps = \sum_(cpu < num_cpus) service_in j (mps cpu).
  Proof.
    reflexivity.
  Qed.

End Schedule.
