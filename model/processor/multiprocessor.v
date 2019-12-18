From mathcomp Require Export fintype.
Require Export prosa.behavior.all.

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
      of integers from 0 to [num_cpus - 1]. The purpose of this definition is
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
      given multiprocessor state [mps], if [j] is scheduled in the
      processor-local state [(mps cpu)].  *)
  Let multiproc_scheduled_on (j : Job) (mps : multiprocessor_state) (cpu : processor num_cpus)
    := scheduled_in j (mps cpu).

  (** The service received by a given job [j] in a given multiprocessor state
      [mps] is given by the sum of the service received across all individual
      processors of the multiprocessor. *)
  Let multiproc_service_in (j : Job) (mps : multiprocessor_state)
    := \sum_(cpu < num_cpus) service_in j (mps cpu).

  (** Finally, we connect the above definitions with the generic Prosa
      interface for processor models. *)
  Global Program Instance multiproc_state : ProcessorState Job multiprocessor_state :=
    {
      scheduled_on := multiproc_scheduled_on;
      service_in := multiproc_service_in
    }.
  Next Obligation.
    move: j s H0.
    move=> j s /existsP Hsched.
    apply/eqP.
    rewrite sum_nat_eq0.
    apply/forallP=>/= c.
    rewrite service_implies_scheduled//.
    case: (boolP (scheduled_in _ _))=>//= Habs.
    exfalso; apply: Hsched.
      by exists c.
  Defined.
End Schedule.
