From mathcomp Require Import all_ssreflect.
Require Export prosa.behavior.all.

(** * The Ideal Uniprocessor Model *)


(** In this module, we define a central piece of the Prosa model: the notion of
    an ideal uniprocessor state. The word "ideal" here refers to the complete
    absence of runtime overheads or any other complications. In an ideal
    uniprocessor schedule, there are only two possible cases: at a given time,
    either a specific job is scheduled and makes unit-progress, or the
    processor is idle. To model this, we simply reuse the standard [option]
    type from the Coq standard library. *)

Section State.

  (** Consider any type of jobs. *)
  Variable Job: JobType.

  (** We connect the notion of an ideal processor state with
      the generic interface for the processor-state abstraction in Prosa by
      declaring a so-called instance of the [ProcessorState] typeclass. *)
  Global Program Instance processor_state : ProcessorState Job :=
    {
      (** We define the ideal "processor state" as an [option Job],
          which means that it is either [Some j] (where [j] is a
          [Job]) or [None] (which we use to indicate an idle
          instant). *)
      State := option Job;
      (** As this is a uniprocessor model, cores are implicitly defined
          as the [unit] type containing a single element as a placeholder. *)
      (** We say that a given job [j] is scheduled in a
          given state [s] iff [s] is [Some j]. *)
      scheduled_on j s (_ : unit) := s == Some j;
      (** Similarly, we say that a given job [j] receives service in a
          given state [s] iff [s] is [Some j]. *)
      service_on j s (_ : unit) := s == Some j;
    }.
  Next Obligation. by rewrite /nat_of_bool; case: ifP H => // ? /negP[]. Qed.

End State.

(** ** Idle Instants *)

(** In this section, we define the notion of idleness for ideal uniprocessor
    schedules. *)
Section IsIdle.

  (** Consider any type of jobs... *)
  Context {Job : JobType}.
  Variable arr_seq : arrival_sequence Job.

  (** ... and any ideal uniprocessor schedule of such jobs. *)
  Variable sched : schedule ((*ideal*)processor_state Job).

  (** We say that the processor is idle at time [t] iff there is no job being scheduled. *)
  Definition is_idle (t : instant) := sched t == None.

End IsIdle.
