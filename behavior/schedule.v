Require Export prosa.behavior.arrival_sequence.

(** * Generic Processor State Interface *)

(** Rather than choosing a specific schedule representation up front, we define
    the notion of a generic processor state, which allows us to state general
    definitions of core concepts (such as "how much service has a job
    received") that work across many possible scenarios (e.g., ideal
    uniprocessor schedules, schedules with overheads, variable-speed
    processors, multiprocessors, etc.).

    A concrete processor state type precisely determines how all relevant
    aspects of the execution environment are modeled (e.g., scheduled jobs,
    overheads, spinning). Here, we define just the common interface of all
    possible concrete processor states by means of a type class, i.e., we
    define a few generic functions and an invariant that must be defined for
    all concrete processor state types.

    In the most simple case (i.e., an ideal uniprocessor state—see
    [model/processor/ideal.v]), at any given time, either a particular job is
    scheduled or the processor is idle. *)
Class ProcessorState (Job : JobType) :=
  {
    State : Type;
    (** A [ProcessorState] instance provides a finite set of cores on which
        jobs can be scheduled. In the case of uniprocessors, this is irrelevant
        and may be ignored (by convention, the unit type is used as a
        placeholder in uniprocessor schedules, but this is not
        important). (Hint to the Coq novice: [finType] just means some type
        with finitely many values, i.e., it is possible to enumerate all cores
        of a multi-processor.)  *)
    Core : finType;
    (** For a given processor state and core, the [scheduled_on] predicate
        checks whether a given job is running on the given core. *)
    scheduled_on : Job -> State -> Core -> bool;
    (** For a given processor state and core, the [supply_on] function
        determines how much supply the core produces in the given
        state). *)
    supply_on : State -> Core -> work;
    (** For a given processor state and core, the [service_on]
        function determines how much service a given job receives on
        the given core). *)
    service_on : Job -> State -> Core -> work;
    (** We require [service_on] and [supply_on] to be consistent in
        the sense that a job cannot receive more service on a given
        core in a given state than there is supply on the core in this
        state. *)
    service_on_le_supply_on :
      forall j s r, service_on j s r <= supply_on s r;
    (** In addition, a job can receive service (on a given core) only
        if it is also scheduled (on that core). *)
    service_on_implies_scheduled_on :
      forall j s r, ~~ scheduled_on j s r -> service_on j s r = 0
  }.
Coercion State : ProcessorState >-> Sortclass.

(** The above definition of the [ProcessorState] interface provides
    the predicate [scheduled_on] and the function [service_on], which
    relate a given job to a given core in a given state. This level of
    detail is required for generality, but in many situations it
    suffices and is more convenient to elide the information about
    individual cores, instead referring to all cores at once. To this
    end, we next define the short-hand functions [scheduled_in] and
    [service_in] to directly check whether a job is scheduled at all
    (i.e., on any core), and how much service the job receives
    anywhere (i.e., across all cores). *)
Section ProcessorIn.

  (** Consider any type of jobs... *)
  Context {Job : JobType}.

  (** ...and any type of processor state. *)
  Context {State : ProcessorState Job}.

  (** For a given processor state, the [scheduled_in] predicate checks
      whether a given job is running on any core in that state. *)
  Definition scheduled_in (j : Job) (s : State) : bool :=
    [exists c : Core, scheduled_on j s c].

  (** For a given processor state, the [supply_in] function determines
      how much supply the processor provides (across all cores) in the given state. *)
  Definition supply_in (s : State) : work :=
    \sum_(r : Core) supply_on s r.

  (** For a given processor state, the [service_in] function
      determines how much service a given job receives in that state
      (across all cores). *)
  Definition service_in (j : Job) (s : State) : work :=
    \sum_(r : Core) service_on j s r.

End ProcessorIn.

(** * Schedule Representation *)

(** In Prosa, schedules are represented as functions, which allows us to model
    potentially infinite schedules. More specifically, a schedule simply maps
    each instant to a processor state, which reflects state of the computing
    platform at the specific time (e.g., which job is presently scheduled). *)

Definition schedule {Job : JobType} (PState : ProcessorState Job) :=
  instant -> PState.

(** The following line instructs Coq to not let proofs use knowledge of how
    [scheduled_on] and [service_on] are defined. Instead,
    proofs must rely on basic lemmas about processor state classes. *)
Global Opaque scheduled_on service_on.

Obligation Tactic := try done.
