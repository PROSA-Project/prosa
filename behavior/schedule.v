From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
Require Export prosa.behavior.arrival_sequence.

(** * Generic Processor State *)

(** Rather than choosing a specific schedule representation up front, we define
    the notion of a generic processor state, which allows us to state general
    definitions of core concepts (such as "how much service has a job
    received") that work across many possible scenarios (e.g., ideal
    uniprocessor schedules, schedules with overheads, variable-speed
    processors, multiprocessors, etc.).

    A concrete processor state type precisely determines how all relevant
    aspects of the execution environment are modeled (e.g., scheduled jobs,
    overheads, spinning). Here, we define just the common interface of all
    possible concrete processor states by means of a "type class", i.e., we
    define a few generic predicates and an invariant that must be defined by
    all concrete processor state types.

    In the most simple case (i.e., an ideal uniprocessor state), at any time,
    either a particular job is scheduled or the processor is idle. *)
Class ProcessorState (Job : JobType) (State : Type) :=
  {
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
    (** For a given processor state, the [scheduled_in] predicate checks
        whether a given job is running on any core in that state. *)
    scheduled_in (j : Job) (s : State) : bool :=
      [exists c : Core, scheduled_on j s c];
    (** For a given processor state, the [service_in] function determines how
       much service a given job receives in that state (across all cores). *)
    service_in : Job -> State -> work;
    (** For a given processor state, a job does not receive service if it is
        not scheduled in that state *)
    service_implies_scheduled :
      forall j s, ~~ scheduled_in j s -> service_in j s = 0
  }.

(** * Schedule Representation *)

(** In Prosa, schedules are represented as functions, which allows us to model
    potentially infinite schedules. More specifically, a schedule simply maps
    each instant to a processor state, which reflects state of the computing
    platform at the specific time (e.g., which job is presently scheduled). *)

Definition schedule (PState : Type) := instant -> PState.

(** The following line instructs Coq to not let proofs use knowledge of how
    [scheduled_on], [scheduled_in], and [service_in] are defined. Instead,
    proofs must rely on basic lemmas about processor state classes. *)
Global Opaque scheduled_on scheduled_in service_in.
