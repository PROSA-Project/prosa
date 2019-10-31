From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
From rt.restructuring.behavior Require Export arrival_sequence.

(** We define the notion of a generic processor state. The processor state type
   determines aspects of the execution environment are modeled (e.g., overheads, spinning).
   In the most simple case (i.e., Ideal.processor_state), at any time,
   either a particular job is either scheduled or it is idle. *)
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

(** A schedule maps an instant to a processor state *)
Definition schedule (PState : Type) := instant -> PState.

(** The following line instructs Coq to not let proofs use knowledge of how
    [scheduled_on], [scheduled_in], and [service_in] are defined. Instead,
    proofs must rely on basic lemmas about processor state classes. *)
Global Opaque scheduled_on scheduled_in service_in.
