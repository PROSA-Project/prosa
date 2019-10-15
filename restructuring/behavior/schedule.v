From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.
From rt.restructuring.behavior Require Export arrival_sequence.

(* We define the notion of a generic processor state. The processor state type
   determines aspects of the execution environment are modeled (e.g., overheads, spinning).
   In the most simple case (i.e., Ideal.processor_state), at any time,
   either a particular job is either scheduled or it is idle. *)
Class ProcessorState (Job : JobType) (State : Type) :=
  {
    (* For a given processor state, the [scheduled_in] predicate checks whether a given
       job is running in that state. *)
    scheduled_in : Job -> State -> bool;
    (* For a given processor state, the [service_in] function determines how much
       service a given job receives in that state. *)
    service_in : Job -> State -> work;
    (* For a given processor state, a job does not receive service if it is not scheduled
       in that state *)
    service_implies_scheduled :
      forall j s, ~~ scheduled_in j s -> service_in j s = 0
  }.

(* A schedule maps an instant to a processor state *)
Definition schedule (PState : Type) := instant -> PState.
