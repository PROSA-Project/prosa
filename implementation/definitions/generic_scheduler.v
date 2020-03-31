Require Export prosa.analysis.transform.swap.

(** * Generic Reference Scheduler *)

(** In this file, we provide a generic procedure that produces a schedule by
    making a decision on what to schedule at each point in time. *)

(** To begin with, we define the notion of a pointwise scheduling policy that
    makes a decision at a given time [t] based on given prefix up to time
    [t.-1]. *)
Section PointwisePolicy.
  (** Consider any type of jobs and type of schedule. *)
  Context {Job : JobType}.
  Variable PState : Type.

  (** A pointwise scheduling policy is a function that, given a schedule prefix
      that is valid up to time [t - 1], decides what to schedule at time
      [t]. *)
  Definition PointwisePolicy := schedule PState -> instant -> PState.
End PointwisePolicy.

Section GenericSchedule.
  (** Consider any type of jobs and type of schedule. *)
  Context {Job : JobType} {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Suppose we are given a policy function that, given a schedule prefix that
      is valid up to time [t - 1], decides what to schedule at time [t]. *)
  Variable policy : PointwisePolicy PState.

  (** Let [idle_state] denote the processor state that indicates that the
      entire system is idle. *)
  Variable idle_state : PState.

  (** We construct the schedule step by step starting from an "empty" schedule
      that is idle at all times as a base case. *)
  Definition empty_schedule: schedule PState := fun _ => idle_state.

  (** Next, we define a function that computes a schedule prefix up to a given
      time horizon [h]. *)
  Fixpoint schedule_up_to (h : instant)  :=
    let
      prefix := if h is h'.+1 then schedule_up_to h' else empty_schedule
    in
      replace_at prefix h (policy prefix h).

  (** Finally, we define the generic schedule as follows: for a
      given point in time [t], we compute the finite prefix up to and including
      [t], namely [schedule_up_to t], and then return the job scheduled at time
      [t] in that prefix. *)
  Definition generic_schedule (t : instant) : PState :=
    schedule_up_to t t.

End GenericSchedule.

