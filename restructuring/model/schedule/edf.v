From mathcomp Require Import ssrnat ssrbool fintype.
From rt.restructuring.behavior Require Export schedule.

(** In this file, we define what it means to be an "EDF schedule". *)
Section DefinitionOfEDF.

  (* For any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (* ... any given type of processor states: *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (* We say that a schedule is locally an EDF schedule at a point in
     time [t] if the job scheduled at time [t] has a deadline that is
     earlier than or equal to the deadline of any other job that could
     be scheduled at time t but is scheduled later.

     Note that this simple definition is (intentionally) oblivious to
     (i.e., not compatible with) issues such as non-preemptive regions
     or self-suspensions. *)
  Definition EDF_at (sched: schedule PState) (t: instant) :=
    forall (j: Job),
      scheduled_at sched j t ->
      forall (t': instant) (j': Job),
        t <= t' ->
        scheduled_at sched j' t' ->
        job_arrival j' <= t ->
        job_deadline j <= job_deadline j'.

  (* A schedule is an EDF schedule if it is locally EDF at every point in time. *)
  Definition is_EDF_schedule (sched: schedule PState) := forall t, EDF_at sched t.

End DefinitionOfEDF.







