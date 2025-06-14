Require Export prosa.analysis.facts.model.overheads.schedule_change.

(** * Overhead Resource Model

    In this section, we define a scheduling model with overheads
    inspired by real-world uniprocessor OS implementations. We
    characterize different types of overheads, their cumulative
    duration, and the constraints governing their behavior. *)
Section OverheadResourceModel.

  (** Consider any type of jobs with arrival times and costs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider an arrival sequence and a corresponding schedule. *)
  Variable arr_seq : arrival_sequence Job.
  Variable sched : schedule (processor_state Job).

  (** We define functions that quantify the cumulative time that a
      given job (including the idle thread represented as [None])
      spends in dispatch, context switching, and CRPD overheads. *)

  Definition time_spent_in_dispatch (oj : option Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) (scheduled_job sched t == oj) && is_dispatch sched t.

  Definition time_spent_in_context_switch (oj : option Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) (scheduled_job sched t == oj) && is_context_switch sched t.

  Definition time_spent_in_CRPD (oj : option Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) (scheduled_job sched t == oj) && is_CRPD sched t.

  (** Next, we define boundedness predicates on the duration of
      overheads. We assume that, if the processor continuously
      schedules the same job (or remains idle) over a time interval,
      then the total time spent in each type of overhead is bounded by
      a fixed constant. These assumptions are used to control the
      contribution of each overhead type when no other scheduling
      activity occurs. *)

  Definition time_spent_in_dispatch_is_bounded_by DB :=
    forall (t1 t2 : instant) (oj : option Job),
      scheduled_job_invariant sched oj t1 t2 ->
      time_spent_in_dispatch oj t1 t2 <= DB.

  Definition time_spent_in_context_switch_is_bounded_by CSB :=
    forall (t1 t2 : instant) (oj : option Job),
      scheduled_job_invariant sched oj t1 t2 ->
      time_spent_in_context_switch oj t1 t2 <= CSB.

  Definition time_spent_in_CRPD_is_bounded_by CRPDB :=
    forall (t1 t2 : instant) (oj : option Job),
      scheduled_job_invariant sched oj t1 t2 ->
      time_spent_in_CRPD oj t1 t2 <= CRPDB.


  (** Next, we define ordering assumptions among types of overheads. *)

  (** Dispatch overhead must occur before any context switch. *)
  Definition dispatch_precedes_context_switch :=
    forall (oj : option Job) (t1 t2 : instant),
      scheduled_job_invariant sched oj t1 t2 ->
      forall t,
        t1 <= t < t2 ->
        is_dispatch sched t ->
        forall t',
          t1 <= t' <= t ->
          ~~ is_context_switch sched t'.

  (** Context-switch overhead must occur before any execution progress. *)
  Definition context_switch_precedes_progress :=
    forall (oj : option Job) (t1 t2 : instant),
      scheduled_job_invariant sched oj t1 t2 ->
      forall t,
        t1 <= t < t2 ->
        is_context_switch sched t ->
        forall t',
          t1 <= t' <= t ->
          ~~ is_progress sched t'.

  (** Context-switch overhead must occur before any CRPD overhead. *)
  Definition context_switch_precedes_CRPD :=
    forall (oj : option Job) (t1 t2 : instant),
      scheduled_job_invariant sched oj t1 t2 ->
      forall t,
        t1 <= t < t2 ->
        is_context_switch sched t ->
        forall t',
          t1 <= t' <= t ->
          ~~ is_CRPD sched t'.

  (** The overhead resource model bundles all of the above assumptions
      into a single definition. It requires upper bounds on each form
      of overhead and the temporal ordering among overhead phases. *)
  Definition overhead_resource_model (DB CSB CRPDB : duration)  :=
    time_spent_in_dispatch_is_bounded_by DB
    /\ time_spent_in_context_switch_is_bounded_by CSB
    /\ time_spent_in_CRPD_is_bounded_by CRPDB
    /\ dispatch_precedes_context_switch
    /\ context_switch_precedes_progress
    /\ context_switch_precedes_CRPD.

End OverheadResourceModel.
