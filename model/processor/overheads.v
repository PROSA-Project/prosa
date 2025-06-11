Require Export prosa.behavior.all.

(** In the following, we define a processor state that models the
    possibility for a job to experience overheads. We consider three
    types of overheads: dispatch overheads, which occur when the
    scheduler selects the next job to run; context switch overheads,
    when the processor sets up the environment for the next job; and
    cache-related preemption delays, which arise due to cold caches
    after preemption. *)
Section State.

  (** Consider any type of jobs. *)
  Variable Job: JobType.

  (** The [proc_state] type represents the current activity of
      the processor, including various overheads and job
      execution. Some states carry an [option Job] to indicate whether
      the event is related to an actual job ([Some j]) or to an idle
      thread ([None]). The states include: [Idle], [ContextSwitch]
      between two jobs (possibly involving idle), [Dispatch] of a job
      (or idle), [CacheRelatedPreemptionDelay] due to cold cache after
      preemption, and [Progress], indicating normal job execution. *)
  Inductive proc_state :=
  | Idle
  | ContextSwitch (j1 : option Job) (j2 : option Job)
  | Dispatch (j : option Job)
  | CacheRelatedPreemptionDelay (j : Job)
  | Progress (j : Job).

  (** Next, we define the semantics of the processor state with overheads. *)
  Section Service.

    (** Let [j] denote any job. *)
    Variable j : Job.

    (** A job [j] is considered scheduled in a state [s] if [s]
        represents activity tied to [j], such as being dispatched, in
        a context switch involving [j], delayed due to preemption, or
        making progress. *)
    Definition overheads_scheduled_on (s : proc_state) (_ : unit) : bool :=
      match s with
      | Idle                           => false
      | ContextSwitch  _ None          => false
      | ContextSwitch  _ (Some j')     => j == j'
      | Dispatch None                  => false
      | Dispatch (Some j')             => j == j'
      | CacheRelatedPreemptionDelay j' => j == j'
      | Progress j'                    => j == j'
      end.

    (** The processor provides one unit of supply in states where it
        is available to do useful work (that is, either idle or
        actively running a job). Overhead states contribute no
        supply. *)
    Definition overheads_supply_on (s : proc_state) (_ : unit) : work :=
      match s with
      | Idle       => 1
      | Progress j => 1
      | _ => 0
      end.

    (** A job [j] receives service only when the processor is in the
          [Progress j] state, indicating actual execution. *)
    Definition overheads_service_on (s : proc_state) (_ : unit) : work :=
      match s with
      | Progress j' => if j' == j then 1 else 0
      | _ => 0
      end.

  End Service.

  (** Finally, we connect the above definitions with the generic Prosa
      interface for abstract processor states. *)
  Program Definition processor_state : ProcessorState Job :=
    {|
      State        := proc_state;
      scheduled_on := overheads_scheduled_on;
      supply_on    := overheads_supply_on;
      service_on   := overheads_service_on
    |}.
  Next Obligation. by move => j [] // s [] /=; case: eqP. Qed.
  Next Obligation. by move => j [] // s [] //=; rewrite [s == j]eq_sym; case (j == s). Qed.

End State.

(** In this section, we provide some useful definitions for schedule inspection. *)
Section ScheduleInspection.

  (** Consider any type of jobs... *)
  Context {Job : JobType}.

  (** ... and a schedule with overheads. *)
  Variable sched : schedule (overheads.processor_state Job).

  (** Function [scheduled_job] returns the job (if any) that is
      associated with the processor state at time [t]. This includes
      jobs being dispatched, involved in context switches, delayed due
      to preemption, or making progress. *)
  Definition scheduled_job (t : instant) : option Job :=
    match sched t with
    | Idle => None
    | Dispatch oj => oj
    | ContextSwitch _ oj => oj
    | CacheRelatedPreemptionDelay oj => Some oj
    | Progress oj => Some oj
    end.

  (** Indicates whether the processor is performing a context switch
      at time [t]. *)
  Definition is_context_switch (t : instant) :=
    match sched t with
    | ContextSwitch _ _ => true
    | _ => false
    end.

  (** Indicates whether the processor is dispatching a job at time [t]. *)
  Definition is_dispatch (t : instant) :=
    match sched t with
    | Dispatch _ => true
    | _ => false
    end.

  (** Indicates whether the processor is incurring cache-related
      preemption delay at time [t]. *)
  Definition is_CRPD (t : instant) :=
    match sched t with
    | CacheRelatedPreemptionDelay _ => true
    | _ => false
    end.

End ScheduleInspection.
