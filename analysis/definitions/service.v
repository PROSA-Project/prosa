Require Export prosa.behavior.service.

(** * Served At *)

(** In this section, we define a set of jobs that receive service at a
    given time. *)
Section ServedAt.

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** We define jobs served at a given time [t] as a set of jobs that
      receive service at [t]. *)
  Definition served_at (t : instant) :=
    [seq j <- arrivals_up_to arr_seq t | receives_service_at sched j t].

End ServedAt.
