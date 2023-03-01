From mathcomp Require Import all_ssreflect.
Require Export prosa.behavior.all.

(** In the following, we define a processor state that includes the possibility
    of spinning, where spinning jobs do not progress (= don't get any service).

    NB: For now, the definition serves only to document how this can be done;
        it is not actually used anywhere in the library.  *)
Section State.

  (** Consider any type of jobs. *)
  Variable Job: JobType.

  (** We define the state of a processor at a given time to be one of three
      possible cases: either a specific job is scheduled and makes progress
      [Progress j], a specific job is scheduled but makes not useful progress
      [Spin j], or the processor is idle [Idle]. *)
  Inductive processor_state :=
    Idle
  | Spin (j : Job)
  | Progress (j : Job).

  (** Next, we define the semantics of the processor state with spinning. *)
  Section Service.

    (** Let [j] denote any job. *)
    Variable j : Job.

    (** It is scheduled in a given state [s] iff the state is not idle and [j]
        is the job mentioned in the state. *)
    Definition spin_scheduled_on (s : processor_state) (_ : unit) : bool :=
      match s with
      | Idle        => false
      | Spin j'     => j' == j
      | Progress j' => j' == j
      end.

    (** In contrast, job [j] receives service only if the given state [s] is
        [Progress j]. *)
    Definition spin_service_on (s : processor_state) (_ : unit) : work :=
      match s with
      | Idle        => 0
      | Spin j'     => 0
      | Progress j' => j' == j
      end.

  End Service.

  (** Finally, we connect the above definitions with the generic Prosa
      interface for abstract processor states. *)
  Program Definition pstate_instance : ProcessorState Job :=
    {|
      State := processor_state;
      scheduled_on := spin_scheduled_on;
      service_on   := spin_service_on
    |}.
  Next Obligation. by move=> j [] //= j' _ /negbTE ->. Qed.
End State.
