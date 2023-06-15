Require Export prosa.behavior.schedule.

(** * Supply *)
(** In this section, we define some useful notions about supply. *)
Section Supply.

  (** Consider any kind of jobs and any kind of processor state. *)
  Context {Job : JobType} {PState : ProcessorState Job}.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** We define a function that retrieves the amount of supply available
      at a particular instant in time. *)
  Definition supply_at (t : instant) := supply_in (sched t).

  (** Based on the notion of instantaneous supply, we define the
      cumulative supply produced during an interval from [t1] until
      (but not including) [t2]. *)
  Definition supply_during (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) supply_at t.

  (** Next, we define a predicate that checks if there is any supply at
      a given time instant. *)
  Definition has_supply (t : instant) := supply_at t > 0.

  (** We say that there is a blackout at a time instant [t] if there
      is no supply at [t]. *)
  Definition is_blackout (t : instant) := ~~ has_supply t.

  (** Similarly to [supply_during], we define the cumulative duration
      of blackout time instants during a time interval <<[t1,t2)>>. *)
  Definition blackout_during (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) is_blackout t.

End Supply.
