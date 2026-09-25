Require Export prosa.model.priority.classes.
Require Export prosa.analysis.facts.behavior.arrivals.

(** * Carry-In Work *)
(** In this module, we characterize work remaining from earlier releases. *)
Section NoCarryIn.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has an arrival time and a cost. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job} `{JobCost Job}.

  (** Consider any arrival sequence of such jobs with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and the resultant schedule. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** There is no carry-in at time [t] iff every job (regardless of priority)
      from the arrival sequence released before [t] has completed by that time. *)
  Definition no_carry_in (t : instant) :=
    forall j_o,
      arrives_in arr_seq j_o ->
      arrived_before j_o t ->
      completed_by sched j_o t.

  (** Conversely, there exists a carry-in job if any earlier-arrived job is
      still incomplete. *)
  Definition exists_carry_in (t : instant) :=
    has (fun j => ~~ completed_by sched j t) (arrivals_before arr_seq t).

  (** We connect the Boolean search to the propositional condition via reflection. *)
  Lemma exists_carry_inP :
    forall t, reflect (~ no_carry_in t) (exists_carry_in t).
  Proof.
    move=> t; apply: (iffP idP).
    - move/hasP=> [j H_in /negP H_unfinished] H_empty.
      apply: H_unfinished; apply: H_empty.
      + exact: in_arrivals_implies_arrived H_in.
      + exact: in_arrivals_implies_arrived_before H_in.
    - move=> H_carry; apply/negPn/negP => /hasPn H_complete.
      apply: H_carry => j H_arrival H_before.
      have H_in : j \in arrivals_before arr_seq t.
      { by apply: arrived_between_implies_in_arrivals. }
      by move: (H_complete j H_in); rewrite negbK.
  Qed.

End NoCarryIn.
