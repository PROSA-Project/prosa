Require Export prosa.model.processor.overheads.

(** In this section, we define predicates and functions to reason
    about schedule changes over time intervals. *)
Section ScheduleChanges.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence and any schedule. *)
  Variable arr_seq : arrival_sequence Job.
  Variable sched : schedule (overheads.processor_state Job).

  (** A schedule change occurs at time [t] if the processor state
      (i.e., which job is scheduled or whether it is idle) at time [t]
      differs from that at time [t−1]. *)
  Definition schedule_change (t : instant) :=
    scheduled_job sched t.-1 != scheduled_job sched t.

  (** In addition, we define the number of schedule changes in the
      interval <<[t1, t2)>>. *)
  Definition number_schedule_changes (t1 t2 : instant) :=
    count schedule_change (index_iota t1 t2).

  (** The predicate [no_schedule_changes_during t1 t2] holds if the
      number of schedule changes in the interval <<(t1, t2)>> is
      zero. Note that we count changes only from time [t1+1] onward
      because a change between [t1−1] and [t1] does not reflect any
      change occurring *within* the interval. *)
  Definition no_schedule_changes_during (t1 t2 : instant) :=
    number_schedule_changes t1.+1 t2 == 0.

  (** The predicate [scheduled_job_invariant oj t1 t2] holds if the
      processor always schedules either a specific job or is being
      idle at every instant in <<[t1, t2)>>.

      Unlike [number_schedule_changes], [scheduled_job_invariant]
      fixes a specific job (or idle state). This is useful when 
      bounding overheads that can be attributed to a specific job. *)
  Definition scheduled_job_invariant (oj : option Job) (t1 t2 : instant) :=
    all (fun t => scheduled_job sched t == oj) (index_iota t1 t2).

End ScheduleChanges.
