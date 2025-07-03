Require Export prosa.model.processor.overheads.
Require Export prosa.model.priority.classes.

(** In this section, we define the notion of a priority bump. *)
Section PriorityBump.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.

  (** Consider a JLFP-policy. *)
  Context {JLFP : JLFP_policy Job}.

  (** Consider any explicit-overhead uni-processor schedule. *)
  Variable sched : schedule (overheads.processor_state Job).

  (** Time [t] is a priority bump if the job scheduled at time [t] has
      strictly higher priority than the job scheduled at time [t−1].
      A priority bump also occurs if the processor was idle at time
      [t−1] and starts executing a job at time [t]. *)
  Definition priority_bump (t : instant) :=
    match scheduled_job sched t.-1, scheduled_job sched t with
    | None, None => false
    | None, Some _ => true
    | Some _, None => false
    | Some j1, Some j2 =>  ~~ hep_job j1 j2
    end.

End PriorityBump.
