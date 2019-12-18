Require Export prosa.model.preemption.parameter. 

(** * Preemption Model Compliance *)

(** A preemption model restricts when jobs can be preempted. In this
    module, we specify the corresponding semantics, i.e., how a valid
    schedule must be restricted to be compliant with a given
    preemption model. *)
Section ScheduleWithLimitedPreemptions.

  (**  Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any processor model, ... *)
  Context {PState : Type} `{ProcessorState Job PState}.
  
  (** ... and any preemption model. *)
  Context `{JobPreemptable Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  
  (** ... and a schedule of the jobs in the arrival sequence. *)
  Variable sched : schedule PState.
  
  (** We say that a schedule respects the preemption model given by
      [job_preemptable] if non-preemptable jobs remain scheduled. *)
  Definition schedule_respects_preemption_model :=
    forall j t,
      arrives_in arr_seq j ->
      ~~ job_preemptable j (service sched j t) ->
      scheduled_at sched j t.
  
End ScheduleWithLimitedPreemptions.
