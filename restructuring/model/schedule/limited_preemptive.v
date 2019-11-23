Require Export rt.restructuring.model.preemption.parameter. 
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require Import rt.restructuring.model.processor.ideal.

(** * Schedule with Limited Preemptions *)
(** In this section we introduce the notion of preemptions-aware
    schedule. *)
Section ScheduleWithLimitedPreemptions.

  (**  Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** Next, consider any ideal uniprocessor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).
  
  (** Based on the definition of the model with preemption points, 
      we define a valid schedule with limited preemptions. *)
  Definition valid_schedule_with_limited_preemptions :=
    forall j t,
      arrives_in arr_seq j ->
      ~~ job_preemptable j (service sched j t) ->
      scheduled_at sched j t.
  
End ScheduleWithLimitedPreemptions.
