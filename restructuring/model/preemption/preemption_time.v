Require Export rt.restructuring.model.processor.ideal.
Require Export rt.restructuring.model.preemption.valid_model.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Preemption Time in Ideal Uni-Processor Model *)
(** In this section we define the notion of preemption _time_ for
    ideal uni-processor model. *)
Section PreemptionTime.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume the existence of a function mapping a
      task to its maximal non-preemptive segment ... *)
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and the existence of a function mapping a job and
      its progress to a boolean value saying whether this job is
      preemptable at its current point of execution. *)
  Context `{JobPreemptable Job}.
  
  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any ideal uniprocessor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
  
  (** We say that a time instant t is a preemption time iff the job
      that is currently scheduled at t can be preempted (according to
      the predicate). *)
  Definition preemption_time (t : instant) :=
    if sched t is Some j then
      job_preemptable j (service sched j t)
    else true.
    
End PreemptionTime.
