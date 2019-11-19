From rt.util Require Import all.
From rt.restructuring.behavior Require Import all.
From rt.restructuring.analysis.basic_facts Require Import ideal_schedule.
From rt.restructuring.model Require Import job task.
From rt.restructuring.model Require Import processor.ideal.
From rt.restructuring.model.preemption Require Import job.parameters task.parameters valid_model.
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
  
  (** In this section we prove a few basic properties of the preemption_time predicate. *)
  Section Lemmas.

    (** Consider a valid model with bounded nonpreemptive segments. *)
    Hypothesis H_model_with_bounded_nonpreemptive_segments: 
      valid_model_with_bounded_nonpreemptive_segments arr_seq sched. 

    (** Then, we show that time 0 is a preemption time. *)
    Lemma zero_is_pt: preemption_time 0.
    Proof.
      unfold preemption_time.
      case SCHED: (sched 0) => [j | ]; last by done.
      move: (SCHED) => /eqP; rewrite -scheduled_at_def; move => ARR. 
      apply H_jobs_come_from_arrival_sequence in ARR.
      rewrite /service /service_during big_geq; last by done.
      destruct H_model_with_bounded_nonpreemptive_segments as [T1 T2].
        by move: (T1 j ARR) => [PP _]. 
    Qed.

    (** Also, we show that the first instant of execution is a preemption time. *)
    Lemma first_moment_is_pt:
      forall j prt,
        arrives_in arr_seq j ->
        ~~ scheduled_at sched j prt ->
        scheduled_at sched j prt.+1 ->
        preemption_time prt.+1.
    Proof. 
      intros s pt ARR NSCHED SCHED.
      unfold preemption_time.
      move: (SCHED); rewrite scheduled_at_def; move => /eqP SCHED2; rewrite SCHED2; clear SCHED2.
      destruct H_model_with_bounded_nonpreemptive_segments as [T1 T2].
        by move: (T1 s ARR) => [_ [_ [_ P]]]; apply P.
    Qed.

  End Lemmas.
    
End PreemptionTime.
