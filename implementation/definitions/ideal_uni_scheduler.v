Require Export prosa.implementation.definitions.generic_scheduler.

Require Export prosa.model.processor.ideal.
Require Export prosa.model.preemption.parameter.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.facts.readiness.backlogged.
Require Export prosa.analysis.transform.swap.

(** * Ideal Uniprocessor Reference Scheduler *)

(** In this file, we provide a generic priority-aware scheduler that produces
    an ideal uniprocessor schedule for a given arrival sequence. The scheduler
    respects nonpreemptive sections and arbitrary readiness models. *)

Section UniprocessorScheduler.

  (** Consider any type of jobs with costs and arrival times, ... *)
  Context {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job}.

  (** .. in the context of an ideal uniprocessor model. *)
  Let PState := ideal.processor_state Job.
  Let idle_state : PState := None.

  (** Suppose we are given a consistent arrival sequence of such jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

  (** ... and a non-clairvoyant readiness model. *)
  Context {RM : JobReady Job (ideal.processor_state Job)}.
  Hypothesis H_nonclairvoyant_job_readiness : nonclairvoyant_readiness RM.

  (** ** Preemption-Aware Scheduler *)

  (** First, we define the notion of a generic uniprocessor scheduler that is
      cognizant of non-preemptive sections, so consider any preemption model. *)
  Context `{JobPreemptable Job}.

  Section NonPreemptiveSectionAware.

    (** Suppose we are given a scheduling policy that applies when jobs are
        preemptive: given a set of jobs ready at time [t], select which to run
        (if any) at time [t]. *)
    Variable choose_job : instant -> seq Job -> option Job.

    (** The next job is then chosen either by [policy] (if the current job is
       preemptive or the processor is idle) or a non-preemptively executing job
       continues to execute. *)
    Section JobAllocation.

      (** Consider a finite schedule prefix ... *)
      Variable sched_prefix : schedule (ideal.processor_state Job).

      (** ... that is valid up to time [t - 1]. *)
      Variable t : instant.

      (** We define a predicate that tests whether the job scheduled at the
          previous instant (if [t > 0]) is nonpreemptive (and hence needs to be
          continued to be scheduled). *)
      Definition prev_job_nonpreemptive : bool :=
        match t with
        | 0 => false
        | S t' => if sched_prefix t' is Some j
                 then job_ready sched_prefix j t
                      && ~~job_preemptable j (service sched_prefix j t)
                 else false
        end.

      (** Based on the [prev_job_nonpreemptive] predicate, either the previous
          job continues to be scheduled or the given policy chooses what to run
          instead. *)
      Definition allocation_at : option Job :=
        if prev_job_nonpreemptive then
          sched_prefix t.-1
        else
          choose_job t (jobs_backlogged_at arr_seq sched_prefix t).
    End JobAllocation.

    (** A preemption-model-compliant ideal uniprocessor schedule is then produced
        when using [allocation_at] as the policy for the generic scheduler. *)
    Definition pmc_uni_schedule : schedule PState := generic_schedule allocation_at idle_state.

  End NonPreemptiveSectionAware.

  (** ** Priority-Aware Scheduler *)

  (** Building on the preemption-model aware scheduler, we next define a simple priority-aware scheduler. *)
  Section PriorityAware.

    (** Given any JLDP priority policy... *)
    Context `{JLDP_policy Job}.

    (** ...always choose the highest-priority job when making a scheduling decision... *)
    Definition choose_highest_prio_job t jobs := supremum (hep_job_at t) jobs.

    (** ... to obtain a priority- and preemption-model-aware ideal uniprocessor
        schedule. *)
    Definition uni_schedule : schedule PState := pmc_uni_schedule choose_highest_prio_job.
  End PriorityAware.

End UniprocessorScheduler.
