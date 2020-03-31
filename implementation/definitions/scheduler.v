Require Export prosa.behavior.all.
Require Export prosa.model.priority.classes.
Require Export prosa.util.supremum.
Require Export prosa.model.preemption.parameter.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.model.processor.ideal.

Section UniprocessorSchedule.

  Context {Job : JobType}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobPreemptable Job}.
  Context `{JLDP_policy Job}.
  Context {Task : eqType}.
  Context `{JobReady Job (ideal.processor_state Job)}.

  Variable arr_seq : arrival_sequence Job.

  Section JobAllocation.

    Variable sched_prefix : schedule (ideal.processor_state Job).

    Definition jobs_backlogged_at (t : instant): seq Job :=
      [seq j <- arrivals_up_to arr_seq t | backlogged sched_prefix j t].

    Definition prev_job_nonpreemptive (t : instant) : bool:=
      match t with
      | 0 => false
      | S t' => if sched_prefix t' is Some j then
                  ~~job_preemptable j (service sched_prefix j t)
                else
                  false
      end.

    (** Given an arrival sequence, a prefix schedule [[0, t-1]], computes
        which job has to be scheduled at [t] **)
    Definition allocation_at (t : instant): option Job :=
      if prev_job_nonpreemptive t then
        sched_prefix t.-1
      else
        supremum (hep_job_at t) (jobs_backlogged_at t).

  End JobAllocation.

  Definition empty_schedule: schedule (ideal.processor_state Job) := fun _ => None.

  (** Given an arrival sequence, computes a schedule up to time [h] **)
  Fixpoint schedule_up_to (h : instant) : schedule (ideal.processor_state Job) :=
    let
      prefix := if h is S h' then schedule_up_to h' else empty_schedule
    in
    fun t =>
      if t == h then
        allocation_at prefix t
      else
        prefix t.

  Definition uni_schedule (t : instant) : ideal.processor_state Job :=
    schedule_up_to t t.

End UniprocessorSchedule.

