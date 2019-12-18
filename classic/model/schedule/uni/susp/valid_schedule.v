Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.platform.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we construct a predicate that defines a valid suspension-aware schedule. *)
Module ValidSuspensionAwareSchedule.

  Import ScheduleWithSuspensions Suspension Priority PlatformWithSuspensions.

  (** Basic Setup & Setting*)
  Section DefiningValidSchedule.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.

    (* Assume any given job-level policy... *)
    Variable higher_eq_priority: JLDP_policy Job.
    
    (* ...and job suspension times. *)
    Variable job_suspension_duration: job_suspension Job.

    (** Definition of the Suspension-Aware Schedule *)

    (* Let job_cost denote any job cost function... *)
    Variable job_cost: Job -> time.
    
    (* ...and let sched_susp be any schedule. *)
    Variable sched_susp: schedule Job.

    (* For sched_susp to denote a valid suspension-aware schedule,
       the following properties must be satisfied. *)

    (* 1) All scheduled jobs must come from the arrival sequence. *)
    Let H1_jobs_come_from_arrival_sequence := jobs_come_from_arrival_sequence sched_susp arr_seq.

    (* 2) Jobs only execute after they arrive. *)
    Let H2_jobs_must_arrive_to_execute := jobs_must_arrive_to_execute job_arrival sched_susp.

    (* 3) Jobs do not execute for longer than their costs. *)
    Let H3_completed_jobs_dont_execute := completed_jobs_dont_execute job_cost sched_susp.

    (* 4) The schedule is work-conserving if there are non-suspended jobs. *)
    Let H4_work_conserving :=
      work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp.

    (* 5) The schedule respects task priorities. *)
    Let H5_respects_priority :=
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq
                           sched_susp higher_eq_priority.

    (* 6) Suspended jobs are not allowed to be schedule. *)
    Let H6_respects_self_suspensions :=
      respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp.

    (* All these properties can be combined into the following predicate. *)
    Definition valid_suspension_aware_schedule :=
      H1_jobs_come_from_arrival_sequence /\
      H2_jobs_must_arrive_to_execute /\
      H3_completed_jobs_dont_execute /\
      H4_work_conserving /\
      H5_respects_priority /\
      H6_respects_self_suspensions.
         
  End DefiningValidSchedule.
  
End ValidSuspensionAwareSchedule.