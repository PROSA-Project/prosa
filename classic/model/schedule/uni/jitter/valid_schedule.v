Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.jitter.schedule
               prosa.classic.model.schedule.uni.jitter.platform.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we construct a predicate that defines a valid jitter-aware schedule
   of a given task set. *)
Module ValidJitterAwareSchedule.

  Import UniprocessorScheduleWithJitter Priority Platform.

  (** Basic Setup & Setting*)
  Section DefiningValidSchedule.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.

    (* Assume any given job-level policy. *)
    Variable higher_eq_priority: JLDP_policy Job.
    
    (** Definition of the Jitter-Aware Schedule *)

    (* Consider any job cost and job jitter functions. *)
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    
    (* Let sched be any schedule. *)
    Variable sched: schedule Job.

    (* For sched to denote a valid jitter-aware schedule of ts, the following properties must hold. *)

    (* 1) All scheduled jobs must come from the arrival sequence. *)
    Let H1_jobs_come_from_arrival_sequence := jobs_come_from_arrival_sequence sched arr_seq.

    (* 2) Jobs only execute after the jitter has passed. *)
    Let H2_jobs_execute_after_jitter := jobs_execute_after_jitter job_arrival job_jitter sched.

    (* 3) Jobs do not execute for longer than their costs. *)
    Let H3_completed_jobs_dont_execute := completed_jobs_dont_execute job_cost sched.

    (* 4) The schedule is work-conserving. *)
    Let H4_work_conserving := work_conserving job_arrival job_cost job_jitter arr_seq sched.

    (* 5) The schedule respects task priorities. *)
    Let H5_respects_priority :=
      respects_JLDP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority.

    (* All these properties can be combined into the following predicate. *)
    Definition valid_jitter_aware_schedule :=
      H1_jobs_come_from_arrival_sequence /\
      H2_jobs_execute_after_jitter /\
      H3_completed_jobs_dont_execute /\
      H4_work_conserving /\
      H5_respects_priority.
         
  End DefiningValidSchedule.
  
End ValidJitterAwareSchedule.