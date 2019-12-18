Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.schedule.uni.susp.schedule.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

(* In this file, we propose a reduction that converts a suspension-aware
   schedule to another suspension-aware schedule where the cost of a certain
   job is inflated and its response time does not decrease. *)
Module SustainabilitySingleCost.

  Import ScheduleWithSuspensions Suspension Priority ScheduleConstruction.

  Section Reduction.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (** Basic Setup & Setting*)
    
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and assume any (schedule-independent) JLDP policy. *)
    Variable higher_eq_priority: JLDP_policy Job.
    
    (* Next, consider any suspension-aware schedule of the arrival sequence... *)
    Variable sched_susp: schedule Job.

    (* ...and the associated job suspension times. *)
    Variable job_suspension_duration: job_suspension Job.
    
    (** Definition of the Reduction *)
    
    (* Now we proceed with the reduction. Let j be the job to be analyzed. *)
    Variable j: Job.

    (* Next, consider any job cost inflation that does not decrease the cost of job j
       and that preserves the cost of the remaining jobs. *)
    Variable inflated_job_cost: Job -> time.
    
    (** Schedule Construction *)
    
    (* We are going to construct a new schedule that copies the original suspension-aware
       schedule and tries to preserve the service received by job j, until the time when
       it completes in the original schedule. *)
    Section ScheduleConstruction.

      (* First, we define the schedule construction function. *)
      Section ConstructionStep.
        
        (* For any time t, suppose that we have generated the schedule prefix in the
           interval [0, t). Then, we must define what should be scheduled at time t. *)
        Variable sched_prefix: schedule Job.
        Variable t: time.

        (* For simplicity, let's define some local names. *)
        Let job_is_pending := pending job_arrival inflated_job_cost sched_prefix.
        Let job_is_suspended :=
          suspended_at job_arrival inflated_job_cost job_suspension_duration sched_prefix.
        Let actual_job_arrivals_up_to := jobs_arrived_up_to arr_seq.

        (* Recall that a job is ready in the new schedule iff it is pending and not suspended. *)
        Let job_is_ready j t := job_is_pending j t && ~~ job_is_suspended j t.
        
        (* Then, consider the list of ready jobs at time t in the new schedule. *)
        Definition ready_jobs :=
          [seq j_other <- actual_job_arrivals_up_to t | job_is_ready j_other t].

        (* From the list of ready jobs, we take one of the (possibly many)
           highest-priority jobs, or None, in case there are no ready jobs. *)
        Definition highest_priority_job := seq_min (higher_eq_priority t) ready_jobs.

        (* Then, we construct the new schedule at time t as follows.
           a) If the currently scheduled job in sched_susp is ready to execute in the new schedule
              and has highest priority, pick that job.
           b) Else, pick one of the highest priority ready jobs in the new schedule. *)
        Definition build_schedule : option Job :=
          if highest_priority_job is Some j_hp then
            if sched_susp t is Some j_in_susp then
              if job_is_ready j_in_susp t && higher_eq_priority t j_in_susp j_hp then
                Some j_in_susp
              else
                Some j_hp
            else Some j_hp     
          else None.
        
      End ConstructionStep.

      (* To conclude, starting from the empty schedule, ...*)
      Let empty_schedule : schedule Job := fun t => None.

      (* ...we use the recursive definition above to construct the new schedule. *)
      Definition sched_susp_highercost :=
        build_schedule_from_prefixes build_schedule empty_schedule.

    End ScheduleConstruction.    

  End Reduction.
  
End SustainabilitySingleCost.