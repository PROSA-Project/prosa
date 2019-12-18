Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.platform
               prosa.classic.model.schedule.uni.susp.build_suspension_table.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq bigop fintype.

(* In this file, we prove that uniprocessor suspension-aware scheduling is
   sustainable with job costs under the dynamic suspension model. *)
Module SustainabilityAllCosts.

  Import ScheduleWithSuspensions Suspension Priority PlatformWithSuspensions
         ScheduleConstruction SuspensionTableConstruction.

  Section Reduction.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (** Basic Setup & Setting *)
    
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and assume any (schedule-independent) job-level priorities. *)
    Variable higher_eq_priority: JLDP_policy Job.
    
    (* Next, consider any suspension-aware schedule of the arrival sequence... *)
    Variable sched_susp: schedule Job.

    (* ...and the associated job suspension durations. *)
    Variable job_suspension_duration: job_suspension Job.
    
    (** Definition of the Reduction *)
    
    (* Now we proceed with the reduction.
       Let inflated_job_cost denote any job cost inflation, i.e., the cost of
       every job is as large as in the original schedule. *)
    Variable inflated_job_cost: Job -> time.

    (* To simplify the analysis, instead of observing an infinite schedule, we
       focus on the finite window delimited by the job we want to analyze.
       Let's call this job j, with arrival time arr_j, ... *)
    Variable j: Job.
    Let arr_j := job_arrival j.

    (* ...and suppose that we want to prove that the response time of j in sched_susp
       is upper-bounded by some value R.
       In the analysis, we only need to focus on the schedule prefix [0, arr_j + R). *)
    Variable R: time.

    (* In this sustainability proof, we must construct a new schedule with the inflated
        job costs that is no "better" for job j than the original schedule.
        Since we also modify the suspension durations, the construction is divided in
        two parts: (A) Schedule Construction, and (B) Definition of Suspension Times. *)
    
    (** (A) Schedule Construction *)
    Section ScheduleConstruction.

      (* Let's begin by defining the schedule construction function. *)
      Section ConstructionStep.
        
        (* For any time t, suppose that we have generated the schedule prefix [0, t).
           Then, we must define what should be scheduled at time t. *)
        Variable sched_prefix: schedule Job.
        Variable t: time.

        (* Consider the set of jobs that arrived up to time t. *)
        Let arrivals := jobs_arrived_up_to arr_seq t.

        (* Recall whether a job is pending in the new schedule. *)
        Let job_is_pending := pending job_arrival inflated_job_cost sched_prefix.
        
        (* Also, let's denote as late any job whose service in the new schedule is strictly
           less than the service in sched_susp plus the difference between job costs. *)
        Definition job_is_late any_j t :=
          service sched_prefix any_j t
            < service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j).

        (* In order not to have to prove complex properties about the entire schedule,
           we split the construction for the schedule prefix [0, arr_j + R) and for the
           suffix [arr_j + R, ...). *)

        (** (A.1) The prefix is built in a way that prevents jobs from getting late. *)
        Section Prefix.
          
          (* Consider the list of pending jobs in the new schedule that are either late
             or scheduled in sched_susp.
             (Note that when there are no late jobs, we pick the jobs that are scheduled
              in sched_susp so that the suspension times remain consistent.) *)
          Definition jobs_that_are_late_or_scheduled_in_sched_susp :=
            [seq any_j <- arrivals | job_is_pending any_j t &&
                                  (job_is_late any_j t || scheduled_at sched_susp any_j t)].

          (* From that list, we take one of the (possibly many) highest-priority jobs,
             or None, in case there are no late jobs and sched_susp is idle. *)
          Definition highest_priority_late_job :=
            seq_min (higher_eq_priority t) jobs_that_are_late_or_scheduled_in_sched_susp. 

        End Prefix.

        (** (A.2) In the suffix, we just pick the highest-priority pending job
                  so that the schedule constraints are satisfied. *)
        Section Suffix.

          (* From the list of pending jobs in the new schedule, ... *)
          Definition pending_jobs :=
            [seq any_j <- arrivals | job_is_pending any_j t ].

          (* ...let's take one of the (possibly many) highest-priority jobs. *)
          Definition highest_priority_job :=
            seq_min (higher_eq_priority t) pending_jobs.
          
        End Suffix.

        (** (A.3) In the end, we just combine the prefix and suffix schedules. *)
        Definition build_schedule :=
          if t < arr_j + R then
            highest_priority_late_job (* PREFIX (see A.1) *)
          else
            highest_priority_job. (* SUFFIX (see A.2) *)
        
      End ConstructionStep.

      (* To conclude, starting from the empty schedule, ...*)
      Let empty_schedule : schedule Job := fun t => None.

      (* ...we use the recursive definition above to construct the new schedule. *)
      Definition sched_new :=
        build_schedule_from_prefixes build_schedule empty_schedule.

    End ScheduleConstruction.
    
    (** (B) Definition of Suspension Times *)
    
    (* Having decided when jobs should be scheduled, we now define when they should suspend
       so that the schedule properties remain consistent. *)
    Section DefiningSuspension.

      (* Recall the definition of a suspended job in sched_susp. *)
      Let job_is_suspended_in_sched_susp :=
        suspended_at job_arrival job_cost job_suspension_duration sched_susp.

      (* Based on the notion of a "late" job from the schedule construction, we say that a
         job is suspended at time t in sched_new iff:
         (a) time t precedes arr_j + R (i.e., suspensions only occur in the prefix),
         (b) the job is suspended in sched_susp at time t, and
         (c) the job is not late in sched_new at time t. *)
      Definition suspended_in_sched_new (any_j: Job) (t: time) :=
        (t < arr_j + R) && job_is_suspended_in_sched_susp any_j t
                        && ~~ job_is_late sched_new any_j t.

      (* Next, using this suspension predicate, we build a table of suspension durations
         that is valid up to time (arr_j + R).
         For more details, see model/schedule/uni/susp/build_suspension_table.  *)
      Definition reduced_suspension_duration :=
        build_suspension_duration sched_new (arr_j + R) suspended_in_sched_new.
            
    End DefiningSuspension.
    
  End Reduction.
  
End SustainabilityAllCosts.