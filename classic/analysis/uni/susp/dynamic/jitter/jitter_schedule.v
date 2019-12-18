Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

(* In this file, we formalize a reduction from a suspension-aware schedule
   to a jitter-aware schedule. *)
Module JitterScheduleConstruction.

  Import UniprocessorScheduleWithJitter Suspension Priority ScheduleConstruction.

  Section ConstructingJitterSchedule.

    Context {Task: eqType}.    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> Task.

    (** Basic Setup & Setting*)
    
    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
    
    (* Assume any FP policy and the corresponding job-level priority relation. *)
    Variable higher_eq_priority: FP_policy Task.
    Let job_higher_eq_priority := FP_to_JLFP job_task higher_eq_priority.
    
    (* Consider the original job and task costs from the suspension-aware schedule... *)
    Variable job_cost: Job -> time.
    Variable task_cost: Task -> time.

    (* ...and assume that jobs have associated suspension times. *)
    Variable job_suspension_duration: job_suspension Job.
      
    (* Next, consider any suspension-aware schedule of the arrival sequence. *)
    Variable sched_susp: schedule Job.

    (** Definition of the Reduction *)
    
    (* Now we proceed with the reduction. Let j be the job to be analyzed. *)
    Variable j: Job.

    (* For simplicity, we give some local names for the parameters of this job... *)
    Let arr_j := job_arrival j.
    Let task_of_j := job_task j.

    (* ...and recall the definition of other higher-or-equal-priority tasks. *)
    Let other_hep_task tsk_other :=
      higher_eq_priority tsk_other task_of_j && (tsk_other != task_of_j).
    
    (* Moreover, assume that jobs from higher-priority tasks are associated a response-time bound R. *)
    Variable R: Job -> time.

    (* Now we are going to redefine the job parameters for the new schedule. *)
    Section DefiningJobParameters.

      (* First, we inflate job costs with suspension time. *)
      Section CostInflation.

        (* Recall the total suspension time of a job in the original schedule. *)
        Let job_total_suspension :=
          total_suspension job_cost job_suspension_duration.

        (* We inflate job costs as follows.
           (a) The cost of job j is inflated with its total suspension time.
           (b) The cost of all other jobs remains unchanged. *)
        Definition inflated_job_cost (any_j: Job) :=
          if any_j == j then
            job_cost any_j + job_total_suspension any_j
          else
            job_cost any_j.
        
      End CostInflation.
 
      (* Next, we show how to set the job jitter in the new schedule
         to compensate for the suspension times. *)
      Section ConvertingSuspensionToJitter.

        (* Let any_j be any job in the new schedule. *)
        Variable any_j: Job.

        (* First, recall the distance between any_j and job j that is to be analyzed.
           Note that since we use natural numbers, this distance saturates to 0 if
           any_j arrives later than j. *)
        Let distance_to_j := job_arrival j - job_arrival any_j.
        
        (* Then, we define the actual job jitter in the new schedule as follows.
           a) For every job of higher-priority tasks (with respect to job j), the jitter is set to
              the minimum between the distance to j and the term (R any_j - job_cost any_j).
           b) The remaining jobs have no jitter.
           
           The intuition behind this formula is that any_j is to be released as close to job j as
           possible, while not "trespassing" the response-time bound (R any_j) from sched_susp,
           which is only assumed to be valid for higher-priority tasks. *)
        Definition job_jitter :=
          if other_hep_task (job_task any_j) then
            minn distance_to_j (R any_j - job_cost any_j)
          else 0.

      End ConvertingSuspensionToJitter.
      
    End DefiningJobParameters.

    (** Schedule Construction *)
    
    (* Next we generate a jitter-aware schedule using the job parameters above.
       For that, we always pick the highest-priority pending job (after jitter) in
       the new schedule. However, if there are multiple highest-priority jobs, we
       try not to schedule job j in order to maximize interference. *)
    Section ScheduleConstruction.

      (* First, we define the schedule construction function. *)
      Section ConstructionStep.
        
        (* For any time t, suppose that we have generated the schedule prefix in the
           interval [0, t). Then, we must define what should be scheduled at time t. *)
        Variable sched_prefix: schedule Job.
        Variable t: time.

        (* For simplicity, let's define some local names. *)
        Let job_is_pending := pending job_arrival inflated_job_cost job_jitter sched_prefix.
        Let actual_job_arrivals_up_to := actual_arrivals_up_to job_arrival job_jitter arr_seq.
        Let lower_priority j1 j2 := ~~ job_higher_eq_priority j1 j2.

        (* Next, consider the list of pending jobs at time t that are different from j
           and whose jitter has passed, in the new schedule. *)
        Definition pending_jobs_other_than_j :=
          [seq j_other <- actual_job_arrivals_up_to t | job_is_pending j_other t & j_other != j].

        (* From the list of pending jobs, we can return one of the (possibly many)
           highest-priority jobs, or None, in case there are no pending jobs. *)
        Definition highest_priority_job_other_than_j :=
          seq_min job_higher_eq_priority pending_jobs_other_than_j.

        (* Then, we construct the new schedule at time t as follows.
           a) If job j is pending and the highest-priority job (other than j) has
              lower priority than j, we have to schedule j.
           b) Else, if job j is not pending, we pick one of the highest priority pending jobs. *)
        Definition build_schedule : option Job :=
          if job_is_pending j t then
            if highest_priority_job_other_than_j is Some j_hp then
              if lower_priority j_hp j then
                Some j
              else Some j_hp
            else Some j  
          else highest_priority_job_other_than_j.

      End ConstructionStep.

      (* Finally, starting from the empty schedule, ...*)
      Let empty_schedule : schedule Job := fun t => None.

      (* ...we use the recursive definition above to construct the jitter-aware schedule. *)
      Definition sched_jitter := build_schedule_from_prefixes build_schedule empty_schedule.

    End ScheduleConstruction.    

  End ConstructingJitterSchedule.
  
End JitterScheduleConstruction.