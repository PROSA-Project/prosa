Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.schedule.uni.schedule prosa.classic.model.schedule.uni.response_time.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Schedulability.

  Import Job SporadicTaskset ArrivalSequence UniprocessorSchedule ResponseTime.

  (* In this section, we define the notion of deadline miss. *)
  Section DeadlineMisses.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.    

    Context {Task: eqType}.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* For simplicity, let's define some local names. *)
    Let job_completed_by := completed_by job_cost sched.
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.

    Section Definitions.

      (* In this section, we define the notion of deadline miss for a job. *)
      Section JobLevel.
  
         (* We say that a job j...*)
        Variable j: Job.

        (* ...misses no deadline if it completes by its absolute deadline.*)
        Definition job_misses_no_deadline :=
          job_completed_by j (job_arrival j + job_deadline j).
          
      End JobLevel.

      (* Next, we define the notion of deadline miss for a task. *)
      Section TaskLevel.

        (* We say that a task tsk... *)
        Variable tsk: Task.

        (* ...misses no deadline if all of its jobs complete by their absolute deadline. *)
        Definition task_misses_no_deadline :=
          forall j,
            arrives_in arr_seq j ->
            job_task j = tsk ->
            job_misses_no_deadline j.
        
      End TaskLevel.

      (* Next, we define the notion of deadline miss for a task set. *)
      Section TaskSetLevel.

        (* We say that a task set ts... *)
        Variable ts: seq Task.

        (* ...misses no deadline if all of its tasks do not miss any deadlines. *)
        Definition taskset_misses_no_deadline :=
          forall tsk,
            tsk \in ts ->
            task_misses_no_deadline tsk.
        
      End TaskSetLevel.
      
    End Definitions.

    (* In this section, we prove some lemmas related to schedulability. *)
    Section Lemmas.

      Variable task_cost: Task -> time.
      Variable task_deadline: Task -> time.

      (* First, we infer schedulability from the response-time bounds of a task. *)
      Section ResponseTimeIsBounded.

        (* Assume that all jobs in the arrival sequence have the same deadline
           as their tasks. *)
        Hypothesis H_job_deadline_eq_task_deadline:
          forall j,
            arrives_in arr_seq j ->
            job_deadline_eq_task_deadline task_deadline job_deadline job_task j.
        
        (* Also assume that jobs don't execute after completion. *)
        Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

        (* Let tsk be any task.*)
        Variable tsk: Task.

        (* If tsk has response-time bound R that is no larger than its deadline, ... *)
        Variable R: time.
        Hypothesis H_R_le_deadline: R <= task_deadline tsk.
        Hypothesis H_response_time_bounded: response_time_bounded_by tsk R.

        (* ...then tsk misses no deadline. *)
        Lemma task_completes_before_deadline:
          task_misses_no_deadline tsk.
        Proof.
          unfold valid_sporadic_job, valid_realtime_job in *.
          intros j ARRj JOBtsk.
          apply completion_monotonic with (t := job_arrival j + R);
            last by apply H_response_time_bounded.
          rewrite leq_add2l.
          apply: (leq_trans H_R_le_deadline).
            by rewrite H_job_deadline_eq_task_deadline // -JOBtsk leqnn.
       Qed.

     End ResponseTimeIsBounded.
      
   End Lemmas.

  End DeadlineMisses.
  
End Schedulability.