Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.arrival_sequence           
        prosa.classic.model.arrival.basic.task_arrival.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq div.

(* In this section, we define the notion of arrival curves, which
   can be used to reason about the frequency of job arrivals. *)
Module ArrivalCurves.
  
  Import ArrivalSequence TaskArrival.

  Section DefiningArrivalCurves.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> Task.
    
    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.

    (* Recall the job arrivals of tsk in a given interval [t1, t2). *)
    Let arrivals_of_tsk tsk := arrivals_of_task_between job_task arr_seq tsk.
    Let num_arrivals_of_tsk tsk := num_arrivals_of_task job_task arr_seq tsk.

    (* First, we define what constitutes an arrival bound for task tsk. *)
    Section ArrivalBound.

      (* Let max_arrivals denote any function that takes an interval length and 
         returns the associated number of job arrivals of task. 
         (This corresponds to the eta+ function in the literature.) *)
      Variable max_arrivals: Task -> time -> nat.

      (* Then, we say that max_arrivals is an arrival bound iff, for any interval [t1, t2), 
         [num_arrivals (t2 - t1)] bounds the number of jobs of tsk that arrive in that interval. *)
      Definition is_arrival_bound (tsk: Task) :=
        forall (t1 t2: time),
          t1 <= t2 -> 
          num_arrivals_of_tsk tsk t1 t2 <= max_arrivals tsk (t2 - t1).

      (* We say that max_arrivals is an arrival bound for taskset ts 
         iff max_arrival is an arrival bound for any task from ts. *) 
      Definition is_arrival_bound_for_taskset (ts: seq Task) :=
        forall (tsk: Task), tsk \in ts -> is_arrival_bound tsk.
      
      (* We provide the notion of an arrival curve that equals 0 for the empty interval. *)
      Definition zero_arrival_curve (tsk: Task) :=
        max_arrivals tsk 0 = 0.
      
      (* Next, we provide the notion of a monotonic arrival curve. *)
      Definition monotonic_arrival_curve (tsk: Task) :=
        monotone (max_arrivals tsk) leq.

      (* We say that max_arrivals is a proper arrival curve for task tsk iff 
         [max_arrivals tsk] is an arrival bound for task tsk and [max_arrivals tsk]
         is a monotonic function that equals 0 for the empty interval delta = 0. *)
      Definition proper_arrival_curve (tsk: Task) :=
        is_arrival_bound tsk /\
        zero_arrival_curve tsk /\
        monotonic_arrival_curve tsk.

      (* We say that max_arrivals is a family of proper arrival curves iff 
         for all tsk in ts [max_arrival tsk] is a proper arrival curve. *)         
      Definition family_of_proper_arrival_curves (ts: seq Task) :=
        forall (tsk: Task), tsk \in ts -> proper_arrival_curve tsk.

    End ArrivalBound.

    (* Next, we define the notion of a separation bound for task tsk, i.e., the smallest 
       interval length in which a certain number of jobs of tsk can be spawned. *)
    Section SeparationBound.
      
      (* Let min_length denote any function that takes a number of jobs and 
         returns an associated interval length. 
         (This corresponds to the delta- function in the literature.) *)
      Variable min_length: Task -> nat -> time.

      (* Then, we say that min_length is a separation bound iff, for any number of jobs 
         of tsk, min_separation lower-bounds the minimum interval length in which that number 
         of jobs can be spawned. *)
      Definition is_separation_bound tsk :=
        forall t1 t2,
          t1 <= t2 ->
          min_length tsk (num_arrivals_of_tsk tsk t1 t2) <= t2 - t1.

    End SeparationBound.

  End DefiningArrivalCurves.

End ArrivalCurves.

