From rt.util Require Import all.
From rt.restructuring.behavior Require Export arrival_sequence.
From rt.restructuring.model Require Export task_arrivals.

(* In this section, we define the notion of arrival curves, which
   can be used to reason about the frequency of job arrivals. *)
Section ArrivalCurves.

  Context {Task: TaskType}.
  Context {Job: JobType}.
  Context `{JobTask Job Task}.

  (* Consider any job arrival sequence. *)
  Variable arr_seq: arrival_sequence Job.

  (* First, we define what constitutes an arrival bound for a task. *)
  Section ArrivalCurves.

    (* We say that num_arrivals is a valid arrival curve for task tsk iff *)
    (* [num_arrivals] is a monotonic function that equals 0 for the empty *)
    (* interval delta = 0. *)
    Definition valid_arrival_curve (tsk: Task) (num_arrivals: duration -> nat) :=
      num_arrivals 0 = 0 /\
      monotone num_arrivals leq.

    (* We say that max_arrivals is an upper arrival bound for tsk iff, for any interval [t1, t2),
     [max_arrivals (t2 - t1)] bounds the number of jobs of tsk that arrive in that interval. *)
    Definition respects_max_arrivals (tsk: Task) (max_arrivals: duration -> nat) :=
      forall (t1 t2: instant),
        t1 <= t2 ->
        size (task_arrivals_between arr_seq tsk t1 t2) <= max_arrivals (t2 - t1).

    (* We define in the same way lower arrival bounds *)
    Definition respects_min_arrivals (tsk: Task) (min_arrivals: duration -> nat) :=
      forall (t1 t2: instant),
        t1 <= t2 ->
        min_arrivals (t2 - t1) <= size (task_arrivals_between arr_seq tsk t1 t2).

  End ArrivalCurves.

  Section SeparationBound.

    (* Then, we say that min_separation is a lower separation bound iff, for any number of jobs
       of tsk, min_separation lower-bounds the minimum interval length in which that number
       of jobs can be spawned. *)
    Definition respects_min_separation tsk (min_separation: nat -> duration) :=
      forall t1 t2,
          t1 <= t2 ->
          min_separation (size (task_arrivals_between arr_seq tsk t1 t2)) <= t2 - t1.

    (* We define in the same way upper separation bounds *)
    Definition respects_max_separation tsk (max_separation: nat -> duration):=
      forall t1 t2,
        t1 <= t2 ->
        t2 - t1 <= max_separation (size (task_arrivals_between arr_seq tsk t1 t2)).

  End SeparationBound.

End ArrivalCurves.

(* We define generic classes for arrival curves  *)
Class MaxArrivals (Task: TaskType) := max_arrivals: Task -> duration -> nat.

Class MinArrivals (Task: TaskType) := min_arrivals: Task -> duration -> nat.

Class MaxSeparation (Task: TaskType) := max_separation: Task -> nat -> duration.

Class MinSeparation (Task: TaskType) := min_separation: Task -> nat -> duration.

Section ArrivalCurvesModel.

  Context {Task: TaskType} {Job: JobType}.
  Context `{JobTask Job Task}.

  Context `{MaxArrivals Task} `{MinArrivals Task} `{MaxSeparation Task} `{MinSeparation Task}.

  Variable ts: seq Task.

  (* We say that arrivals is a valid arrival curve for a taskset if it is valid for any task
     in the taskset *)
  Definition valid_taskset_arrival_curve (arrivals : Task -> duration -> nat) :=
    forall tsk,
      tsk \in ts ->
      valid_arrival_curve tsk (arrivals tsk).

  Variable arr_seq: arrival_sequence Job.

  (* We say that max_arrivals is an arrival bound for taskset ts *)
  (* iff max_arrival is an arrival bound for any task from ts. *)
  Definition taskset_respects_max_arrivals :=
    forall (tsk: Task), tsk \in ts -> respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  Definition taskset_respects_min_arrivals :=
    forall (tsk: Task), tsk \in ts -> respects_min_arrivals arr_seq tsk (min_arrivals tsk).

  Definition taskset_respects_max_separation :=
    forall (tsk: Task), tsk \in ts -> respects_max_separation arr_seq tsk (max_separation tsk).

  Definition taskset_respects_min_separation :=
    forall (tsk: Task), tsk \in ts -> respects_min_separation arr_seq tsk (min_separation tsk).

End ArrivalCurvesModel.