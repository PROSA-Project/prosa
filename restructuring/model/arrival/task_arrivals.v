From rt.restructuring.model Require Export task.

(* In this file we provide basic definitions related to tasks on arrival sequences. *)
Section TaskArrivals.

  (* Consider any type of job associated with any type of tasks. *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (* Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  Section Definitions.

    (* Let tsk be any task. *)
    Variable tsk : Task.

    (* We define the sequence of jobs of tsk arriving at time t. *)
    Definition task_arrivals_at (t : instant) : seq Job :=
      [seq j <- arrivals_at arr_seq t | job_task j == tsk].

    (* By concatenation, we construct the list of jobs of tsk that arrived in the
       interval [t1, t2). *)
    Definition task_arrivals_between (t1 t2 : instant) :=
      [seq j <- arrivals_between arr_seq t1 t2 | job_task j == tsk].

    (* Based on that, we define the list of jobs of tsk that arrived up to time t, ...*)
    Definition task_arrivals_up_to (t : instant) := task_arrivals_between 0 t.+1.

    (* ...and the list of jobs of tsk that arrived strictly before time t ... *)
    Definition task_arrivals_before (t : instant) := task_arrivals_between 0 t.

    (* ... and also count the number of job arrivals. *)
    Definition number_of_task_arrivals (t1 t2 : instant) :=
      size (task_arrivals_between t1 t2).
    
  End Definitions.

  (* We define a predicate for arrival sequences for which jobs come from a taskset. *)
  Definition arrivals_come_from_taskset (ts : seq Task) :=
    forall j, arrives_in arr_seq j -> job_task j \in ts.

End TaskArrivals.