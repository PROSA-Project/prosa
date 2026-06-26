Require Import prosa.util.int.
Require Export prosa.model.priority.classes.

(** * GEL Priority Policy  *)

(** We define the class of "Global-EDF-like" (GEL) priority policies, as first
    introduced by Leontyev et al. ("Multiprocessor Extensions to Real-Time
    Calculus", Real-Time Systems, 2011).

    Later work focused on uniprocessor systems also refers to this policy as
    "EDF-like" (EL) --- for example, see Guenzel et al. ("EDF-like scheduling for
    self-suspending real-time tasks", RTSS, 2022).

    GEL scheduling is a (large) subset of the class of JLFP policies, which
    structurally resembles EDF scheduling, hence the name. Under GEL scheduling,
    each task has a constant "priority point offset."  Each job's priority point
    is given by its arrival time plus its task's offset, with the interpretation
    that an earlier priority point implies higher priority.

    EDF and FIFO are both special cases of GEL with the offset respectively
    being the relative deadline and zero. *)

(** To begin, we define the offset type. Note that an offset may be negative. *)
Definition offset := int.

(** We define a task-model parameter to express each task's relative priority point. *)
Class PriorityPoint (Task : TaskType) := { task_priority_point : Task -> offset }.

(** Based on the task-level relative priority-point parameter, we
    define a job's absolute priority point in a straightforward manner.
    To this end, we need to introduce some context first. *)
Section AbsolutePriorityPoint.
  (** For any type of tasks with relative priority points, ... *)
  Context {Job : JobType} {Task : TaskType} `{JobTask Job Task}
    `{PriorityPoint Task} `{JobArrival Job}.

  (** ... a job's absolute priority point is given by its arrival time
          plus its task's relative priority point. *)
  Definition job_priority_point (j : Job) :=
    ((job_arrival j)%:R + task_priority_point (job_task j))%R.

End AbsolutePriorityPoint.

(** We define what it means for an abstract job-level fixed-priority policy to
    behave as a GEL policy. *)
Section GELPolicy.

  (** Consider jobs of tasks with relative priority points. *)
  Context {Job : JobType} {Task : TaskType} `{JobTask Job Task}
    `{PriorityPoint Task} `{JobArrival Job}.

  (** A JLFP policy is GEL if it assigns higher priority to jobs with earlier
      absolute priority points. That is, job [j1] has higher or equal priority
      than job [j2] if and only if [j1]'s priority point is no later than
      [j2]'s priority point. *)
  Definition policy_is_GEL (JLFP : JLFP_policy Job) :=
    forall j1 j2,
      hep_job j1 j2 = (job_priority_point j1 <= job_priority_point j2)%R.

End GELPolicy.
