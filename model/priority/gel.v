Require Export prosa.model.priority.classes.
Require Export BinInt.

From mathcomp.zify Require Import ssrZ.

(** * GEL Priority Policy  *)

(** We define the class of "Global-EDF-like" (GEL) priority policies,
    as first introduced by Leontyev et al. ("Multiprocessor Extensions
    to Real-Time Calculus", Real-Time Systems, 2011).

    GEL scheduling is a (large) subset of the class of JLFP policies,
    which structurally resembles EDF scheduling, hence the name. Under
    GEL scheduling, each task has a constant "priority point offset."
    Each job's priority point is given by its arrival time plus its
    task's offset, with the interpretation that an earlier priority
    point implies higher priority.

    EDF and FIFO are both special cases of GEL with the offset
    respectively being the relative deadline and zero. *)

(** To begin, we define the offset type. Note that an offset may be negative. *)
Definition offset := Z.

(** We define a task-model parameter to express each task's relative priority point. *)
Class PriorityPoint (Task : TaskType) := task_priority_point : Task -> offset.

(** Based on the task-level relative priority-point parameter, we
    define a job's absolute priority point in a straightforward manner.
    To this end, we need to introduce some context first. *)
Section AbsolutePriorityPoint.
  (** For any type of tasks with relative priority points, ... *)
  Context {Job : JobType} {Task : TaskType} `{JobTask Job Task} `{PriorityPoint Task} `{JobArrival Job}.

  (** ... a job's absolute priority point is given by its arrival time
          plus its task's relative priority point. *)
  Definition job_priority_point (j : Job) := (Z.of_nat (job_arrival j) + task_priority_point (job_task j))%Z.
End AbsolutePriorityPoint.

(** The resulting definition of GEL is straightforward: a job [j1]'s
    priority is higher than or equal to a job [j2]'s priority iff
    [j1]'s absolute priority point is no later than [j2]'s absolute
    priority point.  *)
#[export] Instance GEL (Job : JobType) (Task : TaskType)
          `{PriorityPoint Task} `{JobArrival Job} `{JobTask Job Task} : JLFP_policy Job :=
{
  hep_job (j1 j2 : Job) := (job_priority_point j1 <=? job_priority_point j2)%Z
}.

(** In this section, we note three basic properties of the GEL policy:
    the priority relation is reflexive, transitive, and total.  *)
Section PropertiesOfGEL.

  (** Consider any type of tasks with relative priority points...*)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ...and jobs of these tasks. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task}.

  (** GEL is reflexive. *)
  Fact GEL_is_reflexive : reflexive_priorities.
  Proof. by move=> t j; apply: Z.leb_refl. Qed.

  (** GEL is transitive. *)
  Fact GEL_is_transitive : transitive_priorities.
  Proof. by move=> t y x z; apply: Zbool.Zle_bool_trans. Qed.

  (** GEL is total. *)
  Fact GEL_is_total : total_priorities.
  Proof. by move=> t j1 j2; apply: ZInstances.leZ_total. Qed.

End PropertiesOfGEL.

(** We add the above facts into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically where needed. *)
Global Hint Resolve
     GEL_is_reflexive
     GEL_is_transitive
     GEL_is_total
  : basic_rt_facts.
