Require Import rt.util.all.
Require Import rt.util.nondecreasing.

Require Import rt.restructuring.behavior.all.
Require Import rt.restructuring.model.job.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.preemption.job.parameters.
Require Import rt.restructuring.model.preemption.task.parameters.
Require Import rt.restructuring.model.preemption.job.instance.limited.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Platform for Models with Limited Preemptions *)
(** In this section, we introduce a set of requirements for function
    [task_preemption_points], so it is coherent with limited
    preemptions model. *)
Section ModelWithFixedPreemptionPoints.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskPreemptionPoints Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptionPoints Job}.  

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.  
  
  (** Consider an arbitrary task set ts. *)     
  Variable ts : list Task.

  (** Next, we describe structural properties that a sequence of
     preemption points of task should satisfy. *)
  
  (** (1) We require the sequence of preemption points to contain the beginning... *)
  Definition task_beginning_of_execution_in_preemption_points :=
    forall tsk, tsk \in ts -> first0 (task_preemption_points tsk) = 0.

  (** ... and (2) the end of execution for any job j.*)
  Definition task_end_of_execution_in_preemption_points :=
    forall tsk, tsk \in ts -> last0 (task_preemption_points tsk) = task_cost tsk.

  (** (3) We require the sequence of preemption points 
     to be a nondecreasing sequence. *)
  Definition task_preemption_points_is_nondecreasing_sequence :=
    forall tsk, tsk \in ts -> nondecreasing_sequence (task_preemption_points tsk).

  (** (4) Next, we require the number of nonpreemptive segments of a job to be 
     equal to the number of nonpreemptive segments of its task. Note that 
     some of nonpreemptive segments of a job can have zero length, nonetheless
     the number of segments should match. *)
  Definition job_consists_of_the_same_number_of_segments_as_task :=
    forall j,
      arrives_in arr_seq j -> 
      size (job_preemption_points j) = size (task_preemption_points (job_task j)).

  (** (5) We require lengths of nonpreemptive segments of a job to be bounded 
     by lenghts of the corresponding segments of its task.  *)
  Definition lengths_of_task_segments_bound_length_of_job_segments :=
    forall j n,
      arrives_in arr_seq j -> 
      nth 0 (distances (job_preemption_points j)) n
      <= nth 0 (distances (task_preemption_points (job_task j))) n.
  
  (** (6) Lastly, we ban empty nonpreemptive segments for tasks. *)
  Definition task_segments_are_nonempty :=
    forall tsk n,
      (tsk \in ts) ->
      n < size (distances (task_preemption_points tsk)) ->
      ε <= nth 0 (distances (task_preemption_points tsk)) n.
  
  (** We define a valid task-level model with fixed preemption points 
     as a concatenation of the hypotheses above. *) 
  Definition valid_fixed_preemption_points_task_model :=
    task_beginning_of_execution_in_preemption_points /\
    task_end_of_execution_in_preemption_points /\
    task_preemption_points_is_nondecreasing_sequence /\
    job_consists_of_the_same_number_of_segments_as_task /\
    lengths_of_task_segments_bound_length_of_job_segments /\
    task_segments_are_nonempty.
  
  (** We define a valid model with fixed preemption points as 
     a model with fixed preemptions points at the task-level
     and model with limited preemptions at the job-level. *)
  Definition valid_fixed_preemption_points_model :=
    valid_limited_preemptions_job_model arr_seq /\
    valid_fixed_preemption_points_task_model.
  
End ModelWithFixedPreemptionPoints.
