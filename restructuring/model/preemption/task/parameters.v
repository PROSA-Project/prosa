Require Export rt.util.all.
Require Export rt.restructuring.model.task.concept.
(** * Static information about preemption points *)

(** Definition of a generic type of parameter relating a task 
    to the length of the maximum nonpreeptive segment. *)
Class TaskMaxNonpreemptiveSegment (Task : TaskType) :=
  task_max_nonpreemptive_segment : Task -> work.

(** Definition of a generic type of parameter relating a task
    to its run-to-completion threshold. *)
Class TaskRunToCompletionThreshold (Task : TaskType) :=
  task_run_to_completion_threshold : Task -> work.

(** Definition of a generic type of parameter relating task
    to the sequence of its preemption points. *)
Class TaskPreemptionPoints (Task : TaskType) :=
  task_preemption_points : Task -> seq work.

(** We provide a conversion from task preemption points to task max non-preemptive segment. *)
Instance TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
         (Task : TaskType) `{TaskPreemptionPoints Task} : TaskMaxNonpreemptiveSegment Task :=
  fun tsk => max0 (distances (task_preemption_points tsk)).

(** * Derived Parameters *) 
(** * Task Maximum and Last Non-preemptive Segment *)
(** In this section we define the notions of the maximal and 
    the last non-preemptive segments of a task. *)
Section MaxAndLastNonpreemptiveSegment.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** In addition, assume the existence of a function that
      maps a job to the sequence of its preemption points. *)
  Context `{TaskPreemptionPoints Task}.

  (** Next, we define a function [task_max_nonpr_segment] that
      maps a task to the length of the longest nonpreemptive segment
      of this task. *)
  Definition task_max_nonpr_segment (tsk : Task) :=
    max0 (distances (task_preemption_points tsk)).

  (** Similarly, [task_last_nonpr_segment] is a function that
      maps a job to the length of the last nonpreemptive segment. *)
  Definition task_last_nonpr_segment (tsk : Task) :=
    last0 (distances (task_preemption_points tsk)).
    
End MaxAndLastNonpreemptiveSegment.
