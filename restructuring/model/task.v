From mathcomp Require Export ssrbool.
From rt.restructuring.behavior Require Export job.

From rt.restructuring.behavior Require Export arrival_sequence.
  
(* Throughout the library we assume that tasks have decidable equality *)
Definition TaskType := eqType.

(* Definition of a generic type of parameter relating jobs to tasks *)
Class JobTask (J : JobType) (T : TaskType) := job_task : J -> T.

Section SameTask.
  
  (* For any type of job associated with any type of tasks... *)
  Context {Job: JobType}.
  Context {Task: TaskType}.
  Context `{JobTask Job Task}.

  (* ... we say that two jobs j1 and j2 are from the same task iff job_task j1
     is equal to job_task j2. *)
  Definition same_task j1 j2 := job_task j1 == job_task j2.

End SameTask.


(* Definition of a generic type of parameter for task deadlines *)
Class TaskDeadline (Task : TaskType) := task_deadline : Task -> duration.

(* Given task deadlines and a mapping from jobs to tasks we provide a generic definition of job_deadline *)
Instance job_deadline_from_task_deadline
         (Job : JobType) (Task : TaskType)
         `{TaskDeadline Task} `{JobArrival Job} `{JobTask Job Task} : JobDeadline Job :=
  fun j => job_arrival j + task_deadline (job_task j).


(* Definition of a generic type of parameter for task cost *)
Class TaskCost (T : TaskType) := task_cost : T -> duration.


(* In this section, we introduce properties of a task. *)
Section PropertesOfTask.

  (* Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.

  (* Next we intrdoduce attributes of a valid sporadic task. *)
  Section ValidTask.
    
    (* Consider an arbitrary task. *)
    Variable tsk: Task.
    
    (* The cost and deadline of the task must be positive. *)
    Definition task_cost_positive := task_cost tsk > 0.
    Definition task_deadline_positive := task_deadline tsk > 0.

    (* The task cost cannot be larger than the deadline or the period. *)
    Definition task_cost_le_deadline := task_cost tsk <= task_deadline tsk.
    
  End ValidTask.
  
  (* Job of task *)
  Section ValidJobOfTask.
    
    (* Consider any type of jobs associated with the tasks ... *)
    Context {Job : JobType}.
    Context `{JobTask Job Task}.
    Context `{JobCost Job}.
    Context `{JobDeadline Job}.

    (* Consider an arbitrary job. *)
    Variable j: Job.

    (* The job cost cannot be larger than the task cost. *)
    Definition job_cost_le_task_cost :=
      job_cost j <= task_cost (job_task j).

  End ValidJobOfTask.

  (* Jobs of task *)
  Section ValidJobsTask.
          
    (* Consider any type of jobs associated with the tasks ... *)
    Context {Job : JobType}.
    Context `{JobTask Job Task}.
    Context `{JobCost Job}.
    
    (* ... and any arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.

    (* The cost of a job from the arrival sequence cannot
       be larger than the task cost. *)
    Definition cost_of_jobs_from_arrival_sequence_le_task_cost :=
      forall j,
        arrives_in arr_seq j ->
        job_cost_le_task_cost j.

  End ValidJobsTask.

End PropertesOfTask.

(* In this section, we introduce properties of a task set. *)
Section PropertesOfTaskSet.

  (* Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (*  ... and any type of jobs associated with these tasks ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.

  (* ... and any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (* Consider an arbitrary task set. *)
  Variable ts : seq Task.

  (* Tasks from the task set have a positive cost. *)
  Definition tasks_cost_positive :=
    forall tsk,
      tsk \in ts ->
      task_cost_positive tsk. 

  (* All jobs in the arrival sequence come from the taskset. *)
  Definition all_jobs_from_taskset :=
    forall j,
      arrives_in arr_seq j ->
      job_task j \in ts.

End PropertesOfTaskSet. 