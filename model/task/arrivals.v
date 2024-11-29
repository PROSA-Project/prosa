Require Export prosa.model.task.concept.

(** In this module, we provide basic definitions concerning the job
    arrivals of a given task. *)

Section TaskArrivals.

  (** Consider any type of job associated with any type of tasks. *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any job arrival sequence ...  *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any task. *)
  Variable tsk : Task.

  (** First, we construct the list of jobs of task [tsk] that arrive
      in a given half-open interval <<[t1, t2)>>. *)
  Definition task_arrivals_between (t1 t2 : instant) :=
    [seq j <- arrivals_between arr_seq t1 t2 | job_of_task tsk j].

  (** Based on that, we define the list of jobs of task [tsk] that
      arrive up to and including time [t], ... *)
  Definition task_arrivals_up_to (t : instant) :=
    task_arrivals_between 0 t.+1.

  (** ... the list of jobs of task [tsk] that arrive strictly
      before time [t], ... *)
  Definition task_arrivals_before (t : instant) :=
    task_arrivals_between 0 t.

  (** ... the list of jobs of task [tsk] that arrive exactly at an instant [t], ... *)
  Definition task_arrivals_at (tsk : Task) (t : instant) :=
    [seq j <- arrivals_at arr_seq t | job_of_task tsk j].
  
  (** ... and finally count the number of job arrivals. *)
  Definition number_of_task_arrivals (t1 t2 : instant) :=
    size (task_arrivals_between t1 t2).

  (** ... and also count the cost of job arrivals. *)
  Definition cost_of_task_arrivals (t1 t2 : instant) :=
    \sum_(j <- task_arrivals_between t1 t2) job_cost j.

  (** In the following, suppose there is a deadline associated with each job. *)
  Context `{JobDeadline Job}.

  (** We define the list of jobs of task [tsk] that arrive in
      a given half-open interval <<[t1, t2)>> and that also have a deadline
      within the closed interval <<[t1, t2]>>, ... *)
  Definition task_arrivals_with_deadline_within (t1 t2 : instant) :=
    [seq j <- arrivals_between arr_seq t1 t2 | job_of_task tsk j & job_deadline j <= t2].

  (** ... and similarly define the count of such jobs. *)
  Definition number_of_task_arrivals_with_deadline_within (t1 t2 : instant) :=
    size (task_arrivals_with_deadline_within t1 t2).

End TaskArrivals.

(** In this section we introduce a few definitions
    regarding arrivals of a particular task prior to a job. *)
Section PriorArrivals.

  (** Consider any type of jobs associated with any type of tasks. *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  
  (** Consider any arrival sequence of jobs ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any job [j]. *)
  Variable j : Job.
  
  (** We first define a sequence of jobs of a task 
   that arrive before or at [job_arrival j]. *)
  Definition task_arrivals_up_to_job_arrival :=
    task_arrivals_up_to arr_seq (job_task j) (job_arrival j).

  (** Next, we define a sequence of jobs of a task
   that arrive strictly before [job_arrival j]. *)
  Definition task_arrivals_before_job_arrival :=
    task_arrivals_before arr_seq (job_task j) (job_arrival j).

  (** Finally, we define a sequence of jobs of a task 
   that arrive at [job_arrival j]. *)
  Definition task_arrivals_at_job_arrival :=
    task_arrivals_at arr_seq (job_task j) (job_arrival j).
  
End PriorArrivals.

(** In this section, we define the notion of a job's index. *)
Section JobIndex.

  (** Consider any type of tasks, ... *)
  Context {Task : TaskType}.

  (** ... any type of jobs associated with the tasks, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.

  (** ... and any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.  
  
  (** Given a job [j], we define a concept of job index as the number
      of jobs of the same task as [j] that arrived before or at the 
      same instant as [j]. Please note that job indices start from zero. *)
  Definition job_index (j : Job) :=
    index j (task_arrivals_up_to_job_arrival arr_seq j).

End JobIndex.

(** In this section we define the notion of a previous job 
    for any job with a positive [job_index]. *)
Section PreviousJob.

  (** Consider any type of jobs associated with any type of tasks. *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  
  (** Consider any job arrival sequence.  *)
  Variable arr_seq : arrival_sequence Job.

  Let task_arrivals_up_to_job_arrival j := task_arrivals_up_to_job_arrival arr_seq j.
  Let prev_index j := job_index arr_seq j - 1.
    
  (** For any job [j] with a positive [job_index] we define the notion 
     of a previous job. *)  
  Definition prev_job (j : Job) := nth j (task_arrivals_up_to_job_arrival j) (prev_index j).

End PreviousJob.
