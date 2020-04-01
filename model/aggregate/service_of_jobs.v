Require Export prosa.model.priority.classes.

(** * Service Received by Sets of Jobs *)

(** In this file, we define the notion of service received by a set of
    jobs. *)

Section ServiceOfJobs.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  
  (** Consider any kind of processor model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *) 
  Variable arr_seq : arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched : schedule PState.
  
  (** First, we define the service received by a generic set of jobs. *)
  Section ServiceOfSetOfJobs.

    (** Let [P] be any computable predicate over jobs, ...*)
    Variable P : pred Job.
    
    (** ... and let [jobs] denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** We define the cumulative service received at time [t] by
        jobs in [jobs] that satisfy predicate [P] ... *)
    Definition service_of_jobs_at (t : instant) :=
      \sum_(j <- jobs | P j) service_at sched j t.
    
    (** ... and the cumulative service received during the interval
        <<[t1, t2)>> by jobs that satisfy predicate [P]. *)
    Definition service_of_jobs (t1 t2 : instant) :=
      \sum_(j <- jobs | P j) service_during sched j t1 t2.

  End ServiceOfSetOfJobs.
  
  (** Next, we define the service received by jobs with higher or
     equal priority under JLFP policies. *)
  Section PerJobPriority.
    
    (** Consider any JLDP policy. *)
    Context `{JLFP_policy Job}.
    
    (** Let jobs denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** Let j be the job to be analyzed. *)
    Variable j : Job.

    (** Based on the definition of jobs of higher or equal priority, ... *)
    Let of_higher_or_equal_priority j_hp := hep_job j_hp j.
    
    (** ...we define the service received during <<[t1, t2)>> by jobs of higher or equal priority. *)
    Definition service_of_higher_or_equal_priority_jobs (t1 t2 : instant) :=
      service_of_jobs of_higher_or_equal_priority jobs t1 t2.

  End PerJobPriority.

  (** Finally, we define the notion of cumulative service received by
      the jobs of a given task. *)  
  Section ServiceOfTask.
    
    (** Let [tsk] be the task to be analyzed ... *)
    Variable tsk : Task. 

    (** ... and let [jobs] denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** We define the cumulative task service received by the jobs of
        task [tsk] within time interval <<[t1, t2)>>. *)
    Definition task_service_of_jobs_in t1 t2 :=
      service_of_jobs (job_of_task tsk) jobs t1 t2.

  End ServiceOfTask.

End ServiceOfJobs.
