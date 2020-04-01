Require Export prosa.analysis.definitions.busy_interval.

(** * Cumulative Priority Inversion for JLFP-models *)
(** In this module we define the notion of cumulative priority inversion for uni-processor for JLFP schedulers. *)
Section CumulativePriorityInversion.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.    

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  
  (** Next, consider any ideal uniprocessor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}. 

  (** In this section, we define a notion of bounded priority inversion experienced by a job. *)
  Section JobPriorityInversionBound.

    (** Consider an arbitrary task [tsk]. *)
    Variable tsk : Task.

    (** Consider any job j of [tsk]. *)
    Variable j : Job.
    Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
    Hypothesis H_job_task : job_of_task tsk j. 

    (** We say that the job incurs priority inversion if it has higher
        priority than the scheduled job. Note that this definition
        implicitly assumes that the scheduler is
        work-conserving. Therefore, it cannot be applied to models
        with jitter or self-suspensions. *)
    Definition is_priority_inversion (t : instant) :=
      if sched t is Some jlp then
        ~~ hep_job jlp j
      else false.
    
    (** Then we compute the cumulative priority inversion incurred by
         a job within some time interval <<[t1, t2)>>. *)
    Definition cumulative_priority_inversion (t1 t2 : instant) :=
      \sum_(t1 <= t < t2) is_priority_inversion t.

    (** We say that priority inversion of job [j] is bounded by a constant [B] iff cumulative 
         priority inversion within any busy interval prefix is bounded by [B]. *)
    Definition priority_inversion_of_job_is_bounded_by (B : duration) :=
      forall (t1 t2 : instant),
        busy_interval_prefix arr_seq sched j t1 t2 ->
        cumulative_priority_inversion t1 t2 <= B.

  End JobPriorityInversionBound.

  (** In this section, we define a notion of the bounded priority inversion for task. *)
  Section TaskPriorityInversionBound.

    (** Consider an arbitrary task [tsk]. *)
    Variable tsk : Task.

    (** We say that task [tsk] has bounded priority inversion if all 
         its jobs have bounded cumulative priority inversion. *)
    Definition priority_inversion_is_bounded_by (B : duration) :=
      forall (j : Job),
        arrives_in arr_seq j ->
        job_task j = tsk ->
        job_cost j > 0 -> 
        priority_inversion_of_job_is_bounded_by j B.

  End TaskPriorityInversionBound.

End CumulativePriorityInversion.
