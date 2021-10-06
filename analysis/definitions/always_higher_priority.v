Require Export prosa.model.priority.classes.

(** * Always Higher Priority *)
(** In this section, we define what it means for a job to always have
    a higher priority than another job. *) 
Section AlwaysHigherPriority.
 
  (** Consider any type of jobs ... *) 
  Context {Job : JobType}.

  (** ... and any JLDP policy. *) 
  Context `{JLDP_policy Job}.
  
  (** We say that a job [j1] always has higher priority than job [j2]
      if, at any time [t], the priority of job [j1] is strictly higher than
      the priority of job [j2]. *)
  Definition always_higher_priority (j1 j2 : Job) :=
    forall t, hep_job_at t j1 j2 && ~~ hep_job_at t j2 j1.  

End AlwaysHigherPriority. 
