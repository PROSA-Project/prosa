Require Export prosa.model.priority.classes.
Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.definitions.service.
Require Export prosa.analysis.abstract.definitions.

(** * Service Inversion *)
(** In this section, we define a readiness aware notion of service inversion. *)
Section ServiceInversion.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider any kind of uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uni : uniprocessor_model PState.

  (** Consider any notion of readiness. *)
  Context `{!JobReady Job PState}.

  (** Consider any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Assume a given JLDP policy. *)
  Context `{JLFP_policy Job}.

  (** Consider a job [j]. *)
  Variable j : Job.

  (** We say that the service inversion is taking place at some instant [t] if a
      lower priority job is being served in spite of a higher-or-equal-priority
      job being schedulable. Note that the priority relation is based on [j]. *)
  Definition service_inversion (t : instant) :=
    has (hep_job ^~ j) [seq jhep <- arrivals_up_to arr_seq t | job_ready sched jhep t]
    && has (fun jlp => ~~ hep_job jlp j) (served_jobs_at arr_seq sched t).

  (** Then we compute the cumulative service inversion incurred by a
      job within some time interval <<[t1, t2)>>. *)
  Definition cumulative_service_inversion (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) service_inversion t.

End ServiceInversion.

(** In this section, we define a notion of the bounded service
    inversion for tasks. *)
Section TaskServiceInversionBound.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider any kind of uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uni : uniprocessor_model PState.
  
  (** Consider any notion of job readiness ... *)
  Context `{!JobReady Job PState}.
  
  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.
 
  (** Assume that we have some definition of interference and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}. 

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** Recall the notion of abstract busy interval prefix. *)
  Let busy_interval_prefix_ab := busy_interval_prefix sched.

  Definition service_inversion_is_bounded (B : duration) :=
    forall j t1 t2,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost_positive j ->
      busy_interval_prefix_ab j t1 t2 ->
      cumulative_service_inversion arr_seq sched j t1 t2 <= B.
 
End TaskServiceInversionBound.
