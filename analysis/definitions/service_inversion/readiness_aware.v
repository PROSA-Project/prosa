Require Export prosa.model.priority.classes.
Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.definitions.service.
Require Export prosa.analysis.abstract.definitions.

(** * Service Inversion *)
(** In this section, we define the notion of service inversion for
    arbitrary processors. *)
Section ServiceInversion.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  Context `{!JobReady Job PState}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Assume a given JLDP policy. *)
  Context `{JLFP_policy Job}.

  (** Consider a job [j]. *)
  Variable j : Job.

  (** We say that the job incurs service inversion if it has higher
      priority than the job receiving service. Note that this
      definition is oblivious to whether job [j] is ready. Therefore,
      it may not apply as intuitively expected in models with jitter
      or self-suspensions. Further generalization of the concept is
      likely necessary to efficiently analyze models in which jobs may
      be pending without being ready. *)
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

  (** Consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.
  
  Context `{!JobReady Job PState}.
  
  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLDP policy. *)
  Context `{JLFP_policy Job}.
 
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}. 

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  Let busy_interval_prefix_ab := busy_interval_prefix sched.
  
  Definition service_inversion_is_bounded (B : duration) :=
    forall j t1 t2,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost_positive j ->
      busy_interval_prefix_ab j t1 t2 ->
      cumulative_service_inversion arr_seq sched j t1 t2 <= B.
 
End TaskServiceInversionBound.
