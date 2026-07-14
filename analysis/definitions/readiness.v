Require Export prosa.behavior.ready.
Require Export prosa.analysis.definitions.schedule_prefix.
Require Export prosa.model.preemption.parameter.
Require Export prosa.model.priority.classes.
Require Export prosa.model.task.sequentiality.

(** * Properties of Readiness Models *)

(** In this file, we define common properties of readiness models. *)
Section ReadinessModelProperties.

  (** For any type of jobs with costs and arrival times ... *)
  Context {Job : JobType} `{JobCost Job} `{JobArrival Job}.

  (** ... and any kind of processor model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... consider a  notion of job readiness. *)
  Variable ReadinessModel : JobReady Job PState.

  (** First, we define a notion of non-clairvoyance for readiness
      models. Intuitively, whether a job is ready or not should depend only on
      the past (i.e., prior allocation decisions and job behavior), not on
      future events. Formally, we say that the [ReadinessModel] is
      non-clairvoyant if a job's readiness at a given time does not vary across
      schedules with identical prefixes. That is, given two schedules [sched]
      and [sched'], the predicates [job_ready sched j t] and [job_ready sched'
      j t] may not differ if [sched] and [sched'] are identical prior to time
      [t]. *)
  Definition nonclairvoyant_readiness :=
    forall sched sched' j h,
      identical_prefix sched sched' h ->
      forall t,
        t <= h ->
        job_ready sched j t = job_ready sched' j t.

  (** Next, we relate the readiness model to the preemption model. *)
  Context `{JobPreemptable Job}.

  (** In a preemption-policy-compliant schedule, nonpreemptive jobs must remain
      scheduled. Further, in a valid schedule, scheduled jobs must be
      ready. Consequently, in a valid preemption-policy-compliant schedule, a
      nonpreemptive job must remain ready until at least the end of its
      nonpreemptive section. *)
  Definition valid_nonpreemptive_readiness sched :=
     forall j t,
       ~~ job_preemptable j (service sched j t)
       -> job_ready sched j t.

  (** For the next definition, consider the tasks from which the jobs stem. *)
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** We say a readiness model is sequential iff only a task's earliest
      incomplete job is ready, meaning that later jobs can be executed only
      after all earlier jobs have been completed. *)
  Definition sequential_readiness (arr_seq : arrival_sequence Job) :=
    forall sched j t,
      job_ready sched j t -> prior_jobs_complete arr_seq sched j t.

  (** Finally, consider a JLFP policy that indicates a higher-or-equal
      priority relation. *)
  Context `{JLFP_policy Job}.

(** We introduce a property of readiness models called _work-bearing readiness_,
    which extracts the useful property of the classic readiness model stating
    that, if there is some job _pending_ at a time instant [t], then there also
    exists a job that is _ready_ at time [t]. In other words, we say that a
    readiness model is work-bearing if for every job [j] that is pending but not
    ready at some instant [t], there exists a job with higher or equal priority
    [j_hp] that is both pending _and_ ready at time [t]. *)
  Definition work_bearing_readiness
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :=
    forall (j : Job) (t : instant),
      arrives_in arr_seq j ->
      pending sched j t ->
      exists j_hp,
        arrives_in arr_seq j_hp
        /\ job_ready sched j_hp t
        /\ hep_job j_hp j.

End ReadinessModelProperties.
