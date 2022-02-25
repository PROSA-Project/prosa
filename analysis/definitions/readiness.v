Require Export prosa.behavior.ready.
Require Export prosa.analysis.definitions.schedule_prefix.
Require Export prosa.model.preemption.parameter.
Require Export prosa.model.priority.classes.

(** * Properties of Readiness Models *)

(** In this file, we define commonsense properties of readiness models. *)
Section ReadinessModelProperties.
  
  (** For any type of jobs with costs and arrival times ... *)
  Context {Job : JobType} `{JobCost Job} `{JobArrival Job}.

  (** ... and any kind of processor model, ... *)
  Context {PState: ProcessorState Job}.

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
  Definition valid_nonpreemptive_readiness :=
     forall sched j t,
        ~~ job_preemptable j (service sched j t) -> job_ready sched j t.
  
End ReadinessModelProperties.
