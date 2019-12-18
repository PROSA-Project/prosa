Require Export prosa.behavior.all.
Require Export prosa.analysis.definitions.progress.
Require Export prosa.util.nat.

(** * Job Model Parameter for Jobs Exhibiting Self-Suspensions *)

(** We define a job's self-suspension parameter as follows: after having
    received a given number of units of service [rho], a job [j] may either
    self-suspend for a given duration [d], in which case [job_suspension j rho
    = d], or it may remain ready, in which case [job_suspension j rho =
    0]. Note that a job may self-suspend before having received any service,
    which is equivalent to release jitter. (Suspensions after a job has
    completed are meaningless and irrelevant.) *)
Class JobSuspension (Job : JobType) := job_suspension : Job -> work -> duration.

(** * Readiness of Self-Suspending Jobs *)

(** In the following section, we define the notion of "readiness" for
    self-suspending jobs based on the just-defined job-model parameter. *)
Section ReadinessOfSelfSuspendingJobs.
  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ... and any kind of processor state. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Suppose jobs have an arrival time, a cost, and that they exhibit
      self-suspensions. *)
  Context `{JobArrival Job} `{JobCost Job} `{JobSuspension Job}.

  (** We say that a job's last suspension (if any) of length [delay] "has
      passed" at a given time [t] (i.e., the job is ready again at time [t]) if
      the job arrived at least [delay] time units ago and has not progressed
      within the last [delay] time units. In other words, since a
      self-suspension can start only when a job progresses (i.e., when it
      receives some service), if a job has not been making progress in the last
      [delay] time units, then a self-suspension of length [delay] has
      necessarily ended at time [t]. *)
  Definition suspension_has_passed (sched : schedule PState) (j : Job) (t : instant) :=
    let delay := job_suspension j (service sched j t) in
    (job_arrival j + delay <= t) && no_progress_for sched j t delay.

  (** Based on [suspension_has_passed], we state the notion of readiness for
      self-suspending jobs: a job [t] is ready at time [t] in a schedule
      [sched] only if it is not self-suspended or complete at time [t]. *)
  Global Program Instance suspension_ready_instance : JobReady Job PState :=
    {
      job_ready sched j t := suspension_has_passed sched j t && ~~ completed_by sched j t
    }.
  Next Obligation.
    move: H3 => /andP [PASSED UNFINISHED].
    rewrite /pending. apply /andP. split => //.
    move: PASSED. rewrite /suspension_has_passed /has_arrived => /andP [ARR _].
    by move: ARR; apply leq_addk.
  Defined.

End ReadinessOfSelfSuspendingJobs.


(** * Total Suspension Time of a Job *)

(** Next, we define the notion of a job's cumulative and total suspension times. *)

Section TotalSuspensionTime.

  (** Consider any kind of jobs... *)
  Context {Job : JobType}.

  (** ...where each job has a cost and may exhibit self-suspensions. *)
  Context `{JobCost Job} `{JobSuspension Job}.

  (** A job's total self-suspension length is simply the sum of the lengths of
     all its suspensions. *)
  Definition total_suspension (j : Job) := \sum_(0 <= ρ < job_cost j) job_suspension j ρ.

End TotalSuspensionTime.
