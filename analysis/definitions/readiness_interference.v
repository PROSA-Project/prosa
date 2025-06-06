Require Export prosa.model.priority.definitions.
Require Export prosa.analysis.abstract.definitions.
Require Export prosa.analysis.definitions.job_properties.

(** Readiness Interference *)

(** In this file, we define the interference incurred by a job due to the
    fact that the job may become non-ready before its completion.

    We model this interference as an instant when all of the higher-or-equal-priority
    jobs (w.r.t the job under analysis) becomes non-ready. Such an instant may occur due to,
    1) All of the pending jobs becoming non-ready, so the processor is in idle state.
    2) A lower priority job is scheduled, but no priority inversion is taking place.

    The motivation behind such a definition is to have the interference due to non-readiness
    exclusive of other interference factors like priority inversion, and interference due
    to other higher-or-equal-priority jobs. *)

Section Definitions.
  (** Consider any kind of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any notion of readiness.
      Note that although any notion of readiness would work, it wouldn't make
      sense to have this kind of interference in case of a work-bearing notion of
      readiness, since this interference would always be false in that case. *)
  Context `{!JobReady Job PState}.

  (** Consider any arrival sequence of jobs. *)
  Variable arr_seq : arrival_sequence Job.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** Consider any JLFP priority policy. *)
  Context {JLFP : JLFP_policy Job}.

  (** Now consider any job [j]. *)
  Variable j : Job.

  (** Now we define interference due to no higher or equal priority jobs being ready. *)
  Definition no_hep_ready (t : instant) :=
    all (fun j' => ~~ job_ready sched j' t)
      [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j].

  (** Using the above definition we define cumulative interference due to
      no higher or equal priority jobs being ready in an interval. *)
  Definition cumulative_readiness_interference (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) no_hep_ready t.

End Definitions.

(** In this section, we define the notion of a bound on the total
   interference due to no higher or equal priority being ready in an interval. *)
Section Bound.
  (** Consider any tasks. *)
  Context {Task : TaskType}.

  (** Consider any jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobTask Job Task}.

  (** Consider any processor model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any notion of readiness. *)
  Context `{!JobReady Job PState}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Consider any JLFP priority policy. *)
  Context {JLFP : JLFP_policy Job}.

  (** Assume that we have some definition of [Interference] and [InterferingWorkload]. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Now consider a task [tsk]. *)
  Variable tsk : Task.

  (** Recall the notion of abstract busy interval prefix. *)
  Let busy_interval_prefix_ab := busy_interval_prefix sched.

  (** Now we define the required bound as, for any job [j ∈ tsk] and any interval <<[t1, t1 + Δ)>>
      that is inside the busy interval <<[t1, t2]>> of [j], [B : duration] is a bound
      on the total interference due to no higher-or-equal priority jobs being
      ready in the interval <<[t1, t1 + Δ)>>. *)
  Definition readiness_interference_is_bounded (B : duration -> duration -> duration) :=
    forall j t1 t2 Δ,
      t1 + Δ <= t2 ->
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      job_cost_positive j ->
      busy_interval_prefix_ab j t1 t2 ->
      cumulative_readiness_interference arr_seq sched j t1 (t1 + Δ) <= B (job_arrival j - t1) Δ.

End Bound.
