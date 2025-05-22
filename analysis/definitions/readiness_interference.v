Require Export prosa.model.priority.definitions.
Require Export prosa.analysis.abstract.definitions.

(** Readiness Interference *)

(** In this file, we define the notion of interference due to none of the
    higher or equal priority jobs being ready. The motivation behind having
    such a definition is :
    1) It helps us to handle readiness models where a job may become not ready
       in between its arrival and completion. e.g. self-suspensions. Note that
       another job may be still be executed at this executed at this instance.
       Thus, the below point.
    2) It helps us to handle instances where a job is facing interference
       specifically due to the job being not ready, and separate from
       [another_hep_job_interference] and [service_inversion]. *)

Section Definitions.
  (** Consider any kind of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any notion of readiness.
      Note that although any notion of readiness would work, it wouldn't make
      sense to have this kind of interference in case of readiness model where
      [work_bearing_readiness] is true, since this interference would always
      be false in that case. *)
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

  (** Recall the definition of abstract quiet time. *)
  Let quiet_time_ab := quiet_time sched.

  (** Now we define the required bound as, for any job [j ∈ tsk] and any interval <<[t1, t1 + Δ)>>
      that starts with a quiet time (w.r.t. job [j]), [B : duration] is a bound
      on the total interference due to no higher-or-equal priority jobs being
      ready in any interval <<[t1, t1 + Δ)>>. *)
  Definition readiness_interference_is_bounded (B : duration) :=
    forall j t1 Δ,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      quiet_time_ab j t1  ->
      cumulative_readiness_interference arr_seq sched j t1 (t1 + Δ) <= B.

End Bound.
