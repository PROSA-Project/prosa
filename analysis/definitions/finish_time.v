Require Export prosa.behavior.service.

(** * Finish Time of a Job *)

(** In this file, we define a job's precise finish time.

    Note that in general a job's finish time may not be defined: if a job never
    finishes in a given schedule, it does not have a finish time. To get around
    this, we define a job's finish time under the assumption that _some_ (not
    necessarily tight) response-time bound [R] is known for the job.

    Under this assumption, we can simply re-use ssreflect's existing [ex_minn]
    search mechanism (for finding the minimum natural number satisfying a given
    predicate given a witness that some natural number satisfies the predicate)
    and benefit from the existing corresponding lemmas. This file briefly
    illustrates how this can be done. *)

Section JobFinishTime.

  (** Consider any type of jobs with arrival times and costs ... *)
  Context {Job : JobType} `{JobArrival Job} `{JobCost Job}.

  (** ... and any schedule of such jobs. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** Consider an arbitrary job [j]. *)
  Variable j : Job.

  (** In the following, we proceed under the assumption that [j] finishes
      eventually (i.e., no later than [R] time units after its arrival, for any
      finite [R]). *)
  Variable R : nat.
  Hypothesis H_response_time_bounded : job_response_time_bound sched j R.

  (** For technical reasons, we restate the response-time assumption explicitly
      as an existentially quantified variable. *)
  #[local] Corollary job_finishes : exists t, completed_by sched j t.
  Proof. by exists (job_arrival j + R); exact: H_response_time_bounded. Qed.

  (** We are now ready for the main definition: job [j]'s finish time is the
      earliest time [t] such that [completed_by sched j t] holds. This time can
      be computed with ssreflect's [ex_minn] utility function, which is
      convenient because then we can reuse the corresponding lemmas. *)
  Definition finish_time : instant := ex_minn job_finishes.

  (** In the following, we demonstrate the reuse of [ex_minn] properties by
      establishing three natural properties of a job's finish time. *)

  (** First, a job is indeed complete at its finish time. *)
  Corollary finished_at_finish_time : completed_by sched j finish_time.
  Proof.
    rewrite /finish_time/ex_minn.
    by case: find_ex_minn.
  Qed.

  (** Second, a job's finish time is the earliest time that it is complete. *)
  Corollary earliest_finish_time :
    forall t,
      completed_by sched j t ->
      finish_time <= t.
  Proof.
    move=> t COMP.
    rewrite /finish_time/ex_minn.
    by case: find_ex_minn.
  Qed.

  (** Third, Prosa's notion of [completes_at] is satisfied at the finish time. *)
  Corollary completes_at_finish_time :
    completes_at sched j finish_time.
  Proof.
    apply/andP; split; last exact: finished_at_finish_time.
    apply/orP; case FIN: finish_time; [by right|left].
    apply: contra_ltnN => [?|];
      first by apply: earliest_finish_time.
    by lia.
  Qed.

  (** Finally, we can define a job's precise response time as usual as the time
      from its arrival until its finish time. *)
  Definition response_time : duration := finish_time - job_arrival j.

End JobFinishTime.
