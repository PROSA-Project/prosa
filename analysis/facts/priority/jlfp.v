Require Export prosa.analysis.facts.behavior.arrivals.
Require Export prosa.model.readiness.basic.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.model.schedule.work_conserving.

(** * Selecting a Highest-Priority Job *)

(** We establish when priority compliance forces a pending job to execute. *)
Section JLFPSelection.

  (** Consider jobs with arrival times and execution costs. *)
  Context {Job : JobType} `{JobArrival Job} `{JobCost Job}.

  (** Allow any processor model ... *)
  Context {PState : ProcessorState Job}.

  (** ... and any preemption model. *)
  Context `{JobPreemptable Job}.

  (** We restrict the focus to basic readiness models. *)
  Context {job_ready_model : JobReady Job PState}.
  Hypothesis H_basic_readiness : basic_readiness job_ready_model.

  (** Given an arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... consider a work-conserving schedule of the arriving jobs. *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** A fixed job order governs scheduling decisions ... *)
  Context {JLFP : JLFP_policy Job}.

  (** ... and the schedule honors this order at preemption times. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Resolving ties uniquely makes the choice among eligible jobs deterministic. *)
  Hypothesis H_priority_antisymmetric :
    antisymmetric_job_priorities JLFP arr_seq.

  (** To establish that a pending job is selected, it suffices to compare
      it with whichever job actually executes. If [j] is waiting, work
      conservation supplies an executing job [j']. At a preemption time,
      priority compliance gives [hep_job j' j], while the final premise
      asks the caller to establish the reverse comparison. Antisymmetry
      then identifies the two jobs. The case where [j] already executes
      is immediate, so the premise only addresses distinct competing jobs. *)
  Lemma jlfp_pending_highest_priority_job_is_scheduled :
    forall t j,
      preemption_time arr_seq sched t ->
      arrives_in arr_seq j ->
      pending sched j t ->
      (forall j', scheduled_at sched j' t -> j' != j -> hep_job j j') ->
      scheduled_at sched j t.
  Proof.
    move=> t j PT ARR PEND HIGHEST.
    case: (boolP (scheduled_at sched j t)) => // NSCHED.
    have BACK : backlogged sched j t
      by rewrite /backlogged H_basic_readiness PEND NSCHED.
    have [j' SCHED] := H_work_conserving j t ARR BACK.
    suff EQ : j = j' by move: NSCHED; rewrite EQ SCHED.
    apply: H_priority_antisymmetric => //.
    - apply: HIGHEST => //.
      apply/eqP => EQ; by move: NSCHED; rewrite -EQ SCHED.
    - exact: H_respects_policy.
  Qed.

End JLFPSelection.
