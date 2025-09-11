(** * Connecting the General Result to the Model in the Paper *)

(** In the following, we instantiate the general transfer schedulability result
    for a system model that more closely resembles the system model defined in
    the paper by Willemsen et al. (EMSOFT

    2025#, <a
    href="https://doi.org/10.1145/3763236">DOI: 10.1145/3763236</a>#).
    In particular, we explicitly introduce the notion of system evolutions,
    which are usually left implicit in Prosa. *)


Require Export prosa.util.all.
Require Export prosa.analysis.definitions.finish_time.
Require Export prosa.results.transfer_schedulability.criterion.


(** * Elements of the EMSOFT'25 System Model *)

(** We first define the key notions that refine the model in the paper relative
    to the more abstract one in the main proof of transfer schedulability:

    - job precedence and delay constraints,

    - system evolutions, and

    - a notion of schedulers. *)

(** ** Precedence and Delay *)

(** We introduce a readiness model that matches the model assumed in the paper:
    jobs have predecessors and may be scheduled (i.e., become ready) only after
    a predecessor-dependent delay has passed. *)

(** *** Job Parameters *)

(** We introduce two new job parameters that model, for each job, the set of
    predecessors and the associated delays. *)

(** The list of a job [j]'s predecessors is given by [job_predecessors j]. *)

Class JobPredecessors (Job : JobType) := { job_predecessors : Job -> seq Job }.

(** The delay that must pass between when a job [j] is first scheduled and the
    completion of a predecessor [j'] is given by [job_delay j j']. *)

Class JobDelay (Job : JobType) := { job_delay : Job -> Job -> duration }.

(** *** Definition of Job Readiness *)

(** Based on the above two job parameters, we can precisely define the assumed
    precedence constraints in terms of a readiness model, which is a standard
    Prosa interface. *)

Section DelayedPrecedenceReadiness.

  (** Consider any kind of jobs... *)

  Context {Job : JobType}.

  (** ... and any kind of processor state. *)

  Context {PState : ProcessorState Job}.

  (** Suppose jobs have an arrival time, a cost, a set of predecessors, and
      predecessor-specific release delays. *)

  Context `{JobArrival Job} `{JobCost Job} `{JobPredecessors Job} `{JobDelay Job}.

  (** For a given predecessor [j_pred] of a job [j], we say the delay has passed
      at time [t] if [j_pred] completed at least [job_delay j j_pred] time units
      earlier. *)

  Let delay_has_passed sched j t j_pred :=
    let
      delta := job_delay j j_pred
    in
      (t >= delta) && completed_by sched j_pred (t - delta).

  (** We say that a job [j] is _released_ at a time [t] after its arrival if the
      delay has passed w.r.t. each predecessor. *)

  Let is_released sched j t :=
    (job_arrival j <= t)
    && all (delay_has_passed sched j t) (job_predecessors j).

  (** A job [j] is hence _ready_ to be scheduled at time [t] if and only if it
      is released and not yet complete. *)

  #[local,program] Instance delayed_precedence_ready_instance : JobReady Job PState :=
  {
    job_ready sched j t := is_released sched j t && ~~ completed_by sched j t
  }.
  Next Obligation.
    move=> sched j t /andP[/andP[ARR _] UNFINISHED].
    by apply /andP; split.
  Qed.

End DelayedPrecedenceReadiness.

(** ** System Evolutions *)

(** Next, we introduce the notion of system evolutions that determine each job's
    cost and delay parameters. *)

(** Given an arbitrary type of evolutions [Omega], ... *)

Class SystemEvolutions (Omega : Type) (Job : JobType) := {

    (** ... the job costs in an evolution [omega : Omega] are given by
        [evo_costs omega] and ... *)

    evo_costs : Omega -> JobCost Job;

    (** ... the delays are given by [evo_delays omega]. *)

    evo_delays : Omega -> JobDelay Job;

  }.


(** ** Scheduler Interface *)

(** Finally, we introduce the notion of a scheduling algorithm. *)

Section SchedulerDef.

  (** Allowing for any type of system evolutions [Omega], ... *)

  Variable Omega : Type.

  (** ... any kind of jobs, ... *)

  Variable Job : JobType.

  (** ... and any kind of processor model, ... *)

  Context {PState : ProcessorState Job}.

  (** ... a scheduler is a function that, given each job's arrival time,
      predecessors, and an evolution [omega], yields a schedule of the jobs. *)

  Definition Scheduler
    `{JobArrival Job} `{JobPredecessors} `{SystemEvolutions Omega}
    := Omega -> schedule PState.

End SchedulerDef.

(** * Instantiation of the EMSOFT'25 System Model *)

(** With all basic elements defined, we can state the transfer schedulability
    results in terms of the system model assumed in the paper. *)

Section EMSOFTModel.

  (** ** The Set of Jobs *)

  (** We consider jobs described by _evolution-independent_ arrival times and
      predecessor sets, ... *)

  Context {Job : JobType} `{JobArrival Job} `{JobPredecessors Job}.

  (** ... which arrive according to the arrival sequence [arr_seq]. *)

  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ** Ideal Uniprocessor Assumption *)

  (** We consider ideal uniprocessor schedules. *)

  #[local] Existing Instance ideal.processor_state.
  Let PState := ideal.processor_state Job.

  (** ** System Evolutions *)

  (** Let [Omega] denote the set of all system evolutions. *)

  Variable Omega : Type.
  Context `{SystemEvolutions Omega Job}.

  (** For clarity, we introduce the following abbreviations: *)

  (** - [job_cost omega j] denotes the cost of job [j] in evolution [omega]. *)

  Let job_cost omega := @job_cost _ (evo_costs omega).

  (** - [job_delay omega j j'] denotes the delay between jobs [j] and its
        predecessor [j'] in evolution [omega]. *)

  Let job_delay omega := @job_delay _ (evo_delays omega).

  (** - [job_ready omega] denotes the readiness model resulting from
        [job_delay omega] and the evolution-invariant predecessor sets. *)

  Let job_ready (omega : Omega) : JobReady Job PState :=
    @delayed_precedence_ready_instance _ _ _  (evo_costs omega) _ (evo_delays omega).

  (** ** Worst-Case Reference Evolution *)

  (** Let [omega_0] denote the system evolution with maximal parameters, ... *)

  Variable omega_0 : Omega.

  (** ... that is, the job costs in [omega_0] upper-bound the costs in any other
      evolution, ... *)

  Hypothesis H_max_cost :
    forall omega j,
      job_cost omega j <= job_cost omega_0 j.

  (** ... and the delays in [omega_0] similarly upper-bound the delays in any
      other evolution. *)

  Hypothesis H_max_delay :
    forall omega j j',
      job_delay omega j j'  <= job_delay omega_0 j j'.

  (** ** The Schedulers *)

  (** Suppose we are given two scheduling algorithms [algA] and [algB]. *)

  Variable algA algB : Scheduler Omega Job.

  (** As discussed in the paper, we restrict our attention to schedulers that
      always produce well-formed schedules. *)

  Hypothesis H_well_formed_A :
    @valid_schedule _ _ (algA omega_0) (job_cost omega_0) _  (job_ready omega_0) arr_seq.
  Hypothesis H_well_formed_B :
    forall omega, @valid_schedule _ _ (algB omega) (job_cost omega) _  (job_ready omega) arr_seq.


  (** For brevity, recall the notion of [schedulability_transferred]. We
      specialize the definition such that [algA omega_0] is the reference
      schedule and [algB omega] the online schedule. *)

  Definition schedulability_transferred_AB omega :=
    schedulability_transferred
      (algA omega_0) (algB omega) (job_cost omega_0) (job_cost omega).

  (** ** Clairvoyant Results *)

  (** We are now ready to state the results pertaining to clairvoyant scheduling
      algorithms. *)

  (** First, recall the [transfer_schedulability_criterion] as applied to
      clairvoyant schedulers. *)

  Definition clairvoyant_criterion :=

    (** For any evolution [omega], the criterion is assumed to hold ... *)

    (forall omega, transfer_schedulability_criterion

                (** ... for the reference schedule [algA omega_0] and the online
                    schedule [algB omega] ... *)

                (algA omega_0)     (algB omega)

                (** ... w.r.t. the respective job costs ... *)

                (job_cost omega_0) (job_cost omega)

                (** ... for the given, fixed job arrival times ... *)

                arr_seq

                (** with regard to online job costs. This last parameter is the
                    "clairvoyant" part. *)

                (job_cost omega)).


  (** The above clairvoyant criterion ensures that schedulability is transferred
      in every evolution. *)

  Theorem clairvoyant_sufficiency :
    clairvoyant_criterion ->
    forall omega, schedulability_transferred_AB omega.
  Proof.
    by move=> ? ?; apply: online_transfer_schedulability_criterion_sufficiency.
  Qed.

  (** Conversely, the fact that schedulability is transferred in every evolution
      implies that the above criterion holds. *)

  Theorem clairvoyant_necessity :
    (forall omega, schedulability_transferred_AB omega) ->
    clairvoyant_criterion.
  Proof.
    rewrite /schedulability_transferred_AB => TRANS omega.
    by apply: online_transfer_schedulability_criterion_necessity.
  Qed.


  (** ** Non-Clairvoyant Result *)

  (** Finally, we state the sufficiency result for non-clairvoyant schedulers. *)

  (** As above, we recall the transfer schedulability criterion, this time
      instantiated for reference costs [job_cost omega_0] (again, note the last
      parameter). *)

  Definition nonclairvoyant_criterion :=
    forall omega,
        transfer_schedulability_criterion
          (algA omega_0)     (algB omega)
          (job_cost omega_0) (job_cost omega)
          arr_seq
          (job_cost omega_0).

  (** Assuming the above criterion holds, schedulability is transferred in all
      evolutions. *)

  Theorem nonclairvoyant_sufficiency :
    nonclairvoyant_criterion ->
    forall omega, schedulability_transferred_AB omega.
  Proof.
    by move=> CRIT omega; apply: ref_transfer_schedulability_criterion_sufficiency.
  Qed.


  (** * Results w.r.t. Finish Times *)

  (** The results stated above are stated w.r.t. Prosa's standard [completed_by]
      predicate, which tests whether or not a job is finished at a given time
      (and in a given schedule) by comparing the total amount of service
      received so far with the job's cost.

      The advantage of Prosa's [completed_by] predicate is that it is always
      applicable, even if some jobs never finish (i.e., are starved). It does
      not, however, yield the job's finish time, which is the earliest time at
      which the [completed_by] predicate holds, and which consequently is
      defined only in starvation-free schedules. *)

  (** In the following, we re-state the above theorems in terms of finish times
      under the strengthened assumption that we are indeed looking at
      starvation-free schedules.

      We begin with the two sufficiency theorems. *)


  (** ** Non-Starvation Assumption *)

  (** For convenience, to match Prosa's existing definitions, we state the
      non-starvation assumption in terms of the existence of _some_ finite
      response-time bound for every job in the arrival sequence.

      First, we assume non-starvation only for the reference schedule

      [algA
      omega_0]. The following notation means that there exists a
      bound [R] for each job [j] in the arrival sequence such that [j] completes
      within [R] time units of its arrival (in the reference schedule). *)

  Hypothesis H_non_starvation :
    forall j,
      arrives_in arr_seq j ->
      { R : duration |
        @job_response_time_bound _ _ (algA omega_0) (job_cost omega_0) _  j R }.

  (** ** Definition of Finish Times *)

  (** With the non-starvation assumption in place, we can start reasoning about
      finish times. Let us recall the relevant definitions from Prosa. *)

  Section FinishTimes.

    (** In the context of a given evolution [omega] ... *)

    Variable omega : Omega.

    (** ... and for a given, _certainly finishing_ job [jf] that is part of the
        arrival sequence [arr_seq], ... *)

    Variable jf : Job.
    Hypothesis H_arrives : arrives_in arr_seq jf.

    (** ... we exploit the non-starvation assumption ... *)

    Let R := proj1_sig (H_non_starvation jf H_arrives).
    Let ref_response_time_bound := proj2_sig (H_non_starvation jf H_arrives).

    (** ... to define [jf]'s finish time in the reference schedule
        [algA omega_0]. *)

    Definition ref_finish_time : instant :=
      finish_time _ _ _ ref_response_time_bound.

    (** To define the finish time in the online schedule, we need to put in a
        little more legwork, since the non-starvation assumption above applies
        only to the reference schedule, but not to the online schedule. To this
        end, assume that schedulability is transferred from [algA omega_0] to
        [algB omega]. *)

    Hypothesis H_trans : schedulability_transferred_AB omega.

    (** Under this assumption, [R] is of course also a response-time bound
        w.r.t. the online schedule. *)

    Lemma online_response_time_bound :
      @job_response_time_bound _ _ (algB omega) (job_cost omega) _  jf R.
    Proof. by apply/H_trans/ref_response_time_bound. Qed.

    (** Having established that the online schedule is starvation-free, too, we
        can recall the finish time in [algB omega], too. *)

    Definition online_finish_time : instant :=
      finish_time _ _ _ online_response_time_bound.

    (** With the finish times in place for both schedules, we can state the
        property that we're after: the finish time in the online schedule is no
        later than in the reference schedule. *)

    Definition online_finish_time_bounded :=
      online_finish_time <= ref_finish_time.

  End FinishTimes.

  (** ** Clairvoyant Sufficiency Result for Finish Times *)

  (** With the above setup in place, we can easily re-state the
      [clairvoyant_sufficiency] theorem in terms of finish times. *)

  Section SufficientFinishTimesClairvoyant.

    (** Under the assumption that the schedulability transfer criterion holds
        w.r.t. _online_ job costs, ... *)

    Hypothesis H_criterion : clairvoyant_criterion.

    (** ... the finish time of any job (that is part of the arrival sequence) in
        any online schedule is no later than in the reference schedule. *)

    Theorem clairvoyant_sufficiency' :
      forall omega j (IN : arrives_in arr_seq j),
        online_finish_time_bounded omega j IN
          (clairvoyant_sufficiency H_criterion omega).
    Proof.
      move=> omega j IN.
      by apply/earliest_finish_time/clairvoyant_sufficiency/finished_at_finish_time.
    Qed.

  End SufficientFinishTimesClairvoyant.

  (** Before moving on to the necessity argument for the clairvoyant case, which
      will require further assumptions and legwork, we first quickly dispatch
      the sufficiency argument in the case of non-clairvoyant schedulers. *)

  (** ** Non-Clairvoyant Sufficiency Result for Finish Times *)

  (** The sufficiency claim for non-clairvoyant schedulers follows virtually
      identically to the above theorem since the underlying argument is the
      same. *)

  Section SufficientFinishTimesNonclairvoyant.

    (** Under the assumption that the schedulability transfer criterion holds
        w.r.t. _reference_ job costs, ... *)

    Hypothesis H_criterion : nonclairvoyant_criterion.

    (** ... the finish time of any job (that is part of the arrival sequence) in
        any online schedule is no later than in the reference schedule. *)

    Theorem nonclairvoyant_sufficiency' :
      forall omega j (IN : arrives_in arr_seq j),
        online_finish_time_bounded omega j IN
          (nonclairvoyant_sufficiency H_criterion omega).
    Proof.
      move=> omega j IN.
      by apply/earliest_finish_time/nonclairvoyant_sufficiency/finished_at_finish_time.
    Qed.

  End SufficientFinishTimesNonclairvoyant.

  (** ** Clairvoyant Necessity Result for Finish Times *)

  (** For the necessity case, we need to strengthen our non-starvation
      assumption to also cover any online schedule. We again express this
      assumption in terms of the existence of a finite response-time bound for
      every job in all online schedules. *)

  Hypothesis H_non_starvation' :
    forall j,
      arrives_in arr_seq j ->
      forall omega,
        { R | @job_response_time_bound _ _ (algB omega) (job_cost omega) _  j R }.

  (** *** Online Finish Times, Revisited *)

  (** Based on the above non-starvation assumption, we can refer to the
      completion time in the online schedule directly. *)

  Section FinishTimes.

    (** In the context of a given evolution [omega] ... *)

    Variable omega : Omega.

    (** ... and for a given, certainly finishing job [jf] that is part of the
        arrival sequence [arr_seq], ... *)

    Variable jf : Job.
    Hypothesis H_arrives : arrives_in arr_seq jf.

    (** ... we exploit the non-starvation assumption ... *)

    Let online_response_time_bound :=
          proj2_sig (H_non_starvation' jf H_arrives omega).

    (** ... to define [j]'s finish time in the online schedule [algB omega]. *)

    Definition online_finish_time' : instant :=
      finish_time _ _ _ online_response_time_bound.

    (** Using this notion of [j]'s online finish time, we can re-state that it
        finishes no later in the online schedule than in the reference schedule. *)

    Definition online_finish_time_bounded' :=
      online_finish_time' <= ref_finish_time jf H_arrives.

  End FinishTimes.

  (** *** Clairvoyant Necessity Theorem *)

  (** Finally, we are in a position to state the necessity result w.r.t. finish
      times. *)

  Section NecessaryFinishTimesClairvoyant.

    (** Under the assumption that, for any job that arrives in the arrival
        sequence, the finish time in any online schedule is no later than in the
        reference schedule, ... *)

    Hypothesis H_bounded :
      forall omega j in_arrival_sequence,
        online_finish_time_bounded' omega j in_arrival_sequence.


    (** ... we can show that the transfer schedulability criterion w.r.t. online
        job costs holds. *)

    Theorem clairvoyant_necessity' : clairvoyant_criterion.
    Proof.
      apply: clairvoyant_necessity => omega.
      move=> j t COMP.
      have [ZERO|POS] := (posnP (job_cost omega_0 j)).
      { move: (H_max_cost omega j); rewrite ZERO leqn0 => /eqP ZERO'.
        by move: ZERO'; rewrite /job_cost /completed_by /job.job_cost => ->. }
      { have [t' [LT SCHED']] : exists t' : nat, t' < t /\ scheduled_at (algA omega_0) j t'.
        { apply: positive_service_implies_scheduled_before.
          by move: POS COMP; rewrite /completed_by/service/job.job_cost/job_cost; lia. }
        have IN : arrives_in arr_seq j by move: (H_well_formed_A) => [+ _]; apply.
        set RTB := proj2_sig (H_non_starvation' j IN omega).
        apply: completion_monotonic; last by apply/finished_at_finish_time/RTB.
        move: (H_bounded omega j IN); rewrite /online_finish_time_bounded'/online_finish_time' => BOUND.
        apply: (leq_trans BOUND).
        exact/earliest_finish_time/COMP. }
    Qed.

  End NecessaryFinishTimesClairvoyant.

End EMSOFTModel.
