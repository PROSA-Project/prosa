Require Export prosa.behavior.all.
Require Export prosa.model.processor.platform_properties.
Require Import prosa.analysis.facts.behavior.schedule.
Require Import prosa.analysis.facts.behavior.service.

(** * Multiprocessor State *)

(** In the following, we define a model of identical multiprocessors, i.e., of
    machines that comprise several identical cores. Each core is modeled by its
    own processor state and is required to be a uniprocessor, so that "core"
    and "processor" are synonymous throughout this file.

    The construction is generic in the type of the per-core state: any
    uniprocessor state (such as the ideal state) can be plugged into the generic
    multiprocessor construction below. (In fact, by combining it with
    variable-speed processors, one even obtains a so-called uniform
    multiprocessor model.)

    The uniprocessor requirement rules out nesting, i.e., using a multiprocessor
    state as a core to form a multiprocessor of multiprocessors. It is needed
    because this construction reports at most one scheduled job per core (see
    [multiproc_job_on] below): lossless when each core is a uniprocessor, but
    lossy for a core that is itself a multiprocessor, which could schedule
    several jobs at once. We impose the requirement below as the hypothesis
    [H_cores_are_uniprocessors]; lifting it is left to future work.

    NB: For now, the definition serves only to document how this can be done;
        it is not actually used anywhere in the library. *)

Section Schedule.

  (** Consider any types of jobs... *)
  Variable Job : JobType.

  (** ... and consider any type of per-core state. *)
  Variable core_state : ProcessorState Job.

  (** We formalize the restriction discussed above: each core is required to be
      a uniprocessor. *)
  Hypothesis H_cores_are_uniprocessors : uniprocessor_model core_state.

  (** Given a desired number of cores [num_cores], we define a finite
      type of integers from [0] to [num_cores - 1]. The purpose of this
      definition is to obtain a finite type (i.e., set of values) that can be
      enumerated in a terminating computation.

      Syntax hint: the ['I_] before [num_cores] is ssreflect syntax for the
      finite set of integers from zero to [num_cores - 1]. *)
  Let core_ids (num_cores : nat) := 'I_num_cores.

  (** Next, for any given number of cores [num_cores]... *)
  Variable num_cores : nat.

  (** ...we represent the type of the "multiprocessor state" as a function that
      maps core IDs (as defined by [core_ids num_cores], see above) to the
      given state on each core. *)
  Definition multiprocessor_state := core_ids num_cores -> core_state.

  (** Based on this notion of multiprocessor state, the job running on a
      specific core [c], according to the given multiprocessor state [mps], is
      the job scheduled in [(mps c)], the state of core [c], if any. By
      [H_cores_are_uniprocessors] there is at most one such job, so taking
      the head of the list of jobs scheduled in [(mps c)] loses no
      information. *)
  Definition multiproc_job_on (mps : multiprocessor_state) (c : core_ids num_cores)
      : option Job :=
    ohead (jobs_scheduled_in (mps c)).

  (** Whenever a job [j] is scheduled in [(mps c)], the state of core [c],
      [multiproc_job_on] reports it, i.e., returns [Some j]. By
      [H_cores_are_uniprocessors] at most one job is scheduled per core,
      so the head of [jobs_scheduled_in (mps c)] can only be [j].
      Although [H_cores_are_uniprocessors] is phrased in terms of schedules,
      it quantifies over <<all>> schedules, so the constant schedule
      [fun _=> mps c] recovers the fact for the single state [mps c]. *)
  Lemma scheduled_in_implies_job_on_eq :
    forall (mps : multiprocessor_state) (c : core_ids num_cores) (j : Job),
      scheduled_in j (mps c) ->
      multiproc_job_on mps c == Some j.
  Proof.
    move=> mps c j SCHED; rewrite /multiproc_job_on.
    case E: (jobs_scheduled_in (mps c)) => [|j' js].
    - by move: SCHED; rewrite jobs_scheduled_in_iff E.
    - have H_j' : scheduled_in j' (mps c) by rewrite jobs_scheduled_in_iff E mem_head.
      by rewrite (H_cores_are_uniprocessors j' j (fun _=> mps c) 0 H_j' SCHED).
  Qed.

  (** Similarly, the supply produced by a given multiprocessor state [mps] on a
      given core [c] is exactly the supply provided by [(mps c)]. *)
  Definition multiproc_supply_on
    (mps : multiprocessor_state) (c : core_ids num_cores)
    := supply_in (mps c).

  (** Next, the service received by a given job [j] in a given multiprocessor
      state [mps] on a given core [c] is exactly the service received by
      [j] in [(mps c)]. *)
  Definition multiproc_service_on
    (j : Job) (mps : multiprocessor_state) (c : core_ids num_cores)
    := service_in j (mps c).

  (** Finally, we connect the above definitions with the generic Prosa
      interface for processor models. *)
  #[local] Program Instance multiproc_state : ProcessorState Job :=
    {|
      State        := multiprocessor_state;
      job_on       := multiproc_job_on;
      supply_on    := multiproc_supply_on;
      service_on   := multiproc_service_on
    |}.
  Next Obligation.
    by move => ? ? ?; apply: leq_sum => c _; exact: service_on_le_supply_on.
  Qed.
  Next Obligation.
    move=> j mps c NJOB.
    rewrite /multiproc_service_on.
    apply: service_in_implies_scheduled_in.
    apply: contra NJOB.
    exact: scheduled_in_implies_job_on_eq.
  Qed.

  (** From the instance [multiproc_state], we get the function [service_in].
      The service received by a given job [j] in a given multiprocessor state
      [mps] is given by the sum of the service received across all individual cores
      of the multiprocessor. *)
  Lemma multiproc_service_in_eq :
    forall (j : Job) (mps : multiprocessor_state),
      service_in j mps = \sum_(c < num_cores) service_in j (mps c).
  Proof. reflexivity. Qed.

End Schedule.
