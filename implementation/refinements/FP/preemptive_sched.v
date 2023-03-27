Require Export prosa.analysis.facts.preemption.task.preemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.preemptive.
Require Export prosa.analysis.facts.readiness.sequential.
Require Export prosa.analysis.definitions.tardiness.
Require Export prosa.implementation.facts.ideal_uni.prio_aware.
Require Export prosa.implementation.definitions.task.

(** ** Fully-Preemptive Fixed-Priority Schedules  *)

(** In this section, we prove that the fully-preemptive preemption policy
    under fixed-priority schedules is valid, and that the scheduling policy is
    respected at each preemption point.

    This file does not contain novel facts; it is used to uniform POET's certificates
    and minimize their verbosity. *)
Section Schedule.

  (** In this file, we adopt the Prosa standard implementation of jobs and tasks. *)
  Definition Task := [eqType of concrete_task].
  Definition Job := [eqType of concrete_job].

  (** Consider any valid arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... assume sequential readiness, ... *)
  Instance sequential_ready_instance : JobReady Job (ideal.processor_state Job) :=
    sequential_ready_instance arr_seq.

  (** ... and consider any fully-preemptive, fixed-priority schedule. *)
  #[local] Existing Instance fully_preemptive_job_model.
  #[local] Existing Instance NumericFPAscending.
  Definition sched := uni_schedule arr_seq.

  (** First, we remark that such a schedule is valid. *)
  Remark sched_valid :
    valid_schedule sched arr_seq.
  Proof.
    apply uni_schedule_valid => //.
    by apply sequential_readiness_nonclairvoyance.
  Qed.

  (** Finally, we show that the fixed-priority policy is respected at each preemption point. *)
  Lemma respects_policy_at_preemption_point :
    respects_FP_policy_at_preemption_point arr_seq sched (NumericFPAscending Task).
  Proof.
    apply schedule_respects_policy => //; rt_eauto.
    by apply sequential_readiness_nonclairvoyance.
  Qed.

End Schedule.
