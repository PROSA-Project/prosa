Require Export prosa.analysis.facts.preemption.task.preemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.preemptive.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.definitions.tardiness.
Require Export prosa.implementation.facts.ideal_uni.prio_aware.
Require Export prosa.implementation.definitions.task.
Require Export prosa.model.priority.edf.

(** ** Fully-Preemptive Earliest-Deadline-First Schedules  *)

(** In this section, we prove that the fully-preemptive preemption policy
    under earliest-deadline-first schedules is valid, and that the scheduling policy is
    respected at each preemption point.

    This file does not contain novel facts; it is used to uniform POET's certificates
    and minimize their verbosity.  *)
Section Schedule.

  (** In this file, we adopt the Prosa standard implementation of jobs and tasks. *)
  Definition Task := concrete_task : eqType.
  Definition Job := concrete_job : eqType.

  (** Consider any valid arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... assume basic readiness, ... *)
  Instance basic_ready_instance : JobReady Job (ideal.processor_state Job) :=
    basic.basic_ready_instance.

  (** ... and consider any fully-preemptive, earliest-deadline-first schedule. *)
  #[local] Existing Instance fully_preemptive_job_model.
  #[local] Existing Instance EDF.
  Definition sched := uni_schedule arr_seq.

  (** First, we remark that such a schedule is valid. *)
  Remark sched_valid :
    valid_schedule sched arr_seq.
  Proof.
    apply uni_schedule_valid => //.
    by apply basic_readiness_nonclairvoyance.
  Qed.

  (** Finally, we show that the fixed-priority policy is respected at each preemption point. *)
  Lemma respects_policy_at_preemption_point_edf_fp :
    respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).
  Proof.
    apply schedule_respects_policy => //; auto with basic_rt_facts.
    by apply basic_readiness_nonclairvoyance.
  Qed.

End Schedule.
