From mathcomp Require Import eqtype ssrnat seq path fintype bigop.
Require Export prosa.util.int.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.model.priority.gel.
Require Export prosa.model.priority.elf.

(** * Generality of ELF *)

(** In the following, we make some formal remarks on the obvious generality of
    ELF w.r.t. Fixed Priority and GEL. *)

(** We begin with the general setup. *)
Section GeneralityOfELF.

  (** Consider any type of tasks with relative priority points,...*)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ...jobs of these tasks, and ... *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task}.

  (** ... any processor model. *)
  Context {PState : ProcessorState Job}.

  (** Suppose the jobs have arrival times and costs, and allow for any preemption
      and readiness models. *)
  Context {Arrival : JobArrival Job} {Cost : JobCost Job}
    `{JobPreemptable Job} {JR: @JobReady Job PState Cost Arrival}.

  (** Suppose [fp] is the fixed-priority policy that parameterizes the ELF policy. *)
  Variable fp: FP_policy Task.

  (** ** ELF Generalizes Fixed-Priority Scheduling *)

  (** First, let us consider fixed-priority scheduling, which by design
      ELF trivially generalizes. *)

  Section ELFGeneralizesFixedPriority.

    (** If each task has a distinct priority, or equivalently, no two tasks
        have equal priority according to the [fp] fixed-priority policy,... *)
    Hypothesis H_FP_policy_is_distinct:
      forall tsk1 tsk2, ~~ ep_task tsk1 tsk2.

    (** ... then the ELF policy reduces to the underlying FP policy. *)
    Remark elf_generalizes_fixed_priority :
      forall sched arr_seq,
        respects_JLFP_policy_at_preemption_point arr_seq sched (ELF fp)
        <-> respects_FP_policy_at_preemption_point arr_seq sched fp.
    Proof.
      move=> sched arr_seq; split => RESPECTED j j' t ARR PT BL SCHED;
        rewrite /hep_job_at /FP_to_JLFP /JLFP_to_JLDP /hep_job.
      - move: (RESPECTED j j' t ARR PT BL SCHED);
          rewrite /hep_job_at /JLFP_to_JLDP /ELF /hep_job
          => /orP[/andP[HEP NOTHEP] //| /andP[HEP GEL] //].
      rewrite /ELF; apply /orP; left.
      move: (RESPECTED j j' t ARR PT BL SCHED);
        rewrite /hep_job_at /FP_to_JLFP /JLFP_to_JLDP /hep_job => HEP.
      specialize (H_FP_policy_is_distinct (job_task j) (job_task j')).
      move: H_FP_policy_is_distinct;
        rewrite /ep_task negb_and => /orP[NOTHEP| NOTHEP].
      - by apply /andP; split.
      - case: (negP NOTHEP HEP).
    Qed.

  End ELFGeneralizesFixedPriority.

  (** ** ELF Generalizes GEL *)

  (** ELF similarly generalizes GEL in a trivial manner. *)
  Section ELFGeneralizesGEL.

  (** If the [fp] fixed-priority policy assigns equal priority to all tasks... *)
  Hypothesis H_FP_policy_is_same:
    forall tsk1 tsk2, ep_task tsk1 tsk2.

  (** ... then the ELF policy reduces to GEL. *)
  Remark elf_generalizes_gel:
    forall sched arr_seq,
      respects_JLFP_policy_at_preemption_point arr_seq sched (ELF fp)
      <-> respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task).
  Proof.
    move=> sched arr_seq; split => RESPECTED j j' t ARR PT BL SCHED;
      rewrite /hep_job_at /JLFP_to_JLDP /hep_job;
      specialize (H_FP_policy_is_same (job_task j) (job_task j')).
    { move: (RESPECTED j j' t ARR PT BL SCHED);
        rewrite /hep_job_at /JLFP_to_JLDP /ELF /hep_job => /orP[/andP[HEP NOTHEP]| /andP[HEP GEL'] //].
      move: H_FP_policy_is_same; rewrite /ep_task => /andP[NOTHEP' _].
      case: (negP NOTHEP NOTHEP'). }
    { rewrite /ELF /hep_job; apply /orP; right.
      move: (RESPECTED j j' t ARR PT BL SCHED); rewrite /hep_job_at /JLFP_to_JLDP /hep_job => GEL'.
      move: H_FP_policy_is_same; rewrite /ep_task =>/andP[_ HEP].
      by apply /andP; split. }
  Qed.

End ELFGeneralizesGEL.


End GeneralityOfELF.

