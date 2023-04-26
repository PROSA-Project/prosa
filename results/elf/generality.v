From mathcomp Require Import eqtype ssrnat seq path fintype bigop.
Require Export prosa.util.int.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.model.priority.elf.
Require Export prosa.analysis.facts.priority.gel.
Require Export prosa.analysis.facts.priority.elf.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.facts.model.sequential.

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

  (** ** ELF Generalizes GEL *)

  (** First, let us consider GEL scheduling, which by design ELF trivially
      generalizes. *)
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
    by move=> sched arr_seq
       ; split=> RESPECTED j j' t ARR PT BL SCHED
       ; move: (RESPECTED j j' t ARR PT BL SCHED)
       ; rewrite !hep_job_at_jlfp hep_job_elf_gel.
  Qed.

  (** ** ELF Generalizes Fixed-Priority Scheduling *)

  (** Next, let us turn to fixed-priority scheduling, which by design ELF also
      generalizes under certain assumptions. *)

  Section ELFGeneralizesFixedPriority.

    (** Since (1) ELF uses GEL only to break ties in fixed task priority, and
        since (2) a fixed-priority policy says nothing about how jobs of
        equal-priority tasks should be ordered (i.e., "ties in priority are
        broken arbitrarily"), an [ELF fp] schedule always is also a valid [fp]
        schedule. *)
    Remark elf_is_fixed_priority :
      forall sched arr_seq,
        respects_JLFP_policy_at_preemption_point arr_seq sched (ELF fp)
        -> respects_FP_policy_at_preemption_point arr_seq sched fp.
    Proof.
      move=> sched arr_seq RESPECTED j j' t ARR PT BL SCHED.
      rewrite hep_job_at_fp.
      by move: (RESPECTED j j' t ARR PT BL SCHED)
         ; rewrite hep_job_at_jlfp /hep_job
            => /orP[/andP[HEP NOTHEP] //| /andP[HEP GEL] //].
    Qed.

    (** Additionally, if each task has a distinct priority, or equivalently, no
        two tasks have equal priority according to the [fp] fixed-priority
        policy, then the reverse also holds: the ELF policy reduces to the
        underlying FP policy. To show this, we require some additional setup and
        assumptions. *)

    (** First, assume that task priorities are indeed distinct. *)
    Hypothesis H_distinct_fixed_priorities:
      forall tsk1 tsk2, tsk1 != tsk2 -> ~~ ep_task tsk1 tsk2.

    (** Second, consider any given valid arrival sequence.*)
    Variable arr_seq : arrival_sequence Job.
    Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

    (** Then in any given valid schedule ... *)
    Variable sched : schedule PState.
    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    (** ... in which tasks execute sequentially ... *)
    Hypothesis H_sequential : sequential_tasks arr_seq sched.

    (** ... the ELF policy and the underlying FP policy are equivalent. *)
    Remark elf_generalizes_fixed_priority :
        respects_JLFP_policy_at_preemption_point arr_seq sched (ELF fp)
        <-> respects_FP_policy_at_preemption_point arr_seq sched fp.
    Proof.
      split; first exact: elf_is_fixed_priority.
      move=> RESPECTED j j' t ARR PT BL SCHED.
      move: (RESPECTED j j' t ARR PT BL SCHED);
        rewrite hep_job_at_fp => HEP.
      rewrite /ELF; apply /orP.
      have [/eqP EQ|NEQ] := eqVneq (job_task j') (job_task j); [right|left].
      { apply/andP; split => //.
        have [LEQ|LT] := leqP (job_arrival j') (job_arrival j);
          first by rewrite hep_job_arrival_gel.
        exfalso.
        have COMP: completed_by sched j t.
          by apply: (H_sequential j j') => //; rewrite same_task_sym.
        move: BL; rewrite /backlogged => /andP [INCOMP _].
        apply ready_implies_incomplete in INCOMP.
        by move: INCOMP => /negP. }
      { have /negP NEP: ~~ ep_task (job_task j') (job_task j).
          by apply: H_distinct_fixed_priorities.
        by move: HEP; rewrite hep_hp_ep_task => /orP [|]. }
    Qed.

  End ELFGeneralizesFixedPriority.

End ELFGeneralizesGEL.

End GeneralityOfELF.
