Require Export prosa.util.int.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.facts.priority.fp.
Require Export prosa.analysis.facts.priority.gel.
Require Export prosa.analysis.facts.priority.elf.
Require Export prosa.analysis.facts.priority.classes.

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
    `{JobPreemptable Job} {JR : @JobReady Job PState Cost Arrival}.

  (** Suppose [FP] is the fixed-priority policy that parameterizes the ELF policy. *)
  Variable FP : FP_policy Task.

  (** ** ELF Generalizes GEL *)

  (** First, let us consider GEL scheduling, which it trivially
      generalizes by design. *)
  Section ELFGeneralizesGEL.

    (** If the [FP] fixed-priority policy assigns equal priority to all tasks, ... *)
    Hypothesis H_FP_equal_priority :
      forall tsk1 tsk2, ep_task tsk1 tsk2.

    (** ... then the ELF policy reduces to GEL. *)
    Remark ELF_generalizes_GEL :
      forall (JLFP : JLFP_policy Job),
        policy_is_ELF FP JLFP <-> policy_is_GEL JLFP.
    Proof.
      move=> JLFP; split => [ELF|GEL]; (repeat split => //) => j j' PRIO.
      - by apply: ELF_policy_priority_point_order.
      - by apply/ep_hep_task/H_FP_equal_priority.
      - by apply: GEL_policy_priority_point_order.
    Qed.

  End ELFGeneralizesGEL.

  (** ** ELF Generalizes Fixed-Priority Scheduling *)

  (** Next, let us turn to fixed-priority scheduling, which by design ELF also
      generalizes under certain assumptions. *)

  Section ELFGeneralizesFixedPriority.

    (** Assume that the underlying task-priority relation has the usual order
        properties. *)
    Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
    Hypothesis H_transitive_priorities : transitive_task_priorities FP.
    Hypothesis H_total_priorities : total_task_priorities FP.

    (** Consider a JLFP policy that behaves as an ELF policy. *)
    Context {JLFP : JLFP_policy Job}.
    Hypothesis H_policy_is_ELF : policy_is_ELF FP JLFP.

    (** Since ELF never inverts fixed task priority, an ELF schedule is always
        also valid with respect to the underlying task-level FP policy. *)
    Remark ELF_respects_fixed_priority :
      forall sched arr_seq,
        respects_JLFP_policy_at_preemption_point arr_seq sched JLFP
        -> respects_FP_policy_at_preemption_point arr_seq sched FP.
    Proof.
      move=> sched arr_seq RESPECTED j j' t ARR PT BL SCHED.
      rewrite hep_job_at_fp.
      apply: ELF_policy_task_priority_order => //.
      exact: RESPECTED.
    Qed.

    (** Additionally, if each task has a distinct priority, or equivalently, no
        two tasks have equal priority according to the [FP] fixed-priority
        policy, then the reverse also holds: the ELF policy reduces to the
        underlying FP policy. To show this, we require some additional setup and
        assumptions. *)

    (** First, note that FP-compliance does not constrain jobs of the same task,
        whereas a given ELF policy may resolve ties arbitrarily when both
        jobs have the same task priority and the same priority point.  Hence,
        in the only ambiguous case, we explicitly rule out tie-breaking that
        disagrees with the required job-level priority order. *)
    Hypothesis H_no_tiebreak :
      forall j j',
        ep_task (job_task j) (job_task j') ->
        job_priority_point j = job_priority_point j' ->
        hep_job j j'.

    (** Second, assume that task priorities are indeed distinct. *)
    Hypothesis H_distinct_fixed_priorities :
      forall tsk1 tsk2, tsk1 != tsk2 -> ~~ ep_task tsk1 tsk2.

    (** Third, consider any given valid arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.
    Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

    (** Then in any given valid schedule ... *)
    Variable sched : schedule PState.
    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    (** ... in which tasks execute sequentially, ... *)
    Hypothesis H_sequential : sequential_tasks arr_seq sched.

    (** ... the ELF policy and the underlying FP policy are equivalent. *)
    Remark elf_generalizes_fixed_priority :
        respects_JLFP_policy_at_preemption_point arr_seq sched JLFP
        <-> respects_FP_policy_at_preemption_point arr_seq sched FP.
    Proof.
      split; first exact: ELF_respects_fixed_priority.
      move=> RESPECTED j j' t ARR PT BL SCHED.
      move: (RESPECTED j j' t ARR PT BL SCHED);
        rewrite hep_job_at_fp => HEP.
      rewrite hep_job_at_jlfp.
      move: HEP; rewrite hep_hp_ep_task => /orP [HP|EP];
        first by apply: ELF_policy_higher_priority_task.
      have SAME: same_task j' j by apply/eqP; move: EP; apply: contraTeq.
      have [LEQ|LT] := leqP (job_arrival j') (job_arrival j).
      { move: LEQ; rewrite leq_eqVlt => /orP [/eqP EQ|LT];
          last exact: ELF_policy_earlier_arrival.
        apply: H_no_tiebreak => //.
        rewrite /job_priority_point EQ.
        by move: SAME; rewrite /same_task => /eqP ->. }
      { exfalso.
        move: BL; rewrite /backlogged => /andP [INCOMP _].
        apply ready_implies_incomplete in INCOMP.
        move: INCOMP => /negP; apply.
        by apply: (H_sequential j j') => //; rewrite same_task_sym. }
    Qed.

  End ELFGeneralizesFixedPriority.


End GeneralityOfELF.
