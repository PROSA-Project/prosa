Require Import prosa.model.priority.elf.
Require Export prosa.analysis.facts.priority.classes.

  (** In this section, we note three basic properties of the ELF policy: the
      priority relation is reflexive, transitive, and total.  *)
Section PropertiesOfELF.

  (** Consider any type of tasks with relative priority points...*)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ...and jobs of these tasks. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task} .

  (** Consider any arbitrary FP policy ...*)
  Variable FP : FP_policy Task.

  (** ... that is reflexive, transitive, and total. *)
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** ELF is reflexive. *)
  Lemma ELF_is_reflexive : reflexive_job_priorities (ELF FP).
  Proof. by move=> j; apply /orP; right; apply/andP; split=> //; exact: GEL_is_reflexive. Qed.

  (** ELF is transitive. *)
  Lemma ELF_is_transitive : transitive_job_priorities (ELF FP).
  Proof.
    move=> y x z.
    move=> /orP [hpxy| /andP[hepxy jpxy]] => /orP[hpyz| /andP [hepyz jpyz]].
    { apply/orP; left; exact: hp_trans hpyz. }
    { apply/orP; left; exact: hp_hep_trans hepyz. }
    { apply/orP; left; exact: hep_hp_trans hpyz. }
    { apply/orP; right; apply /andP; split.
      - exact: H_transitive_priorities hepyz.
      - by apply: (GEL_is_transitive y). }
  Qed.

  (** ELF is total. *)
  Lemma ELF_is_total : total_job_priorities (ELF FP).
  Proof.
    move=> x y.
    rewrite -implyNb; apply/implyP => /norP [Nhpxy /nandP [Nhpxy'|Njpxy] ].
    { by apply /orP; left; rewrite -not_hep_hp_task. }
    { move: Nhpxy => /nandP [Nhepxy| NNhepyx].
    { by apply /orP; left; rewrite -not_hep_hp_task. }
    { apply /orP; right. move: NNhepyx => /negbNE -> /=.
      move: Njpxy; unfold hep_job, GEL; lia. }}
    Qed.

End PropertiesOfELF.


(** We add the above facts into a "Hint Database" basic_rt_facts, so Coq will
    be able to apply them automatically where needed. *)
Global Hint Resolve
     ELF_is_reflexive
     ELF_is_transitive
     ELF_is_total
  : basic_rt_facts.
