Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.definitions.interference.
Require Export prosa.analysis.definitions.priority.classes.

Section InterferenceProperties.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType} {jt : JobTask Job Task}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule. *)
  Variable sched : schedule PState.

  (** Consider a FP-policy and a JLFP policy compatible with it. *)
  Context {FP : FP_policy Task} {JLFP : JLFP_policy Job}.
  Hypothesis H_compatible : JLFP_FP_compatible JLFP FP.

  Lemma another_task_hep_job_interference_split_task :
    forall (j: Job) (t : instant),
      another_task_hep_job_interference arr_seq sched j t
      = hp_task_interference arr_seq sched j t
        || other_ep_task_hep_job_interference arr_seq sched j t.
  Proof.
    move=> j t; rewrite -has_predU.
    apply: eq_in_has => jhp jhp_arr /=; rewrite -andb_orl; congr andb.
    rewrite /another_task_hep_job /other_ep_task_hep_job /ep_task_hep_job.
    have [->|tjhp_tj] := eqVneq; first by rewrite hp_task_irrefl// !andbF orbF.
    case E: hep_job => /=; symmetry.
    - by rewrite !andbT -hep_hp_ep_task; apply: (proj1 H_compatible).
    - by rewrite orbF; apply: contraFF E; apply: (proj2 H_compatible).
  Qed.

End InterferenceProperties.
