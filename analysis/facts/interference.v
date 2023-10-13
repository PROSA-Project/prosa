Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.definitions.interference.
Require Export prosa.analysis.definitions.priority.classes.
Require Export prosa.analysis.facts.model.ideal.service_of_jobs.
Require Export prosa.analysis.facts.model.ideal.priority_inversion.

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

  (** Consider a reflexive FP-policy and a JLFP policy compatible with it. *)
  Context {FP : FP_policy Task} {JLFP : JLFP_policy Job}.
  Hypothesis H_compatible : JLFP_FP_compatible JLFP FP.
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.

  (** We observe that any higher-priority job must come from a task with
      either higher or equal priority. *)
  Lemma another_task_hep_job_split_hp_ep :
    forall j1 j2,
      another_task_hep_job j1 j2
      = hp_task_hep_job j1 j2 || other_ep_task_hep_job j1 j2.
  Proof.
    move=> j1 j2; rewrite -[X in _ || X]andbA -andb_orr /another_task_hep_job.
    have [hepj1j2/=|//] := boolP (hep_job j1 j2).
    rewrite -[hp_task _ _](@andb_idr _ (job_task j1 != job_task j2)).
    - by rewrite -andb_orl -hep_hp_ep_task hep_job_implies_hep_task.
    - by apply: contraTN => /eqP->; rewrite hp_task_irrefl.
  Qed.

  (** We establish a higher-or-equal job of another task causing interference,
      can be due to a higher priority task or an equal priority task. *)
  Lemma hep_interference_another_task_split :
    forall (j: Job) (t : instant),
      another_task_hep_job_interference arr_seq sched j t
      = hep_job_from_hp_task_interference arr_seq sched j t
        || hep_job_from_other_ep_task_interference arr_seq sched j t.
  Proof.
    move => j t; rewrite -has_predU; apply: eq_in_has => j' _ /=.
    exact: another_task_hep_job_split_hp_ep.
  Qed.

  (** Now, assuming a uniprocessor model,... *)
  Hypothesis H_uniproc : uniprocessor_model PState.

  (** ...the previous lemma allows us to establish that the cumulative interference incurred by a job
      is equal to the sum of the cumulative interference from higher-or-equal-priority jobs belonging to
      strictly higher-priority tasks (FP) and the cumulative interference from higher-or-equal-priority
      jobs belonging to equal-priority tasks (GEL). *)
  Lemma cumulative_hep_interference_split_tasks_new: forall j t1 Δ,
    cumulative_another_task_hep_job_interference arr_seq  sched j t1 (t1 + Δ)
    = cumulative_interference_from_hep_jobs_from_hp_tasks arr_seq sched j t1 (t1 + Δ)
      + cumulative_interference_from_hep_jobs_from_other_ep_tasks arr_seq sched j t1 (t1 + Δ).
  Proof.
    move => j t1 Δ.
    rewrite -big_split //=; apply: eq_big_seq => t IN.
    rewrite hep_interference_another_task_split.
    have: forall a b, ~~ (a && b) -> (a || b) = a + b :> nat by case; case.
    apply; apply/negP => /andP[/hasP[j' + hp] /hasP[j'' + ep]].
    rewrite !mem_filter => /andP[sj' _] /andP[sj'' _].
    move: hp ep; have ->: j'' = j' by exact: only_one_job_receives_service_at_uni.
    move=> /andP[_ /andP[_ +]] /andP[/andP[_ +] _].
    by rewrite hep_hp_ep_task negb_or ep_task_sym => /andP[_ /negbTE].
  Qed.

End InterferenceProperties.
