Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.definitions.interference.
Require Export prosa.analysis.definitions.priority.classes.
Require Export prosa.analysis.facts.model.ideal.service_of_jobs.
Require Export prosa.analysis.facts.busy_interval.ideal.priority_inversion.

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

  (** We establish a higher-or-equal job of another task causing interference,
      can be due to a higher priority task or an equal priority task. *)
  Lemma hep_interference_another_task_split :
    forall (j: Job) (t : instant),
      another_task_hep_job_interference arr_seq sched j t
      = hep_job_from_hp_task_interference arr_seq sched j t
        || hep_job_from_other_ep_task_interference arr_seq sched j t.
  Proof.
    move => j t.
    rewrite -has_predU; apply: eq_in_has => j' IN //=.
    case: (receives_service_at _ _ _); [rewrite !andbT|rewrite !andbF //].
    rewrite /another_task_hep_job/hp_task_hep_job
      /other_ep_task_hep_job/ep_task_hep_job.
    case HEP: (hep_job j' j); [rewrite !andTb|rewrite !andFb //].
    case HPT: (job_task _ != job_task _);
      last by rewrite andbF orbF; move: HPT => /eqP ->; rewrite hp_task_irrefl.
    rewrite andbT -hep_hp_ep_task; symmetry.
    by move: H_compatible => [+ _]; apply.
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
    have: forall a b, (~~ (a && b)) -> nat_of_bool (a || b) = a + b by case; case.
    apply. apply/negP => /andP [/hasP [j' _ /andP [HP SERV']]
                                 /hasP [j'' _ /andP [/andP [EP _] SERV'']]].
    move: HP EP; have ->: j' = j'' by apply: recv_service_impl_same_job; eauto.
    by move=> /andP [_ /andP [_ /negP +]] /andP [_ /andP [_ +]].
  Qed.

End InterferenceProperties.
