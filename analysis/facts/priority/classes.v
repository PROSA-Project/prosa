Require Export prosa.model.priority.classes.
Require Export prosa.analysis.definitions.priority.classes.

(** In this section, we prove some basic properties about priority relations. *)
Section BasicLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Consider a JLFP policy that indicates a higher-or-equal priority relation. *)
  Context `{JLFP_policy Job}.

  (** First, we prove that [another_hep_job] relation is anti-reflexive. *)
  Lemma another_hep_job_antireflexive :
    forall j, ~ another_hep_job j j.
  Proof.
    by move => j /andP [_ /negP NEQ]; apply: NEQ.
  Qed.

  (** We show that [another_task_hep_job] is "task-wise"
      anti-reflexive; that is, given two jobs [j] and [j'] from the
      same task, [another_task_hep_job j' j] is false. *)
  Lemma another_task_hep_job_taskwise_antireflexive :
    forall tsk j j',
      job_of_task tsk j ->
      job_of_task tsk j' ->
      ~ another_task_hep_job j' j.
  Proof.
    move=> tsko j j' /eqP TSK1 /eqP TSK2 /andP [_ AA].
    by move: AA; rewrite TSK1 TSK2 => /negP A; apply: A.
  Qed.

End BasicLemmas.

(** In the following section, we establish properties of [hp_task] and [ep_task ]auxiliary
    priority relations defined for FP policies. They are useful in proving properties of the
    ELF scheduling policy. *)
Section FPRelationsProperties.

  (** Consider any type of tasks and an FP policy that indicates a higher-or-equal
      priority relation on the tasks.*)
  Context {Task : TaskType} {FP_policy : FP_policy Task}.

  (** First, we prove some trivial lemmas about the [hep_task] and [ep_task]
      relations. *)
  Section BasicProperties.

    (** [hp_task] is irreflexive. *)
    Lemma hp_task_irrefl : irreflexive hp_task.
    Proof. by move=> tsk; rewrite /hp_task; case: hep_task. Qed.

    (** If a task [tsk1] has higher priority than task [tsk2], then task [tsk1] has
        higher-or-equal priority than task [tsk2]. *)
    Lemma hp_hep_task :
      forall tsk1 tsk2,
        hp_task tsk1 tsk2 ->
        hep_task tsk1 tsk2.
    Proof. by move=> ? ? /andP[]. Qed.

    (** If a task [tsk1] has equal priority as task [tsk2], then task [tsk1] has
        higher-or-equal priority than task [tsk2]. *)
    Lemma ep_hep_task :
      forall tsk1 tsk2,
        ep_task tsk1 tsk2 ->
        hep_task tsk1 tsk2.
    Proof. by move=> ? ? /andP[]. Qed.

    (** Task [tsk1] having equal priority as task [tsk2] is equivalent to task [tsk2]
        having equal priority as task [tsk1]. *)
    Lemma ep_task_sym :
      forall tsk1 tsk2,
        ep_task tsk1 tsk2 = ep_task tsk2 tsk1.
    Proof. by move=> x y; rewrite /ep_task andbC. Qed.

    (** If a task [tsk1] has higher-or-equal priority than a task
        [tsk2], then [tsk1] either has strictly higher priority than
        [tsk2] or the two have equal priority. *)
    Lemma hep_hp_ep_task :
      forall tsk1 tsk2,
        hep_task tsk1 tsk2 = hp_task tsk1 tsk2 || ep_task tsk1 tsk2.
    Proof. by move=> ? ?; rewrite /hp_task /ep_task -andb_orr orNb andbT. Qed.

  End BasicProperties.

  (** In the following section, we establish a useful property about the equal
      priority relation, which follows when the FP policy is reflexive.  *)
  Section ReflexiveProperties.

    (** Assuming that the FP policy is reflexive ... *)
    Hypothesis H_reflexive : reflexive hep_task.

    (** ... it follows that the equal priority relation is reflexive. *)
    Lemma eq_reflexive : reflexive ep_task.
    Proof. by move=> ?; apply /andP; split. Qed.

  End ReflexiveProperties.

  (** Now we establish useful properties about the higher priority relation,
      which follow when the FP policy is transitive.  *)
  Section TransitiveProperties.

    (** Assuming that the FP policy is transitive ... *)
    Hypothesis H_transitive : transitive hep_task.

    (** ... it follows that the higher priority relation is also transitive.  *)
    Lemma hp_trans : transitive hp_task.
    Proof.
      move=> y x z /andP[hepxy Nhepyx] /andP[hepyz Nhepyz]; apply/andP; split.
      { exact: H_transitive hepyz. }
      { by apply: contraNN Nhepyx; exact: H_transitive. }
    Qed.

    (** If task [tsk1] has higher priority than task [tsk2], and task [tsk2] has
        higher-or-equal priority than task [tsk3], then task [tsk1] has higher priority
        than task [tsk3]. *)
    Lemma hp_hep_trans :
      forall tsk1 tsk2 tsk3,
        hp_task tsk1 tsk2 ->
        hep_task tsk2 tsk3 ->
        hp_task tsk1 tsk3.
    Proof.
      move=> x y z /andP[hepxy Nhepyx] hepyz; apply/andP; split.
      { exact: H_transitive hepyz. }
      { by apply: contraNN Nhepyx; exact: H_transitive. }
    Qed.

    (** If task [tsk1] has higher-or-equal priority than task [tsk2], and task [tsk2]
        has strictly higher priority than task [tsk3], then task [tsk1]
        has higher priority than task [tsk3]. *)
    Lemma hep_hp_trans :
      forall tsk1 tsk2 tsk3,
        hep_task tsk1 tsk2 ->
        hp_task tsk2 tsk3 ->
        hp_task tsk1 tsk3.
    Proof.
      move=> x y z hepxy /andP[hepyz Nhepzy]; apply/andP; split.
      { exact: H_transitive hepyz. }
      { apply: contraNN Nhepzy => hepzy; exact: H_transitive hepxy. }
    Qed.

  End TransitiveProperties.

  (** Finally, we establish a useful property about the higher priority relation,
      which follows when the FP policy is total.  *)
  Section TotalProperties.

    (** We assume that the FP policy is total. *)
    Hypothesis H_total : total hep_task.

    (** If a task [tsk1] does not have higher-or-equal priority than task [tsk2], then
        task [tsk2] has higher priority than task [tsk1].  *)
    Lemma not_hep_hp_task :
      forall tsk1 tsk2, ~~ hep_task tsk1 tsk2 = hp_task tsk2 tsk1.
    Proof.
      move=> x y; apply /idP/idP => [| /andP[//]].
      move=> Nhepxy; apply /andP; split=> [|//].
      have /orP[h | //] := H_total x y.
      by exfalso; move/negP: Nhepxy.
    Qed.

    (** The converse also holds. *)
    Lemma not_hp_hep_task :
      forall tsk1 tsk2, ~~ hp_task tsk1 tsk2 = hep_task tsk2 tsk1.
    Proof. by move=> x y; rewrite -not_hep_hp_task negbK. Qed.

  End TotalProperties.

End FPRelationsProperties.

(** In the following section, we show that FP policies respect the sequential
    tasks hypothesis. It means that later-arrived jobs of a task don't have
    higher priority than earlier-arrived jobs of the same task (assuming that
    task priorities are reflexive).*)
Section FPRemarks.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks, ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** .. and assume that jobs have a cost and an arrival time. *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any FP policy. *)
  Context {FP : FP_policy Task}.

  Remark respects_sequential_tasks :
    reflexive_task_priorities FP ->
    policy_respects_sequential_tasks (FP_to_JLFP FP).
  Proof.
    move => REFL j1 j2 /eqP EQ LT.
    by rewrite /hep_job /FP_to_JLFP EQ.
  Qed.

End FPRemarks.

Section JLFPFP.
   (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** Consider any pair of JLFP and FP policies. *)
  Context (JLFP : JLFP_policy Job) (FP : FP_policy Task).

  (** If a policy is [JLFP_FP_compatible], then a job [j1] has 
      lower priority than a job [j2] if the task of [j1] has 
      lower priority than the task of [j2]. *)
  Lemma not_hep_task_implies_not_hep_job: forall j1 j2,
      JLFP_FP_compatible JLFP FP ->
      ~~ hep_task (job_task j1) (job_task j2) ->
      ~~ hep_job j1 j2.
  Proof.
    move =>  j1 j2 [NOTHEP HP] NOTHEPTSK.
    specialize (NOTHEP j1 j2).
    by apply contra in NOTHEP.
  Qed.

End JLFPFP.

(** We add the above observation into the "Hint Database" basic_rt_facts, so Coq
    will be able to apply it automatically. *)
Global Hint Resolve respects_sequential_tasks : basic_rt_facts.
