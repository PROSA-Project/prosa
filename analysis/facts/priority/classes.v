Require Export prosa.model.priority.classes.

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

(** We add the above observation into the "Hint Database" basic_rt_facts, so Coq
    will be able to apply it automatically. *)
Global Hint Resolve respects_sequential_tasks : basic_rt_facts.
