Require Export prosa.model.priority.classes.

(** In this section, we prove some basic properties about priority relations. *)
Section BasicLemmas.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  
  (** Consider a JLFP-policy that indicates a higher-or-equal priority relation. *)             
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
