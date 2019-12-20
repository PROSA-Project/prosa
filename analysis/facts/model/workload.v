Require Export prosa.model.aggregate.workload.
Require Export prosa.analysis.facts.behavior.arrivals.

(** * Lemmas about Workload of Sets of Jobs *)
(** In this file, we establish basic facts about the workload of sets of jobs. *)  
Section WorkloadFacts.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** For simplicity, let's define a local name. *)
  Let arrivals_between := arrivals_between arr_seq.  
  
  (** We prove that workload can be split into two parts. *)
  Lemma workload_of_jobs_cat:
    forall t t1 t2 P,
      t1 <= t <= t2 ->
      workload_of_jobs P (arrivals_between t1 t2) =
      workload_of_jobs P (arrivals_between t1 t)
      + workload_of_jobs P (arrivals_between t t2).
  Proof.
    move => t t1 t2 P /andP [GE LE].
    rewrite /workload_of_jobs /arrivals_between.
      by rewrite (arrivals_between_cat _ _ t) // big_cat.
  Qed.

End WorkloadFacts.