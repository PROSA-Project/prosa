Require Import prosa.model.priority.elf.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.definitions.priority.classes.
Require Export prosa.analysis.facts.model.workload.

(** In this file, we prove lemmas that are useful when both an FP policy and
    a JLFP policy are present in context. *)

(** In this section, we prove a lemma about workload partitioning which is useful
    for reasoning about the interference bound function for the ELF scheduling policy. *)
Section WorkloadTaskSum.

  (** Consider any type of tasks with relative priority points...*)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ...and jobs of these tasks. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task} `{JobCost Job} .

  (** Let us consider an FP policy and a JLFP policy present in context. *)
  Context {FP : FP_policy Task}.
  Context {JLFP : JLFP_policy Job}.

  (** Consider any valid arrival sequence [arr_seq]. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence (arr_seq).

  (** We consider an arbitrary task set [ts]... *)
  Variable ts : seq Task.
  Hypothesis H_task_set : uniq ts.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** We define a predicate to identify others tasks which have equal priority as [tsk]. *)
  Let other_ep_task := fun tsk_o => (ep_task tsk tsk_o) && (tsk_o != tsk).

  (** We consider a job [j] belonging to this task... *)
  Variable j : Job.
  Hypothesis H_job_of_task : job_of_task tsk j.

  (** ... and focus on the jobs arriving in an arbitrary interval <<[t1, t2)>>... *)
  Variable t1 t2 : duration.
  Let jobs_arrived := arrivals_between arr_seq t1 t2.

  (** ... that belong to other tasks that have equal priority as [tsk] and
      have higher-or-equal priority [JLFP] than [j]. *)
  Let hep_job_of_ep_other_task :=
    fun j' : Job =>
      hep_job j' j
      && ep_task (job_task j') (job_task j)
      && (job_task j' != job_task j).

  (** Finally, we establish that the cumulative workload of these jobs can be partitioned
      task-wise. *)
  Lemma workload_of_hep_jobs_partitioned_by_tasks :
    workload_of_jobs hep_job_of_ep_other_task jobs_arrived
      = \sum_(tsk_o <- ts | other_ep_task tsk_o)
        workload_of_jobs
          (fun j0 => hep_job_of_ep_other_task j0 && (job_task j0 == tsk_o))
          jobs_arrived.
  Proof.
    apply: workload_of_jobs_partitioned_by_tasks => //.
    - by move=> j' IN'; apply/H_all_jobs_from_taskset/in_arrivals_implies_arrived/IN'.
    - move: H_job_of_task => /eqP TSK j' IN'.
      rewrite /other_ep_task /hep_job_of_ep_other_task TSK
        => /andP [/andP [_ EP] NEQ].
      apply/andP; split => //.
      by rewrite ep_task_sym.
    - by apply: arrivals_uniq.
  Qed.

End WorkloadTaskSum.
