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

  (** Let us consider an FP policy and a compatible JLFP policy present in context. *)
  Context {FP : FP_policy Task}.
  Context {JLFP : JLFP_policy Job}.
  Hypothesis JLFP_FP_is_compatible : JLFP_FP_compatible JLFP FP.

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
  Definition other_ep_task := fun tsk_o => (ep_task tsk tsk_o) && (tsk_o != tsk).

  (** We consider a job [j] belonging to this task ... *)
  Variable j : Job.
  Hypothesis H_job_of_task : job_of_task tsk j.

  (** ... and focus on the jobs arriving in an arbitrary interval <<[t1, t2)>>. *)
  Variable t1 t2 : duration.
  Let jobs_arrived := arrivals_between arr_seq t1 t2.

  (** We first consider jobs that belong to other tasks that have equal priority
      as [tsk] and have higher-or-equal priority [JLFP] than [j]. *)
  Definition hep_job_of_ep_other_task :=
    fun j' : Job =>
      hep_job j' j
      && ep_task (job_task j') (job_task j)
      && (job_task j' != job_task j).

  (** We then establish that the cumulative workload of these jobs can be partitioned
      task-wise. *)
  Lemma hep_workload_from_other_ep_partitioned_by_tasks :
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

  (** Now we focus on jobs belonging to tasks which have higher priority than [tsk]. *)
  Definition from_hp_task (j' : Job) :=
    hp_task (job_task j') (job_task j).

  (** We also identify higher-or-equal-priority jobs [JLFP] that belong to
      (1) tasks having higher priority than [tsk] ... *)
  Definition hep_from_hp_task (j' : Job) :=
    hep_job j' j && hp_task (job_task j') (job_task j).

  (** ... (2) tasks having equal priority as [tsk]. *)
  Definition hep_from_ep_task (j' : Job) :=
    hep_job j' j && ep_task (job_task j') (job_task j).

  (** First, we establish that the cumulative workload of higher-or-equal-priority
      jobs belonging to tasks having higher priority than [tsk] is equal to the
      cumulative workload of jobs belonging to higher-priority tasks. *)
  Lemma hep_hp_workload_hp :
    workload_of_jobs hep_from_hp_task jobs_arrived = workload_of_jobs from_hp_task jobs_arrived.
  Proof.
    apply/eq_bigl =>j0; apply /idP/idP.
    - by move=> /andP[].
    - move=> Hp; apply/andP; split =>//.
      by apply: (hp_task_implies_hep_job JLFP FP).
  Qed.

  (** We then establish that the cumulative workload of higher-or-equal priority jobs
      is equal to the sum of cumulative workload of higher-or-equal priority jobs
      belonging to higher-priority tasks and the cumulative workload of
      higher-or-equal-priority jobs belonging to equal-priority tasks. *)
  Lemma hep_workload_partitioning_taskwise :
    workload_of_higher_or_equal_priority_jobs j jobs_arrived
    = workload_of_jobs hep_from_hp_task jobs_arrived
      + workload_of_jobs hep_from_ep_task jobs_arrived.
  Proof.
    rewrite /workload_of_higher_or_equal_priority_jobs /workload_of_jobs.
    rewrite (bigID from_hp_task) /=; congr (_ + _); apply: eq_bigl => j0.
    apply: andb_id2l => HEPj.
    have HEPt : hep_task (job_task j0) (job_task j) by apply (hep_job_implies_hep_task JLFP).
    apply/idP/idP; rewrite negb_and.
    - move =>/orP[nHEPt| /negPn ?].
      + exfalso; by move: nHEPt; rewrite HEPt.
      + by apply/andP.
    - by move => /andP[? ?]; apply/orP; right; apply/negPn.
  Qed.

End WorkloadTaskSum.
