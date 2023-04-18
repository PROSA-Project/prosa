Require Import prosa.util.int.
Require Import prosa.model.priority.gel.
Require Import prosa.model.schedule.priority_driven.
Require Import prosa.analysis.facts.model.sequential.
Require Import prosa.analysis.facts.priority.sequential.

(** In this file we state and prove some basic facts
    about the GEL scheduling policy. *)
Section GELBasicFacts.

  (** Consider any type of tasks and jobs. *)
  Context `{Task : TaskType} {Job : JobType} `{JobTask Job Task} `{PriorityPoint Task}.
  Context {AR : JobArrival Job}.

  Section HEPJobArrival.
    (** Consider a job [j]... *)
    Variable j : Job.

    (** ... and a higher or equal priority job [j']. *)
    Variable j' : Job.
    Hypothesis H_j'_hep : hep_job j' j.

    (** The arrival time of [j'] is bounded as follows. *)
    Lemma hep_job_arrives_before :
      ((job_arrival j')%:R <=
         (job_arrival j)%:R +
           task_priority_point (job_task j) - task_priority_point (job_task j'))%R.
    Proof.
      by move : H_j'_hep; rewrite /hep_job /GEL /job_priority_point; lia.
    Qed.

    (** Using the above lemma, we prove that for any
        higher-or-equal priority job [j'], the term
        [job_arrival j +  task_priority_point (job_task j) -
        task_priority_point (job_task j')] is positive.  *)
    Corollary hep_job_arrives_after_zero :
      (0 <= (job_arrival j)%:R +
             task_priority_point (job_task j) - task_priority_point (job_task j'))%R.
    Proof. exact: le_trans hep_job_arrives_before. Qed.

  End HEPJobArrival.

  (** If we are looking at two jobs of the same task, then [hep_job] is a
      statement about their respective arrival times. *)
  Fact hep_job_arrival_gel :
    forall j j',
      same_task j j' ->
      (hep_job j j')= (job_arrival j <= job_arrival j').
  Proof.
    move=> j j' /eqP SAME.
    rewrite /hep_job/GEL/job_priority_point SAME.
    by case CMP: (job_arrival _ <= job_arrival _); lia.
  Qed.

  (** Next, we prove that the GEL policy respects sequential tasks. *)
  Lemma GEL_respects_sequential_tasks:
    policy_respects_sequential_tasks (GEL Job Task).
  Proof. by move =>  j1 j2 TSK ARR; rewrite hep_job_arrival_gel. Qed.

  (** In this section, we prove that in a schedule following
      the GEL policy, tasks are always sequential. *)
  Section SequentialTasks.

    (** Consider any arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.

    (** Allow for any uniprocessor model. *)
    Context {PState : ProcessorState Job}.
    Hypothesis H_uniproc : uniprocessor_model PState.

    (** Next, consider any schedule of the arrival sequence, ... *)
    Variable sched : schedule PState.

    Context `{JobCost Job}.
    Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

    (** ... allow for any work-bearing notion of job readiness, ... *)
    Context `{@JobReady Job PState _ AR}.
    Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

    (** ... and assume that the schedule is valid. *)
    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    (** In addition, we assume the existence of a function mapping jobs
        to their preemption points ... *)
    Context `{JobPreemptable Job}.

    (** ... and assume that it defines a valid preemption model. *)
    Hypothesis H_valid_preemption_model:
      valid_preemption_model arr_seq sched.

    (** Next, we assume that the schedule respects the scheduling policy at every preemption point. *)
    Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task).

    (** To prove sequentiality, we use the lemma
        [early_hep_job_is_scheduled]. Clearly, under the GEL priority
        policy, jobs satisfy the conditions described by the lemma
        (i.e., given two jobs [j1] and [j2] from the same task, if [j1]
        arrives earlier than [j2], then [j1] always has a higher
        priority than job [j2], and hence completes before [j2]);
        therefore GEL implies the [sequential_tasks] property. *)
    Lemma GEL_implies_sequential_tasks:
      sequential_tasks arr_seq sched.
    Proof.
      move => j1 j2 t ARR1 ARR2 SAME LT.
      apply: early_hep_job_is_scheduled => // t'.
      rewrite /hep_job_at  /JLFP_to_JLDP !hep_job_arrival_gel //.
      - lia.
      - by rewrite same_task_sym.
    Qed.

  End SequentialTasks.

End GELBasicFacts.

(** We add the following lemma to the basic facts database. *)
Global Hint Resolve
GEL_respects_sequential_tasks
  : basic_rt_facts.
