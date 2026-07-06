Require Import prosa.util.int.
Require Export prosa.model.priority.gel.
Require Import prosa.model.schedule.priority_driven.
Require Import prosa.analysis.facts.model.sequential.
Require Import prosa.analysis.facts.priority.sequential.

(** In this file we state and prove some basic facts
    about the GEL scheduling policy. *)
Section GELBasicFacts.

  (** Consider any type of tasks and jobs. *)
  Context `{Task : TaskType} {Job : JobType}
    `{JobTask Job Task} `{PriorityPoint Task} {Arrival : JobArrival Job}.

  (** Assume GEL scheduling. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_policy_is_GEL : policy_is_GEL JLFP.

  (** Under GEL, higher-or-equal priority implies no later absolute priority
      point. *)
  Fact GEL_policy_priority_point_order :
    forall j j',
      hep_job j j' -> (job_priority_point j <= job_priority_point j')%R.
  Proof. by move: H_policy_is_GEL => [GEL _] j j'; exact: GEL. Qed.

  (** The GEL policy is reflexive by assumption. *)
  Fact GEL_policy_is_reflexive :
    reflexive_job_priorities JLFP.
  Proof. by move: H_policy_is_GEL => [_ [REFL _]]. Qed.

  (** The GEL policy is transitive by assumption. *)
  Fact GEL_policy_is_transitive :
    transitive_job_priorities JLFP.
  Proof. by move: H_policy_is_GEL => [_ [_ [TRANS _]]]. Qed.

  (** The GEL policy is total by assumption. *)
  Fact GEL_policy_is_total :
    total_job_priorities JLFP.
  Proof. by move: H_policy_is_GEL => [_ [_ [_ TOTAL]]]. Qed.

  (** Hence, a job with a strictly earlier priority point has higher-or-equal
      priority. *)
  Fact GEL_policy_earlier_priority_point :
    forall j j',
      (job_priority_point j < job_priority_point j')%R -> hep_job j j'.
  Proof.
    move=> j j' PP.
    move: (GEL_policy_is_total j j') => /orP [//|HEP].
    move: (GEL_policy_priority_point_order _ _ HEP).
    by lia.
  Qed.

  (** Conversely, if a job does not have higher-or-equal priority, then the
      other job has no later priority point. *)
  Fact GEL_policy_not_hep_priority_point_order :
    forall j j',
      ~~ hep_job j j' -> (job_priority_point j' <= job_priority_point j)%R.
  Proof.
    move=> j j' NHEP.
    apply: GEL_policy_priority_point_order.
    move: (GEL_policy_is_total j j').
    by rewrite (negbTE NHEP).
  Qed.

  Section HEPJobArrival.
    (** Consider a job [j]... *)
    Variable j : Job.

    (** ... and a higher or equal priority job [j']. *)
    Variable j' : Job.
    Hypothesis H_j'_hep : hep_job j' j.

    (** The arrival time of [j'] is bounded as follows. *)
    Lemma hep_job_arrives_before :
      ((job_arrival j')%:R
       <= (job_arrival j)%:R
         + task_priority_point (job_task j)
         - task_priority_point (job_task j'))%R.
    Proof.
      move: (GEL_policy_priority_point_order _ _ H_j'_hep).
      by rewrite /job_priority_point/jpp_from_tpp; lia.
    Qed.

    (** Using the above lemma, we prove that for any
        higher-or-equal priority job [j'], the term
        [job_arrival j +  task_priority_point (job_task j) -
        task_priority_point (job_task j')] is positive.  *)
    Corollary hep_job_arrives_after_zero :
      (0 <= (job_arrival j)%:R
           + task_priority_point (job_task j)
           - task_priority_point (job_task j'))%R.
    Proof. exact: le_trans hep_job_arrives_before. Qed.

  End HEPJobArrival.

  (** Next, we prove that the GEL policy respects sequential tasks: within a
      task, a strictly earlier-arriving job has a strictly earlier priority
      point. *)
  Lemma GEL_respects_sequential_tasks :
    policy_respects_sequential_tasks JLFP.
  Proof.
    move=> j1 j2 /eqP SAME LT.
    apply: GEL_policy_earlier_priority_point => //.
    by rewrite /job_priority_point/jpp_from_tpp SAME; lia.
  Qed.

End GELBasicFacts.

(** We add the following lemma to the basic facts database. *)
Global Hint Resolve
  GEL_policy_is_reflexive
  GEL_policy_is_transitive
  GEL_policy_is_total
  GEL_policy_not_hep_priority_point_order
  GEL_respects_sequential_tasks
  : basic_rt_facts.



(** In this section, we prove that in a schedule following
    the GEL policy, tasks are always sequential. *)
Section SequentialTasks.

  (** Consider any type of tasks and jobs. *)
  Context `{Task : TaskType} {Job : JobType}
    `{JobTask Job Task} `{PriorityPoint Task} {Arrival : JobArrival Job}.

  (** Assume GEL scheduling. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_policy_is_GEL : policy_is_GEL JLFP.

  (** Consider jobs with execution costs ... *)
  Context `{JobCost Job}.

  (** ... and any valid  arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** Allow for any uniprocessor model ... *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.

  (** Next, consider any schedule of the arrival sequence, ... *)
  Variable sched : schedule PState.

  (** ...allow for any work-bearing notion of job readiness, ... *)
  Context `{!JobReady Job PState}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid w.r.t. said work-bearing
      readiness model. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Next, we assume that the schedule respects the scheduling policy at
      every preemption point. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** To prove sequentiality, we use the lemma
      [early_hep_job_is_scheduled]. Clearly, under the GEL priority
      policy, jobs satisfy the conditions described by the lemma
      (i.e., given two jobs [j1] and [j2] from the same task, if [j1]
      arrives earlier than [j2], then [j1] always has a higher
      priority than job [j2], and hence completes before [j2]);
      therefore GEL implies the [sequential_tasks] property. *)
  Lemma GEL_implies_sequential_tasks :
    sequential_tasks arr_seq sched.
  Proof.
    move => j1 j2 t ARR1 ARR2 /eqP SAME LT.
    apply: early_hep_job_is_scheduled => //.
    rewrite always_higher_priority_jlfp.
    apply/andP; split.
    - apply: GEL_policy_earlier_priority_point => //.
      by rewrite /job_priority_point/jpp_from_tpp SAME; lia.
    - apply/negP => HEP.
      apply GEL_policy_priority_point_order in HEP => //.
      by move: HEP; rewrite /job_priority_point/jpp_from_tpp SAME; lia.
  Qed.

End SequentialTasks.
