Require Import prosa.model.priority.edf.
Require Import prosa.model.task.absolute_deadline.

(** In this section, we prove a few properties about EDF policy. *)
Section PropertiesOfEDF.

  (** Consider any type of tasks with relative deadlines ... *)
  Context {Task : TaskType}.
  Context `{TaskDeadline Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** EDF respects sequential tasks hypothesis. *)
  Lemma EDF_respects_sequential_tasks:
    policy_respects_sequential_tasks.
  Proof.
    intros j1 j2 TSK ARR.
    move: TSK => /eqP TSK.
    unfold hep_job, EDF, job_deadline, job_deadline_from_task_deadline; rewrite TSK.
      by rewrite leq_add2r.
  Qed.

End PropertiesOfEDF.

(** We add the above lemma into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply it automatically. *)
Global Hint Resolve EDF_respects_sequential_tasks : basic_rt_facts.


Require Export prosa.model.task.sequentiality.
Require Export prosa.analysis.facts.busy_interval.priority_inversion.
Require Export prosa.analysis.facts.priority.sequential.

(** In this section, we prove that EDF priority policy 
    implies that tasks are sequential. *)
Section SequentialEDF.  

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.

  (** ... with a bound on the maximum non-preemptive segment length.
      The bound is needed to ensure that, at any instant, it always 
      exists a subsequent preemption time in which the scheduler can, 
      if needed, switch to another higher-priority job. *)
  Context `{TaskMaxNonpreemptiveSegment Task}.
  
  (** Further, consider any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** Next, consider any ideal uni-processor schedule of this arrival sequence, ... *)
  Variable sched : schedule (ideal.processor_state Job).
  
  (** ... allow for any work-bearing notion of job readiness, ... *)
  Context `{@JobReady Job (ideal.processor_state Job) Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is valid. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  
  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.

  (** Next, we assume that the schedule respects the policy defined by
      the [job_preemptable] function (i.e., jobs have bounded
      non-preemptive segments). *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).

  (** To prove sequentiality, we use lemma
      [early_hep_job_is_scheduled]. Clearly, under the EDF priority
      policy, jobs satisfy the conditions described by the lemma
      (i.e., given two jobs [j1] and [j2] from the same task, if [j1]
      arrives earlier than [j2], then [j1] always has a higher
      priority than job [j2], and hence completes before [j2]);
      therefore EDF implies sequential tasks. *)
  Lemma EDF_implies_sequential_tasks:
    sequential_tasks arr_seq sched.
  Proof.
    intros ? ? ? ARR1 ARR2 SAME LT.
    eapply early_hep_job_is_scheduled => //; rt_eauto.
    clear t; intros ?.
    move: SAME => /eqP SAME.
    apply /andP.
    rewrite /hep_job_at  /JLFP_to_JLDP /hep_job /edf.EDF /job_deadline
      /absolute_deadline.job_deadline_from_task_deadline SAME.
    by lia.
  Qed.

End SequentialEDF.
