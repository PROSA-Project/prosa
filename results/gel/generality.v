From mathcomp Require Import eqtype ssrnat seq path fintype bigop.
Require Export prosa.util.int.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.model.priority.gel.
Require Export prosa.model.priority.edf.
Require Export prosa.model.priority.fifo.
Require Import prosa.model.task.absolute_deadline.

(** * Generality of GEL *)

(** In the following, we make some formal remarks on the obvious generality of
    GEL. *)

(** We begin with the general setup. *)
Section GeneralityOfGEL.

  (** Consider any type of tasks with relative priority points... *)
  Context  {Task : TaskType} `{PriorityPoint Task}.

  (** ... and jobs of these tasks. *)
  Context  {Job : JobType} `{JobTask Job Task}.

  (** Conceptually, the results in this module should hold for any processor
      model. However, due to legacy limitations related to priority-policy
      compliance that yet need to be fixed, we currently can state the
      generality of GEL only for ideal uniprocessor schedules. *)
  Let PState := ideal.processor_state Job.

  (** Suppose the jobs have arrival times, costs, any preemption model, and any
      readiness model. *)
  Context {Arrival : JobArrival Job} {Cost : JobCost Job} `{JobPreemptable Job}
    `{@JobReady Job PState Cost Arrival}.

  (** ** GEL Generalizes EDF *)

  (** First, let us consider EDF, the namesake of GEL, which by design it
      trivially generalizes. *)

  Section GELGeneralizesEDF.

    (** Suppose the tasks have relative deadlines. *)
    Context `{TaskDeadline Task}.

    (** If each task's priority point is set to its relative deadline ... *)
    Hypothesis H_priority_point :
      forall tsk,
        task_priority_point tsk = task_deadline tsk.

    (** ... then the GEL policy reduces to EDF. *)
    Remark gel_generalizes_edf :
      forall sched  arr_seq,
        respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task)
        <-> respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job).
    Proof.
      by move=> sched arr_seq
         ; split => RESPECTED j j' t ARR PT BL SCHED
         ; move: (RESPECTED j j' t ARR PT BL SCHED)
         ; rewrite /hep_job/hep_job_at
                   /GEL/job_priority_point
                   /EDF/job_deadline/job_deadline_from_task_deadline
                   /JLFP_to_JLDP/hep_job
                   !H_priority_point
         ; lia.
    Qed.
  End GELGeneralizesEDF.

  (** ** GEL Generalizes FIFO *)

  (** GEL similarly generalizes FIFO in a trivial manner. *)
  Section GELGeneralizesFIFO.

    (** If each task's priority point is set to zero ... *)
    Hypothesis H_priority_point :
      forall tsk,
        task_priority_point tsk = 0.

    (** ... then the GEL policy reduces to FIFO. *)
    Remark gel_generalizes_fifo :
      forall sched  arr_seq,
        respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task)
        <-> respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).
    Proof.
      by move=> sched arr_seq
         ; split => RESPECTED j j' t ARR PT BL SCHED
         ; move: (RESPECTED j j' t ARR PT BL SCHED)
         ; rewrite /hep_job/hep_job_at
                   /GEL/job_priority_point
                   /FIFO
                   /JLFP_to_JLDP/hep_job
                   !H_priority_point
         ; lia.
    Qed.
  End GELGeneralizesFIFO.

End GeneralityOfGEL.

