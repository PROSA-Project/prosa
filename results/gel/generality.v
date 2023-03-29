From mathcomp Require Import eqtype ssrnat seq path fintype bigop.
Require Export prosa.util.int.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.model.priority.gel.
Require Export prosa.model.priority.fifo.
Require Export prosa.model.priority.edf.
Require Import prosa.model.task.absolute_deadline.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.facts.model.sequential.


(** * Generality of GEL *)

(** In the following, we make some formal remarks on the obvious generality of
    GEL w.r.t. EDF and FIFO, and the somewhat less obvious conditional
    generality w.r.t. fixed-priority scheduling. *)

(** We begin with the general setup. *)
Section GeneralityOfGEL.

  (** Consider any type of tasks with relative priority points... *)
  Context  {Task : TaskType} `{PriorityPoint Task}.

  (** ... jobs of these tasks, and ... *)
  Context  {Job : JobType} `{JobTask Job Task}.

  (** ... any processor model. *)
  Context {PState : ProcessorState Job}.

  (** Suppose the jobs have arrival times and costs, and allow for any preemption
      and readiness models. *)
  Context {Arrival : JobArrival Job} {Cost : JobCost Job}
    `{JobPreemptable Job} {JR: @JobReady Job PState Cost Arrival}.

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

  (** ** GEL Conditionally Generalizes FP *)

  (** We now turn to fixed-priority scheduling. GEL does not generalize
      fixed-priority scheduling in all circumstances. However, if priority
      points are carefully chosen, tasks are sequential, and fixed task
      priorities are unique, then GEL can be equivalent to a given arbitrary
      fixed-priority policy. *)
  Section GELConditionallyGeneralizesFP.

    (** Consider any given fixed-priority policy that is both reflexive and
        total... *)
    Variable fp : FP_policy Task.
    Hypothesis H_reflexive : reflexive_task_priorities fp.
    Hypothesis H_total : total_task_priorities fp.

    (** ... and an arbitrary valid arrival sequence. *)
    Variable arr_seq : arrival_sequence Job.
    Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

   (** In the following, we assume a sequential readiness model: a
       later-arriving job of a task is ready only if all prior jobs are
       complete. *)
    Hypothesis H_sequential : sequential_readiness JR arr_seq.

    (** For ease of reference, we refer to the difference between the relative
        priority points of two given tasks as [pp_delta]. *)
    Definition pp_delta tsk tsk' :=
      (task_priority_point tsk' - task_priority_point tsk)%R.

    (** Before we tackle the conditional equivalence, we first establish a
        helper lemma on the priority of backlogged jobs that sits at the core of
        the argument. *)
    Section GELPrioOfBackloggedJob.

      (** Consider two arbitrary jobs [j] and [j'], ... *)
      Variable j j' : Job.

      (** ... their corresponding tasks [tsk] and [tsk'], ... *)
      Let tsk := job_task j.
      Let tsk' := job_task j'.

      (** ...an arbitrary schedule, ... *)
      Variable sched : schedule PState.

      (** ... and an arbitrary point in time [t]. *)
      Variable t : instant.

      (** Suppose the relative priority point of [tsk'] is larger than that of
          [tsk] ... *)
      Hypothesis H_delta_pos : (pp_delta tsk tsk' >= 0)%R.

      (** ... and that the difference between the priority points of the two
          tasks bounds the maximum response time of [j'] in [sched]. *)
      Hypothesis H_rt_bound :
        job_response_time_bound sched j' `|pp_delta tsk tsk'|.

      (** For clarity, recall the definition of "higher-or-equal job priority"
          under GEL and refer to it as [gel_hep_job]. *)
      Let gel_hep_job := @hep_job _ (GEL Job Task).

      (** We are now ready to state the auxiliary lemma: under the above
          assumptions, if [j] has arrived by time [t] and [j'] is backlogged,
          then [j]'s priority under GEL is higher than or equal to [j']'s
          priority. *)
      Lemma backlogged_job_has_lower_gel_prio :
        has_arrived j t ->
        backlogged sched j' t ->
        gel_hep_job j j'.
      Proof.
        move=> ARRIVED BL'.
        rewrite /gel_hep_job/hep_job/GEL/job_priority_point.
        have [|ARR'] := leqP (job_arrival j)
                          (job_arrival j' + `|pp_delta tsk tsk'|);
          first by move: H_delta_pos; rewrite /pp_delta/tsk/tsk'; lia.
        exfalso.
        have INCOMP : ~ completed_by sched j' t
          by apply /negP; apply: backlogged_implies_incomplete.
        have: completed_by sched j' t => [|//].
        move: H_rt_bound; rewrite /job_response_time_bound.
        apply: completion_monotonic.
        by move: ARRIVED; rewrite /has_arrived; lia.
      Qed.

    End GELPrioOfBackloggedJob.

    (** With the auxiliary lemma in place, we now state the main assumptions
        under which conditional generality can be shown. *)

    (** Firstly, we require that the priorities of tasks that feature in the
        schedule are unique. That is, no two tasks that contribute jobs to the
        arrival sequence share a fixed priority. *)
    Hypothesis H_unique_fixed_priorities :
      forall j j',
        arrives_in arr_seq j ->
        arrives_in arr_seq j' ->
        ~~ same_task j j' ->
        hep_task (job_task j) (job_task j') ->
        hp_task (job_task j) (job_task j').

    (** Secondly, we require that the assigned relative priority points are
        monotonic with decreasing task priority: the relative priority point
        offset of a lower-priority task must not be less than that of any
        higher-priority task (that features in the arrival sequence). *)
    Hypothesis H_hp_delta_pos :
      forall j j',
        arrives_in arr_seq j ->
        arrives_in arr_seq j' ->
        hp_task (job_task j) (job_task j') ->
        (pp_delta (job_task j) (job_task j') >= 0)%R.

    (** To state the third and final assumption, we require an arbitrary, valid
        schedule to be given. *)
    Variable sched : schedule PState.
    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    (** Thirdly, we require that the difference in relative priority points
        between a higher- and lower-priority task exceeds the maximum response
        time of the lower-priority task in the given schedule. In other words,
        the priority points of lower-priority tasks must be chosen to be "large
        enough" to be sufficiently far enough in the future to avoid interfering
        with any concurrently pending jobs of higher-priority tasks. *)
    Hypothesis H_hp_delta_rtb :
      forall j j',
        arrives_in arr_seq j ->
        arrives_in arr_seq j' ->
        hp_task (job_task j) (job_task j') ->
        job_response_time_bound sched j' `|pp_delta (job_task j) (job_task j')|.

    (** Under the three conditions stated above, GEL generalizes the given FP
        policy. *)
    Theorem gel_conditionally_generalizes_fp :
      respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task)
      <-> respects_FP_policy_at_preemption_point arr_seq sched fp.
    Proof.
      have SEQ: sequential_tasks arr_seq sched
        by eapply sequential_tasks_from_readiness; rt_auto.
      split=> RESPECTED j' j t ARR PT BL SCHED; last first.
      { have [SAME|DIFF] := boolP (same_task j' j).
        {
          have [LT_ARR|] := ltnP (job_arrival j') (job_arrival j).
          { exfalso.
            have DIFF: ~ same_task j' j; last by contradiction.
            apply/negP/sequential_tasks_different_tasks; rt_eauto.
            exact: backlogged_implies_incomplete. }
          { rewrite /hep_job_at/GEL/JLFP_to_JLDP/hep_job/job_priority_point.
            by move: SAME; rewrite /same_task => /eqP ->; lia. } }
        { have HFP: hp_task (job_task j) (job_task j').
          { apply: H_unique_fixed_priorities; rt_eauto;
              first by rewrite same_task_sym.
            move: (RESPECTED j' j t ARR PT BL SCHED).
            by rewrite /hep_job_at/FP_to_JLFP/JLFP_to_JLDP/hep_job. }
          by apply: (backlogged_job_has_lower_gel_prio _ _ sched t); rt_eauto.
        } }
      { rewrite /hep_job_at/FP_to_JLFP/JLFP_to_JLDP/hep_job.
        case: (boolP (same_task j' j)); first by rewrite /same_task => /eqP ->.
        move=> DIFF; apply: contraT; rewrite not_hep_hp_task // => HFP.
        have FIN: completed_by sched j (job_arrival j + `|pp_delta (job_task j') (job_task j)|)
          by apply: H_hp_delta_rtb; rt_eauto.
        move: (RESPECTED j' j t ARR PT BL SCHED).
        rewrite /hep_job_at/GEL/JLFP_to_JLDP/hep_job/job_priority_point => PRIO.
        have POS: (pp_delta (job_task j') (job_task j) >= 0)%R
                    by apply: H_hp_delta_pos; rt_eauto.
        have: completed_by sched j t; last first.
        { have: ~ completed_by sched j t => [|//].
          by apply/negP/scheduled_implies_not_completed; rt_eauto. }
        { apply: completion_monotonic; last exact: FIN.
          move: POS; rewrite /pp_delta.
          have: job_arrival j' <= t; last lia.
          by rewrite -/(has_arrived j' t); rt_eauto. } }
    Qed.

  End GELConditionallyGeneralizesFP.

End GeneralityOfGEL.

