Require Export prosa.analysis.abstract.restricted_supply.abstract_seq_rta.
Require Export prosa.analysis.abstract.restricted_supply.iw_readiness.
Require Export prosa.analysis.definitions.sbf.busy.
Require Export prosa.analysis.definitions.workload.bounded.

(** * Task Intra-Supply Interference is Bounded *)

(** In this file, we define the task intra-supply IBF [task_intra_IBF] for
    readiness-aware instantiation of Interference and Interfering Workload. *)
Section TaskIntraInterferenceIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context {Cost : JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.

  (** Consider any kind of fully supply-consuming unit-supply uniprocessor
      model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider any definition of job readiness. *)
  Context `{!JobReady Job PState}.

  (** Consider any JLFP policy that is reflexive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** We also assume that the policy respects sequential tasks. *)
  Hypothesis H_respects_sequential_tasks : policy_respects_sequential_tasks JLFP.

  (** Consider any valid arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and a schedule of this arrival sequence. *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** Consider a readiness-aware definition of interference. *)
  #[local] Instance rs_jlfp_interference : Interference Job :=
    rs_readiness_jlfp_interference arr_seq sched.

  (** Consider a readiness-aware definition of interfering workload. *)
  #[local] Instance rs_jlfp_interfering_workload : InterferingWorkload Job :=
    rs_readiness_jlfp_interfering_workload arr_seq sched.

  (** Let [tsk] be any task to be analyzed. *)
  Variable tsk : Task.

  (** Assume that there exists a bound on the service inversion experienced by
      any job of task [tsk]. *)
  Variable service_inversion_bound : duration -> duration.
  Hypothesis H_service_inversion_is_bounded :
    service_inversion_is_bounded arr_seq sched service_inversion_bound.

  (** Assume that there exists a bound on the higher-or-equal-priority workload
      from tasks different from [tsk]. *)
  Variable athep_workload_bound : duration -> duration -> duration.
  Hypothesis H_workload_is_bounded :
    athep_workload_is_bounded arr_seq sched tsk athep_workload_bound.

  (** Assume that we have a bound on readiness interference. *)
  Variable readiness_interference_bound : duration -> duration -> duration.
  Hypothesis H_readiness_interference_bounded :
    readiness_interference_is_bounded arr_seq sched readiness_interference_bound.

  (** Finally, we define the interference-bound function ([task_intra_IBF]). *)
  Definition task_intra_IBF (A R : duration) :=
    athep_workload_bound A R + service_inversion_bound A + readiness_interference_bound A R.

  (** Next, we prove that [task_intra_IBF] is indeed an interference bound. *)
  Lemma instantiated_task_intra_interference_is_bounded :
    task_intra_interference_is_bounded_by arr_seq sched tsk task_intra_IBF.
  Proof.
    move => t1 t2 Δ j ARR TSK BUSY LT NCOMPL A OFF.
    move: (OFF _ _ BUSY) => EQA; subst A.
    have [ZERO|POS] := posnP (@job_cost _ Cost j).
    { by exfalso; rewrite /completed_by ZERO in NCOMPL. }
    eapply leq_trans; first eapply cumulative_task_interference_split => //.
    rewrite /task_intra_IBF leq_add //; last first.
    { apply leq_trans with (cumulative_readiness_interference arr_seq sched j t1 (t1 + Δ));
        first by apply leq_sum_seq => ? ? ?; lia.
      apply H_readiness_interference_bounded with (t2 := t2) => //=.
      by move: BUSY => [? ?]. }
    { rewrite leq_add //=.
      { erewrite cumulative_i_thep_eq_service_of_othep; eauto 2 => //; last first.
        { rewrite instantiated_quiet_time_equivalent_quiet_time => //; apply BUSY. }
        apply: leq_trans.
        { by apply service_of_jobs_le_workload => //; apply unit_supply_is_unit_service. }
        { by apply H_workload_is_bounded => //; apply: abstract_busy_interval_classic_quiet_time => //. } }
      { apply leq_trans with (cumulative_service_inversion arr_seq sched j t1 t2); last first.
        { apply H_service_inversion_is_bounded => //=.
          by move: BUSY => [? ?]. }
        by rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + Δ)) //= leq_addr. } }
  Qed.

End TaskIntraInterferenceIsBounded.
