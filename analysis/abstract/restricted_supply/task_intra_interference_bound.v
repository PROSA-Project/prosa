Require Export prosa.analysis.abstract.restricted_supply.abstract_seq_rta.
Require Export prosa.analysis.abstract.restricted_supply.iw_instantiation.
Require Export prosa.analysis.definitions.sbf.busy.
Require Export prosa.analysis.facts.blocking_bound_fp.
Require Export prosa.analysis.definitions.workload.bounded.


(** * Task Intra-Supply Interference is Bounded *)

(** In this file, we define the task intra-supply IBF [task_intra_IBF]
    assuming that we have two functions: one bounding service
    inversion and the other bounding the higher-or-equal-priority
    workload (w.r.t. a job under analysis). We then prove that
    [task_intra_IBF] indeed bounds the cumulative task intra-supply
    interference. *)
Section TaskIntraInterferenceIsBounded.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context {Cost : JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.

  (** Consider any kind of fully supply-consuming unit-supply
      uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_unit_supply_proc_model : unit_supply_proc_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider a JLFP policy that indicates a higher-or-equal-priority
      relation, and assume that the relation is reflexive.

      Note that we do not relate the JLFP policy with the
      scheduler. However, we define functions for Interference and
      Interfering Workload that actively use the concept of
      priorities. We require the JLFP policy to be reflexive, so a job
      cannot cause lower-priority interference (i.e. priority
      inversion) to itself. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** We also assume that the policy respects sequential tasks,
      meaning that later-arrived jobs of a task don't have higher
      priority than earlier-arrived jobs of the same task. *)
  Hypothesis H_JLFP_respects_sequential_tasks : policy_respects_sequential_tasks JLFP.

  (** Consider any valid arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and a schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival nor after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** We say that job [j] incurs interference at time [t] iff it
      cannot execute due to (1) the lack of supply at time [t], (2)
      service inversion (i.e., a lower-priority job receiving service
      at [t]), or a higher-or-equal-priority job receiving service. *)
  #[local] Instance rs_jlfp_interference : Interference Job :=
    rs_jlfp_interference arr_seq sched.

  (** The interfering workload, in turn, is defined as the sum of the
      blackout predicate, service-inversion predicate, and the
      interfering workload of jobs with higher or equal priority. *)
  #[local] Instance rs_jlfp_interfering_workload : InterferingWorkload Job :=
    rs_jlfp_interfering_workload arr_seq sched.

  (** Let [tsk] be any task to be analyzed. *)
  Variable tsk : Task.

  (** Assume that there exists a bound on the length of any service
      inversion experienced by any job of task [tsk]. *)
  Variable service_inversion_bound : duration -> duration.
  Hypothesis H_service_inversion_is_bounded :
    service_inversion_is_bounded_by
     arr_seq sched tsk service_inversion_bound.

  (** Assume that there exists a bound on the higher-or-equal-priority
      (w.r.t. a [tsk]'s job) workload of tasks different from [tsk]. *)
  Variable athep_workload_bound : (* Δ *) duration -> duration.
  Hypothesis H_workload_is_bounded :
    athep_workload_is_bounded arr_seq sched tsk athep_workload_bound.

  (** Finally, we define the interference-bound function ([task_intra_IBF]). *)
  Definition task_intra_IBF (A R : duration) :=
    service_inversion_bound A + athep_workload_bound R.

  (** Next, we prove that [task_intra_IBF] is indeed an interference bound. *)
  Lemma instantiated_task_intra_interference_is_bounded :
    task_intra_interference_is_bounded_by
      arr_seq sched tsk task_intra_IBF.
  Proof.
    move => t1 t2 Δ j ARR TSK BUSY LT NCOMPL A OFF.
    move: (OFF _ _ BUSY) => EQA; subst A.
    have [ZERO|POS] := posnP (@job_cost _ Cost j).
    { by exfalso; rewrite /completed_by ZERO in NCOMPL. }
    eapply leq_trans; first by eapply cumulative_task_interference_split => //.
    rewrite /task_intra_IBF leq_add//.
    { apply leq_trans with (cumulative_service_inversion arr_seq sched j t1 (t1 + Δ)); first by done.
      apply leq_trans with (cumulative_service_inversion arr_seq sched j t1 t2); last first.
      { apply: H_service_inversion_is_bounded; eauto 2 => //.
        apply abstract_busy_interval_classic_busy_interval_prefix => //. }
      by rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + Δ)) //= leq_addr. }
    { erewrite cumulative_i_thep_eq_service_of_othep; eauto 2 => //; last first.
      { by apply instantiated_quiet_time_equivalent_quiet_time => //; apply BUSY. }
      apply: leq_trans.
      { by apply service_of_jobs_le_workload => //; apply unit_supply_is_unit_service. }
      { apply H_workload_is_bounded => //; apply: abstract_busy_interval_classic_quiet_time => //. }
    }
  Qed.

End TaskIntraInterferenceIsBounded.
