Require Export prosa.analysis.facts.preemption.job.nonpreemptive.
Require Export prosa.model.task.preemption.fully_nonpreemptive.

(** * Platform for Fully Non-Preemptive Model *)

(** In this section, we prove that instantiation of functions
    [job_preemptable] and [task_max_nonpreemptive_segment] to the fully
    non-preemptive model indeed defines a valid preemption model with
    bounded non-preemptive regions. *)
Section FullyNonPreemptiveModel.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Assume a fully non-preemptive task model. *)
  #[local] Existing Instance fully_nonpreemptive_job_model.
  #[local] Existing Instance fully_nonpreemptive_task_model.
  #[local] Existing Instance fully_nonpreemptive_rtc_threshold.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.


  (** Next, consider any non-preemptive unit-service schedule of the arrival sequence ... *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_unit_service: unit_service_proc_model PState.
  Variable sched : schedule PState.
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule  sched.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Then we prove that the [fully_nonpreemptive_model] function
      defines a model with bounded non-preemptive regions.*)
  Lemma fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions:
    model_with_bounded_nonpreemptive_segments arr_seq.
  Proof.
    have F: forall n, n = 0 \/ n > 0  by intros n; destruct n; [left | right].
    intros j; split.
    { rewrite /job_respects_max_nonpreemptive_segment; eauto 2.
      erewrite job_max_nps_is_job_cost; eauto 2.
    }
    move => progr /andP [_ GE].
    move: (F (progr)) => [EQ | GT].
    { exists progr; split.
        - by apply/andP; split; [|rewrite leq_addr].
        - rewrite /job_preemptable /fully_nonpreemptive_job_model.
          by apply/orP; left; rewrite EQ.
    }
    { exists (maxn progr (job_cost j)).
      have POS: 0 < job_cost j by apply leq_trans with progr.
      split.
      { apply/andP; split; first by rewrite leq_maxl.
        erewrite job_max_nps_is_job_cost; eauto 2; rewrite addnBA; last eauto 2.
        rewrite geq_max; apply/andP; split.
          - rewrite -addnBA; last by eauto 2.
              by rewrite leq_addr.
          - by rewrite addnC -addnBA // leq_addr.
      }
      { apply/orP; right.
        rewrite eqn_leq; apply/andP; split.
        - by rewrite geq_max; apply/andP; split.
        - by rewrite leq_max; apply/orP; right.
      }
    }
  Qed.

  (** Which together with lemma [valid_fully_nonpreemptive_model]
      gives us the fact that [fully_nonpreemptive_model] defined a valid
      preemption model with bounded non-preemptive regions. *)
  Corollary fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.
  Proof.
    split.
    - by apply valid_fully_nonpreemptive_model.
    - by apply fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions.
  Qed.

End FullyNonPreemptiveModel.

(** We add the above lemma into a "Hint Database" basic_rt_facts, so Coq will be able to apply them automatically. *)
Global Hint Resolve
     valid_fully_nonpreemptive_model
     fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions
     fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions : basic_rt_facts.
