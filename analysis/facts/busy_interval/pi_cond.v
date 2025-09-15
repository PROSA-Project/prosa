Require Export prosa.analysis.facts.busy_interval.pi.

(** This file relates the general notion of [cumulative_priority_inversion] with
    the more specialized notion [cumulative_priority_inversion_cond]. *)

Section CondPI.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** Consider any arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and any ideal uniprocessor schedule of this arrival sequence. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uni : uniprocessor_model PState.
  Variable sched : schedule PState.

  (** Consider a JLFP policy that indicates a higher-or-equal priority relation,
      and assume that the relation is reflexive and transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** Consider a valid preemption model with known maximum non-preemptive
      segment lengths. *)
  Context `{TaskMaxNonpreemptiveSegment Task} `{JobPreemptable Job}.
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** Further, allow for any work-bearing notion of job readiness. *)
  Context `{@JobReady Job PState Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** We assume that the schedule is valid. *)
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and the schedule respects the scheduling policy at every preemption point. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** Consider any job [j] of [tsk] with positive job cost. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy interval prefix <<[t1, t2)>> of job j. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval_prefix :
    busy_interval_prefix arr_seq sched j t1 t2.

  (** We establish a technical rewriting lemma that allows us to replace
      [cumulative_priority_inversion] with
      [cumulative_priority_inversion_cond] by exploiting the observation
      that a single job remains scheduled throughout the interval in which job
      [j] suffers priority inversion. *)
  Lemma cum_task_pi_eq :
    forall (jlp : Job) (P : pred Job),
      scheduled_at sched jlp t1 ->
      P jlp ->
        cumulative_priority_inversion arr_seq sched j t1 t2
        = cumulative_priority_inversion_cond arr_seq sched j P t1 t2.
  Proof.
    move=> jlp P SCHED Pjlp.
    apply: eq_big_nat => // t /andP [t1t tt2].
    apply/eqP; rewrite nat_of_bool_eq; apply/eqP/andb_id2l => NSCHED.
    have suff:
      forall j',
        j' \in scheduled_jobs_at arr_seq sched t ->
        ~~ hep_job j' j ->
        P j'.
    { move=> SUFF.
      apply: eq_in_has => j' => SCHED'.
      have [_|NHEP] := boolP (hep_job j' j); first by rewrite andFb.
      by rewrite andTb SUFF. }
    { apply => j' SCHED' NHEP.
      move: SCHED'; rewrite scheduled_jobs_at_iff // => SCHED''.
      have PI: priority_inversion arr_seq sched j t by apply /uni_priority_inversion_P.
      have j't1: scheduled_at sched j' t1
        by apply: (pi_job_remains_scheduled arr_seq) =>//; apply /andP.
      have -> // : j' = jlp.
      { apply /eqP/contraT => NEQ; move: SCHED; apply /contraLR => _.
        by apply scheduled_job_at_neq with (j:= j'). } }
  Qed.

End CondPI.
