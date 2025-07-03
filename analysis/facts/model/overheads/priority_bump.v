Require Export prosa.model.readiness.basic.
Require Export prosa.model.processor.overheads.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.priority.sequential.
Require Export prosa.analysis.facts.model.overheads.schedule.
Require Export prosa.analysis.definitions.overheads.priority_bump.


(** In this section, we prove several properties of the notion of a priority bump. *)
Section PriorityBump.

  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority
      relation, and assume that this relation is reflexive and
      transitive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.
  Hypothesis H_priority_is_transitive : transitive_job_priorities JLFP.

  (** We assume the basic model of readiness. *)
  #[local] Existing Instance basic_ready_instance.

  (** Consider any valid arrival sequence... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any explicit-overhead uni-processor schedule of this
      arrival sequence. *)
  Variable sched : schedule (overheads.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Assume that the preemption model is valid. *)
  Context `{JobPreemptable Job}.
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.

  (** Assume that the schedule respects the JLFP policy. *)
  Hypothesis H_respects_policy :
    respects_JLFP_policy_at_preemption_point arr_seq sched JLFP.

  (** If a priority bump occurs at time [t], then [t] is a preemption time. *)
  Lemma priority_bump_implies_preemption_time :
    forall (t : instant),
      priority_bump sched t ->
      preemption_time arr_seq sched t.
  Proof.
    move=> [ | to]; rewrite /priority_bump => PB.
    { rewrite //= in PB; destruct (scheduled_job sched 0) eqn:SCHED1 => //.
      by rewrite //= H_priority_is_reflexive in PB.
    }
    have UNI := @overheads_proc_model_is_a_uniprocessor_model Job.
    rewrite -pred_Sn in PB.
    destruct (scheduled_job sched to) as [j1 | ] eqn:SCHED1,
          (scheduled_job sched to.+1) as [j2 | ] eqn:SCHED2 =>//.
    { have [/eqP EQ|NEQ] := boolP (j1 == j2).
      { by subst; rewrite H_priority_is_reflexive in PB. }
      { apply scheduled_at_iff_scheduled_job in SCHED1, SCHED2; apply first_moment_is_pt with (j := j2) => //.
        apply/negP => SCHED; move: NEQ => /negP NEQ; apply: NEQ; apply/eqP.
        by apply: overheads_proc_model_is_a_uniprocessor_model => //.
      }
    }
    { apply scheduled_at_iff_scheduled_job in SCHED2; apply first_moment_is_pt with (j := j2) => //.
      by apply/negP => SCHED; apply scheduled_at_iff_scheduled_job in SCHED; rewrite SCHED in SCHED1.
    }
  Qed.

  (** Consider an arbitrary job [j] with positive cost. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider any busy-interval prefix <<[t1, t2)>> of job [j]. *)
  Variables t1 t2 : instant.
  Hypothesis H_busy_interval_prefix : busy_interval_prefix arr_seq sched j t1 t2.

  (** A priority bump within a busy-interval prefix can only be caused
      by a job that arrived within the same busy-interval prefix. *)
  Lemma priority_bump_implies_hp_arrival_in_prefix :
    forall (t t_arr : instant),
      t1 <= t ->
      t < t_arr ->
      t_arr <= t2 ->
      priority_bump sched t ->
      exists jhp,
        scheduled_at sched jhp t
        /\ jhp \in arrivals_between arr_seq t1 t_arr.
  Proof.
    move=> t t_arr NEQ1 NEQ2 NEQ3 PB.
    apply priority_bump_implies_preemption_time in PB.
    edestruct not_quiet_implies_exists_scheduled_hp_job_at_preemption_point as [jhp [ARR [HEP SCHED ]]] =>//.
    { lia. }
    exists jhp; split; try done.
    apply arrived_between_implies_in_arrivals => //; apply/andP; split.
    { by move: ARR => /andP []; lia. }
    { apply valid_schedule_implies_jobs_must_arrive_to_execute in H_valid_schedule.
      apply H_valid_schedule in SCHED.
      by unfold has_arrived in *; lia.
    }
  Qed.

  (** In the following, we assume that the JLFP policy corresponds to
      FIFO: a job has higher or equal priority if and only if it
      arrived earlier. *)
  Hypothesis H_JLFP_is_FIFO : forall j1 j2, hep_job j1 j2 = (job_arrival j1 <= job_arrival j2).

  (** Under the FIFO policy, no priority bumps occur during <<(t1, t2]>>
      since jobs are scheduled in arrival order and thus
      priorities never increase. *)
  Lemma no_priority_bumps_in_fifo :
    forall (t : instant),
      t1 < t <= t2 ->
      ~~ priority_bump sched t.
  Proof.
    move=> t NEQ; apply/negP => PB; unfold priority_bump in *.
    destruct (scheduled_job sched t.-1) as [j1 | ] eqn:SCHED1;
      destruct (scheduled_job sched t) as [j2 | ] eqn:SCHED2; try done; last first.
    { edestruct job_scheduled_in_busy_interval_prefix with (t := t.-1) as [js SCHED] => //; first by lia.
      apply scheduled_at_iff_scheduled_job in SCHED.
      by rewrite SCHED in SCHED1; inversion SCHED1.
    }
    { rewrite H_JLFP_is_FIFO -ltnNge in PB.
      apply scheduled_at_iff_scheduled_job in SCHED1.
      apply scheduled_at_iff_scheduled_job in SCHED2.
      eapply early_hep_job_is_scheduled with (JLFP := hep_job) in PB => //; last first.
      { by intros ?; rewrite /hep_job_at /JLFP_to_JLDP //= !H_JLFP_is_FIFO; lia. }
      eapply completion_monotonic in PB.
      { by apply completed_implies_not_scheduled in PB => //; erewrite SCHED2 in PB. }
      { lia. }
    }
  Qed.

End PriorityBump.
