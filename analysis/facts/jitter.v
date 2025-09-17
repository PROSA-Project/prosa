Require Export prosa.analysis.facts.delay_propagation.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.model.readiness.basic.
Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.definitions.schedulability.

(** * Propagation of Release Jitter in Arrival Curves *)

(** In this module, we prove correct an approach to "hiding" release jitter by
    "folding" it into arrival curves. *)
Section JitterPropagationFacts.

  (** Consider any type of tasks described by arrival curves and the
      corresponding jobs. *)
  Context {Task : TaskType} {arrival_curve : MaxArrivals Task}
          {Job : JobType} `{JobTask Job Task}.

  (** Let [original_arrival] denote each job's _actual_ arrival time ... *)
  Context {original_arrival : JobArrival Job}.

  (** ... and suppose the jobs are affected by bounded release jitter. *)
  Context `{TaskJitter Task} `{JobJitter Job}.

  (** In the following, consider an arbitrary valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Recall the induced "release curve" and associated definitions. *)
  #[local] Existing Instance release_as_arrival.
  #[local] Existing Instance release_curve.

  (** In the following, we let [rel_seq] denote the induced "release curve". *)
  Let rel_seq := release_sequence arr_seq.

  (** Suppose we are given a set of tasks ... *)
  Variable ts : seq Task.

  (** ... with valid bounds on release jitter. *)
  Hypothesis H_valid_jitter : valid_jitter_bounds ts.

  (** ** Restated General Properties *)

  (** We begin by restating general properties of delay propagation, specialized
      to the case of jitter propagation. *)

  (** The arrival and release sequences contain an identical set of jobs. *)
  Corollary jitter_arrives_in_iff :
    forall j,
      arrives_in arr_seq j <-> arrives_in rel_seq j.
  Proof.
    move=> j; split;
          [ apply: (arrives_in_propagated_if original_arrival release_as_arrival) => //
          | apply: (arrives_in_propagated_only_if original_arrival release_as_arrival) => //
          ]; exact: jitter_arr_seq_mapping_valid.
  Qed.

  (** The induced "release sequence" is valid. *)
  Corollary valid_release_sequence :
    @valid_arrival_sequence _ release_as_arrival rel_seq.
  Proof.
    apply: (valid_propagated_arrival_sequence original_arrival release_as_arrival) => //.
    by apply: jitter_arr_seq_mapping_valid.
  Qed.

  (** If the arrival curve is structurally valid, then so is the induced release
      curve. *)
  Corollary valid_release_curve :
    valid_taskset_arrival_curve ts max_arrivals ->
    valid_taskset_arrival_curve ts release_curve.
  Proof.
    move=> VALID.
    apply: propagated_arrival_curve_valid => tsk IN.
    by move: (VALID tsk IN) => [_ {}].
  Qed.

  (** Furthermore, if the arrival curve correctly bounds arrivals according to
      [arr_seq], then the "release curve" also correctly bounds releases
      according to [rel_seq]. *)
  Corollary release_curve_respected :
    valid_taskset_arrival_curve ts max_arrivals ->
    @taskset_respects_max_arrivals _ _ _ arr_seq arrival_curve ts ->
    @taskset_respects_max_arrivals _ _ _ rel_seq release_curve ts.
  Proof.
    move=> AC VALID.
    apply: (propagated_arrival_curve_respected original_arrival release_as_arrival) => //; try by rewrite map_id.
    - by apply: jitter_delay_mapping_valid.
    - by apply: jitter_arr_seq_mapping_valid.
  Qed.


  (** ** Jitter Propagation Properties *)

  (** Next, we establish validity properties specific to jitter
      propagation. These are needed to apply response-time analysis results. *)

  (** Since the arrival and release sequence describe identical sets of jobs,
      trivially all jobs continue to belong to the tasks in the task set. *)
  Lemma jitter_prop_same_jobs :
      all_jobs_from_taskset arr_seq ts ->
      all_jobs_from_taskset rel_seq ts.
  Proof. by move=> ALL j IN; apply: ALL; rewrite jitter_arrives_in_iff. Qed.

  (** Next, consider an arbitrary schedule of the workload. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** Again, trivially, all jobs in the schedule continue to belong to the
      release sequence. *)
  Lemma jitter_prop_same_jobs' :
      jobs_come_from_arrival_sequence sched arr_seq ->
      jobs_come_from_arrival_sequence sched rel_seq.
  Proof. move=> FROM j t SCHED; rewrite -jitter_arrives_in_iff; exact: FROM. Qed.

  (** Let us now consider the execution costs. *)
  Context `{JobCost Job} `{TaskCost Task}.

  (** Since the set of jobs didn't change, and since release jitter propagation
      does not change execution costs, job costs remain trivially valid. *)
  Lemma jitter_prop_valid_costs :
    arrivals_have_valid_job_costs arr_seq ->
    arrivals_have_valid_job_costs rel_seq.
  Proof.
    move=> VALID j IN.
    apply: VALID.
    by rewrite jitter_arrives_in_iff.
  Qed.

  (** If the given schedule respects release jitter, then it continues to do so
      after we've reinterpreted the release times to be the arrival times. *)
  Lemma jitter_ready_to_execute :
    @jobs_must_be_ready_to_execute _ original_arrival _ sched _ jitter_ready_instance ->
    @jobs_must_be_ready_to_execute _ release_as_arrival _ sched _ basic_ready_instance.
  Proof. move=> RDY j t SCHED; by move: (RDY j t SCHED). Qed.

  (** If the schedule is work-conserving, then it continues to be so after we've
      "hidden" release jitter by reinterpreting release times as arrival
      times. *)
  Theorem jitter_work_conservation :
    @work_conserving _ original_arrival _ _ jitter_ready_instance arr_seq sched ->
    @work_conserving _ release_as_arrival _ _ basic_ready_instance rel_seq sched.
  Proof.
    move=> WC_jit j t ARR_rel /andP [R_rel NSCHED].
    have ARR_arr: arrives_in arr_seq j by rewrite jitter_arrives_in_iff.
    apply: WC_jit; first exact: ARR_arr.
    by apply/andP; split.
  Qed.

  (** If the given schedule is valid w.r.t. to original arrivals, then it
      continues to be valid after reinterpreting release times as arrival
      times. *)
  Lemma jitter_valid_schedule :
    @valid_schedule _ original_arrival _ sched _ jitter_ready_instance arr_seq ->
    @valid_schedule _ release_as_arrival _ sched _ basic_ready_instance rel_seq.
  Proof.
    move => [SRC RDY].
    split.
    - exact: jitter_prop_same_jobs'.
    - exact: jitter_ready_to_execute.
  Qed.

  (** In the following, suppose the given schedule is valid w.r.t. the original
      arrival times and jitter-affected readiness. *)
  Hypothesis H_valid_schedule :
    @valid_schedule _ original_arrival _ sched _ jitter_ready_instance arr_seq.

  (** As one would think, the set of scheduled jobs remains unchanged. For
      technical reasons (dependence of the definition of [scheduled_jobs_at] on
      the arrival sequence), this is a lot less obvious at the Coq level than
      one intuitively might expect. *)
  Lemma jitter_scheduled_jobs_at_equiv :
    forall t j,
      (j \in scheduled_jobs_at rel_seq sched t)
      = (j \in scheduled_jobs_at arr_seq sched t).
  Proof.
    move=> j t.
    have SRC := @valid_schedule_jobs_come_from_arrival_sequence _ _ sched _
                  original_arrival jitter_ready_instance arr_seq H_valid_schedule.
    rewrite [RHS]scheduled_jobs_at_iff; [| |exact: SRC|] => //.
    rewrite (@scheduled_jobs_at_iff _ release_as_arrival); first by done.
    - exact: valid_release_sequence.
    - exact: jitter_prop_same_jobs'.
    - exact
        /(@jobs_must_arrive_to_be_ready _ _ sched _ release_as_arrival basic_ready_instance)
        /jitter_ready_to_execute.
  Qed.

  (** Unsurprisingly, on a uniprocessor, the scheduled job remains unchanged,
      too. Again, this is less straightforward than one might think due to
      technical reasons (type-class resolution). *)
  Lemma jitter_scheduled_job_at_eq :
    forall t,
      uniprocessor_model PState ->
      scheduled_job_at arr_seq sched t = scheduled_job_at rel_seq sched t.
  Proof.
    move=> t UNI.
    have SRC := @valid_schedule_jobs_come_from_arrival_sequence _ _ sched _
                  original_arrival jitter_ready_instance arr_seq H_valid_schedule.
    (* Note: there is a lot of repetition here because the automation chokes on
       the multiple available type-class instances and/or promptly picks the
       wrong ones. Not pretty, but it works. *)
    case SCHED: scheduled_job_at => [j|];
      case SCHED': scheduled_job_at => [j'|]; last by done.
    { move: SCHED => /eqP; rewrite scheduled_job_at_scheduled_at; [| |exact: SRC| |] => // SCHED.
      move: SCHED' => /eqP; rewrite (@scheduled_job_at_scheduled_at _ release_as_arrival).
      - move=> SCHED'.
        by rewrite (UNI j j' sched t).
      - exact: valid_release_sequence.
      - exact: jitter_prop_same_jobs'.
      - exact
          /(@jobs_must_arrive_to_be_ready _ _ sched _ release_as_arrival basic_ready_instance)
            /jitter_ready_to_execute.
      - by [].
    }
    { exfalso.
      move: SCHED => /eqP; rewrite scheduled_job_at_scheduled_at; [| |exact: SRC| |] => //.
      move: SCHED'; rewrite (@scheduled_job_at_none _ release_as_arrival);
        first by move=> NSCHED; apply/negP.
      - exact: valid_release_sequence.
      - exact: jitter_prop_same_jobs'.
      - exact
          /(@jobs_must_arrive_to_be_ready _ _ sched _ release_as_arrival basic_ready_instance)
            /jitter_ready_to_execute. }

    { exfalso.
      move: SCHED; rewrite scheduled_job_at_none; [| |exact: SRC|] => // NSCHED.
      move: SCHED' => /eqP; rewrite (@scheduled_job_at_scheduled_at _ release_as_arrival);
        first by apply/negP.
      - exact: valid_release_sequence.
      - exact: jitter_prop_same_jobs'.
      - exact
          /(@jobs_must_arrive_to_be_ready _ _ sched _ release_as_arrival basic_ready_instance)
            /jitter_ready_to_execute.
      - by []. }
  Qed.

  (** Importantly, the schedule remains FP-policy compliant if it was so to
      begin with, despite the postponed arrival times. *)
  Theorem jitter_FP_compliance `{FP : FP_policy Task} `{JobPreemptable Job} :
    uniprocessor_model PState ->
    @respects_FP_policy_at_preemption_point
      _ _ _ original_arrival _ _ _ jitter_ready_instance arr_seq sched FP ->
    @respects_FP_policy_at_preemption_point
      _ _ _ release_as_arrival _ _ _ basic_ready_instance rel_seq sched FP.
  Proof.
    move=> UNI COMP j j_hp t ARR_rel PT_rel BL  SCHED_hp.
    have ARR_arr: arrives_in arr_seq j by rewrite jitter_arrives_in_iff.
    apply: COMP => //.
    by rewrite /preemption_time jitter_scheduled_job_at_eq.
  Qed.

  (** ** Transferred Response-Time Bound *)

  (** Finally, we state the main result, which is the whole point of jitter
      propagation in the first place: if it is possible to bound response times
      after release jitter has been folded into the arrival curves, then this
      implies a response-time bound for the original problem with jitter.
      This theorem conceptually corresponds to equations (5) and (6) in Audsley
      et al. (1993), but has been generalized to arbitrary arrival curves.

      - Audsley, N., Burns, A., Richardson, M., Tindell, K., and Wellings,
        A. (1993). Applying new scheduling theory to static priority preemptive
        scheduling. Software Engineering Journal, 8(5):284–292.  *)
  Theorem jitter_response_time_bound :
    forall tsk R,
      tsk \in ts ->
      @task_response_time_bound _ _ release_as_arrival _ _ _ rel_seq sched tsk R ->
      @task_response_time_bound _ _ original_arrival _ _ _ arr_seq sched tsk (task_jitter tsk + R).
  Proof.
    move=> tsk R IN RTB j IN_arr TSK.
    have IN_rel: arrives_in rel_seq j by rewrite -jitter_arrives_in_iff.
    move: (RTB j IN_rel TSK).
    rewrite /job_response_time_bound/job_arrival/release_as_arrival/job_arrival.
    apply: completion_monotonic.
    move: TSK; rewrite /job_of_task => /eqP TSK.
    move: (H_valid_jitter tsk IN j TSK).
    by lia.
  Qed.


End JitterPropagationFacts.

