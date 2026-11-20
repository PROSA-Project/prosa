Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.analysis.facts.priority.jlfp.
Require Export prosa.analysis.facts.model.ideal.schedule.
Require Export prosa.analysis.facts.model.uniprocessor.
Require Export prosa.model.processor.ideal.
Require Export prosa.model.preemption.fully_preemptive.
Require Export prosa.model.readiness.jitter.

(** * Sustainability under Reduced Job Costs *)

(** Sustainability asks whether a scheduling guarantee continues to hold when
    the workload improves. In this module, the improvement is a reduction in the
    execution requirements of jobs. We compare a schedule with the original,
    _reference costs_ and a second schedule with _reduced costs_. Our aim is to
    carry completion guarantees from the reference schedule to the schedule with
    reduced costs: under a suitable class of fully preemptive JLFP scheduling
    policies, jobs never finish later (i.e., do not exhibit scheduling
    anomalies) if any job's execution cost is reduced.

    The comparison proceeds in three stages. First, we describe how the two
    schedules agree on readiness, that is, on when a job is eligible to
    execute. Next, we compare the service that jobs receive, counting the units
    of execution accumulated over time. Finally, we use this comparison to
    preserve completion, response-time, and deadline guarantees.

    Under the scheduling and readiness assumptions below, this is a _strong
    sustainability_ property with respect to execution costs. Following
    Cerqueira et al. (2018, Definitions 22 and 33), execution cost is the
    improving parameter and the set of other variable parameters is empty.  For
    basic readiness or shared eligibility, this means that arrival times,
    deadlines, and eligibility conditions stay fixed while execution costs
    decrease. A guarantee for the given reference schedule is enough to start
    the comparison.

    In the following, both schedules use the same JLFP priority relation,
    including its tie-breaking decisions. This gives us a common ordering with
    which to relate the scheduling decisions. *)

(** The terminology follows Cerqueira et al., building on the original
    sustainability papers by Baruah and Burns:

    - Felipe Cerqueira, Geoffrey Nelissen, and Bjoern B. Brandenburg,
      "On Strong and Weak Sustainability, with an Application to
      Self-Suspending Real-Time Tasks", ECRTS 2018, pp. 26:1–26:21.
      #<a href="https://doi.org/10.4230/LIPIcs.ECRTS.2018.26">DOI: 10.4230/LIPIcs.ECRTS.2018.26</a>#

    - Sanjoy Baruah and Alan Burns, "Sustainable Scheduling Analysis",
      RTSS 2006, pp. 159–168.
      #<a href="https://doi.org/10.1109/RTSS.2006.47">DOI: 10.1109/RTSS.2006.47</a>#

    - Alan Burns and Sanjoy Baruah, "Sustainability in Real-time Scheduling",
      Journal of Computing Science and Engineering 2(1), pp. 74–97, 2008.
      #<a href="https://jcse.kiise.org/posting/2-1/jcse_2-1_15.pdf">PDF</a># *)


(** ** Shared Eligibility *)

(** For generality beyond basic readiness, let us first describe a common source
    of agreement between readiness models.

    A job is _pending_ once it has arrived and still has execution left to
    perform. Readiness additionally determines whether that pending job may
    execute at the instant under consideration.

    For example, release jitter may keep a job from executing until some time
    after its arrival. More generally, a set of availability windows may allow
    it to execute intermittently. We express such conditions with an eligibility
    predicate that can be shared by the two schedules. *)
Section SharedEligibility.

  (** We describe eligibility independently of the processor model. Arrivals
      and execution costs determine which jobs are pending. *)
  Context {Job : JobType} `{JobArrival Job} `{JobCost Job}.
  Context {PState : ProcessorState Job}.

  (** Let [job_eligible] describe the instants at which each job is allowed
      to execute, independently of any schedule. *)
  Variable job_eligible : Job -> instant -> bool.

  (** Shared eligibility separates common restrictions, such as release jitter,
      from each schedule's completion state. Further below, we will use this so
      a job can finish earlier under reduced costs while its eligibility
      conditions remain the same in both schedules. *)
  Definition shared_eligibility_readiness (job_ready_model : JobReady Job PState) :=
    forall sched j t,
      job_ready sched j t = pending sched j t && job_eligible j t.

End SharedEligibility.

(** ** Comparing the Two Schedules *)

(** With the shared readiness model in hand, we can set up the scheduling
    comparison itself. We consider the same arriving jobs twice, once with
    reference costs and once with reduced costs. *)
Section CostSustainability.

  (** Both schedules use the same jobs and arrival sequence. *)
  Context {Job : JobType} `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.

  (** We give each job two execution requirements: its reference cost and its
      reduced cost. *)
  Variables job_cost_reference job_cost_reduced : JobCost Job.

  (** For convenience, we name the two cost functions. We will use them to
      express the reduction in each job's execution requirement. *)
  Let reference_job_cost := @job_cost _ job_cost_reference.
  Let reduced_job_cost := @job_cost _ job_cost_reduced.

  (** We can now state what it means for the workload to improve: each
      arriving job requires at most its reference budget. *)
  Hypothesis H_cost_reduction :
    forall j,
      arrives_in arr_seq j ->
      reduced_job_cost j <= reference_job_cost j.

  (** Next, consider two schedules on an ideal uniprocessor, each using its
      corresponding costs. The reference schedule supplies the guarantees
      that we want to carry to the schedule with reduced costs. *)
  Variables sched_reference sched_reduced : schedule (ideal.processor_state Job).

  (** Readiness depends on whether a job has completed, so each schedule has
      its own readiness model using the appropriate cost assignment. We will
      connect their decisions when comparing the jobs eligible for execution. *)
  Variable job_ready_reference :
    @JobReady Job (ideal.processor_state Job) job_cost_reference _.
  Variable job_ready_reduced :
    @JobReady Job (ideal.processor_state Job) job_cost_reduced _.

  (** To compare the jobs that still need service, we bind the pending
      predicates to the respective schedules and costs. *)
  Let reference_pending := @pending _ _ sched_reference job_cost_reference _.
  Let reduced_pending := @pending _ _ sched_reduced job_cost_reduced _.

  (** We also name the readiness decisions in the two schedules. *)
  Let reference_ready := @job_ready _ _ _ _ job_ready_reference sched_reference.
  Let reduced_ready := @job_ready _ _ _ _ job_ready_reduced sched_reduced.

  (** Earlier scheduling decisions can affect readiness, even when the rules are
      shared. We therefore require agreement for jobs pending in both
      schedules. This connects the actual readiness decisions in the supplied
      schedules, allowing us to compare the jobs competing for execution. *)
  Definition compatible_readiness :=
    forall j t,
      arrives_in arr_seq j ->
      reference_pending j t ->
      reduced_pending j t ->
      (reference_ready j t <-> reduced_ready j t).

  (** ** Familiar Sources of Compatible Readiness *)

  (** Before using readiness compatibility as an assumption, let us look at some
      familiar models that provide it. In the classic _basic readiness_ model,
      every pending job is ready. A job that is pending in both schedules is
      therefore trivially ready in both, giving us the required agreement
      immediately. *)
  Lemma basic_readiness_compatible :
    basic_readiness job_ready_reference ->
    basic_readiness job_ready_reduced ->
    compatible_readiness.
  Proof.
    move=> BAS_REF BAS_RED j t ARR PEND_REF PEND_RED.
    by rewrite /reference_ready /reduced_ready BAS_REF BAS_RED
      -/reference_pending -/reduced_pending PEND_REF PEND_RED.
  Qed.

  (** The shared eligibility condition introduced above gives a second way to
      establish compatibility. Once a job is pending in both schedules,
      readiness reduces to the common eligibility predicate, and thus is the
      same in both. *)
  Lemma shared_eligibility_readiness_compatible :
    forall job_eligible,
      shared_eligibility_readiness job_eligible job_ready_reference ->
      shared_eligibility_readiness job_eligible job_ready_reduced ->
      compatible_readiness.
  Proof.
    move=> job_eligible ELIG_REF ELIG_RED j t ARR PEND_REF PEND_RED.
    by rewrite /reference_ready /reduced_ready ELIG_REF ELIG_RED
      -/reference_pending -/reduced_pending PEND_REF PEND_RED.
  Qed.

  (** Fixed release jitter gives an example of shared eligibility. To use
      Prosa's jitter interface, interpret the same delay assignment with each
      schedule's costs and readiness model. *)
  Let reference_jitter_readiness (job_jitter : JobJitter Job) :=
    @jitter_readiness _ _ _ job_cost_reference job_jitter job_ready_reference.
  Let reduced_jitter_readiness (job_jitter : JobJitter Job) :=
    @jitter_readiness _ _ _ job_cost_reduced job_jitter job_ready_reduced.

  (** With these two interpretations in place, the following lemma supplies
      readiness compatibility for a shared jitter parameter. *)
  Lemma jitter_readiness_compatible :
    forall job_jitter : JobJitter Job,
      reference_jitter_readiness job_jitter ->
      reduced_jitter_readiness job_jitter ->
      compatible_readiness.
  Proof.
    move=> job_jitter JIT_REF JIT_RED j t ARR
      /andP [_ INC_REF] /andP [_ INC_RED].
    by rewrite /reference_ready /reduced_ready
      JIT_REF JIT_RED INC_REF INC_RED.
  Qed.

  (** ** Service and Completion *)

  (** Let us now assume a compatible readiness model ... *)
  Hypothesis H_compatible_readiness : compatible_readiness.

  (** ... and move on to comparing the service received by jobs in the two
      schedules.  To this end, let us introduce the common JLFP policy, which we
      require to be antisymmetric to ensure consistent tie-breaking. *)
  Variable JLFP : JLFP_policy Job.
  Hypothesis H_priority_antisymmetric : antisymmetric_job_priorities JLFP arr_seq.


  (** Both schedules must be valid under their respective costs and readiness
      models, and follow the common JLFP policy. *)

  Hypothesis H_valid_reference_schedule :
    @valid_schedule_of_arrivals _ _ _ sched_reference job_cost_reference arr_seq.
  Hypothesis H_reference_respects_job_readiness :
    @respects_job_readiness _ _ _ sched_reference job_cost_reference job_ready_reference.
  Hypothesis H_reference_respects_policy :
    @respects_JLFP_policy_at_preemption_point _ _ job_cost_reference _
      fully_preemptive_job_model job_ready_reference arr_seq sched_reference JLFP.
  Hypothesis H_valid_reduced_schedule :
    @valid_schedule_of_arrivals _ _ _ sched_reduced job_cost_reduced arr_seq.
  Hypothesis H_reduced_respects_job_readiness :
    @respects_job_readiness _ _ _ sched_reduced job_cost_reduced job_ready_reduced.
  Hypothesis H_reduced_respects_policy :
    @respects_JLFP_policy_at_preemption_point _ _ job_cost_reduced _
      fully_preemptive_job_model job_ready_reduced arr_seq sched_reduced JLFP.

  (** Additionally, we require the reduced-cost schedule to be
      work-conserving. *)
  Hypothesis H_reduced_work_conserving :
    @work_conserving _ _ job_cost_reduced _ job_ready_reduced arr_seq sched_reduced.


  (** With the setup in place, we can now relate the two schedules. The main
      argument compares accumulated service, that is, the amount of execution a
      job has received so far. Once a job has received its reduced execution
      requirement, it has all the service it needs in the reduced-cost
      schedule. We therefore cap the reference service at
      [minn (reduced_job_cost j) (service sched_reference j t)] when
      making the comparison.

      For example, consider a job with reference cost five and reduced cost
      three. Once the reduced-cost schedule has supplied three units, the job is
      complete there. The comparison therefore counts only the first three units
      of reference service.

      We will establish this service bound by induction on time. To prepare the
      induction step, let us first assume that the bound holds at one instant
      and examine how it constrains the two scheduling decisions. *)
  Section ServiceDominanceStep.

    (** Fix an instant [t] at which we compare the jobs selected for
        execution. *)
    Variable t : instant.

    (** Assume that the capped service bound already holds at [t]. *)
    Hypothesis H_service_dominance :
      forall j,
        arrives_in arr_seq j ->
        minn (reduced_job_cost j) (service sched_reference j t)
        <= service sched_reduced j t.

    (** Our first observation concerns jobs that still have work left under
        reduced costs. For such a job, the cap has not yet been reached in
        the reduced-cost schedule. The assumed service bound therefore
        limits how much execution the reference could already have supplied.
        Together with the cost reduction, this tells us that the job is
        still pending in the reference schedule as well. *)
    Local Lemma pending_in_reference :
      forall j,
        arrives_in arr_seq j ->
        reduced_pending j t ->
        reference_pending j t.
    Proof.
      move=> j ARR /andP [ARRIVED INC].
      rewrite /completed_by in INC.
      apply/andP; split=> //.
      rewrite /completed_by -ltnNge.
      apply: leq_trans (H_cost_reduction j ARR).
      apply: leq_ltn_trans; last by rewrite ltnNge.
      move: (H_service_dominance j ARR).
      by rewrite geq_min /reduced_job_cost (negbTE INC) orFb.
    Qed.

    (** We can now use this observation to transfer readiness. A job that is
        ready in the reduced-cost schedule is pending there, and the preceding
        lemma makes it pending in the reference schedule too.  Readiness
        compatibility then tells us that it is also ready in the reference
        schedule. *)
    Local Lemma ready_in_reference :
      forall j,
        arrives_in arr_seq j ->
        reduced_ready j t ->
        reference_ready j t.
    Proof.
      move=> j ARR READY.
      have PEND : reduced_pending j t by exact: any_ready_job_is_pending.
      apply/(H_compatible_readiness j t ARR _ PEND) => //.
      exact: pending_in_reference.
    Qed.

    (** We can now compare the actual scheduling choices. Suppose the reference
        executes a job that is still pending under reduced costs.  Compatibility
        makes this job ready in the reduced-cost schedule too.  If it is waiting
        there, work conservation supplies some executing job.

        The preceding readiness lemma makes that executing job ready in the
        reference schedule as well. Since job priorities are unique (by
        antisymmetry), the same job is scheduled in both schedules. *)
    Lemma reference_execution_preserved_for_pending_job :
      forall j,
        arrives_in arr_seq j ->
        scheduled_at sched_reference j t ->
        reduced_pending j t ->
        scheduled_at sched_reduced j t.
    Proof.
      move=> j ARR SCHED PEND.
      case: (boolP (scheduled_at sched_reduced j t)) => // NSCHED.
      have READY : reduced_ready j t
        by apply/(H_compatible_readiness j t ARR _ PEND).
      have [j' SCHED'] : exists j', scheduled_at sched_reduced j' t.
      { apply: H_reduced_work_conserving ARR _.
        by rewrite /backlogged -/reduced_ready READY NSCHED. }
      case: (eqVneq j j') => [EQ|DIFF]; first by move: NSCHED; rewrite EQ SCHED'.
      suff EQ : j = j' by move: DIFF; rewrite EQ eqxx.
      apply: H_priority_antisymmetric => //.
      - apply: (H_reference_respects_policy _ _ t) => //.
        + by rewrite /preemption_time; case: (scheduled_job_at arr_seq sched_reference t).
        + apply/andP; split.
          * by apply: ready_in_reference.
          * exact: scheduled_job_at_neq DIFF SCHED.
      - apply: H_reduced_respects_policy SCHED' => //.
        + by rewrite /preemption_time; case: (scheduled_job_at arr_seq sched_reduced t).
        + by rewrite /backlogged -/reduced_ready READY NSCHED.
    Qed.

  End ServiceDominanceStep.

  (** With the pointwise schedule comparison in place, we can establish the
      capped service bound at every instant by induction: at time zero, every
      job has received zero service, which gives us the premise to advance the
      bound one instant at a time for all arriving jobs together using the above
      lemma.

      The cap already covers jobs that have completed under reduced costs.  For
      a job that is still pending, each unit of reference execution is matched
      by execution in the reduced-cost schedule, as shown above.  These
      observations preserve the bound as time advances. *)
  Theorem capped_service_dominance :
    forall j t,
      arrives_in arr_seq j ->
      minn (reduced_job_cost j) (service sched_reference j t)
      <= service sched_reduced j t.
  Proof.
    move=> j t; elim: t j => [j ARR|t IH j ARR]; first by rewrite service0 minn0.
    rewrite -!service_last_plus_before !service_at_is_scheduled_at.
    case: (leqP (reduced_job_cost j) (service sched_reduced j t)) => [COMP|INC].
    - apply: leq_trans (leq_addr _ _).
      exact: leq_trans (geq_minl _ _) COMP.
    - case SCHED: (scheduled_at sched_reference j t); last first.
      + rewrite addn0.
        exact: leq_trans (IH j ARR) (leq_addr _ _).
      + rewrite (reference_execution_preserved_for_pending_job t IH) //.
        * apply/andP; split; last by rewrite /completed_by -ltnNge.
          exact: (valid_schedule_of_arrivals_implies_jobs_must_arrive_to_execute
            sched_reference arr_seq H_valid_reference_schedule).
        * rewrite !addn1 geq_min ltnS.
          apply/orP; right.
          move: (IH j ARR).
          by rewrite geq_min (ltn_geF INC) orFb.
  Qed.

  (** ** Job Completion and Response Times *)

  (** For notational convenience, let us name the completion predicates in both
      schedules. *)
  Let reference_completed_by := @completed_by _ _ sched_reference job_cost_reference.
  Let reduced_completed_by := @completed_by _ _ sched_reduced job_cost_reduced.

  (** Suppose a job has completed in the reference schedule by some instant.
      The above service dominance theorem immediately implies completion in the
      schedule with reduced job costs, too. *)
  Corollary completion_preserved_under_cost_reduction :
    forall j t,
      arrives_in arr_seq j ->
      reference_completed_by j t ->
      reduced_completed_by j t.
  Proof.
    move=> j t ARR COMP.
    apply: leq_trans (capped_service_dominance j t ARR).
    rewrite leq_min leqnn /=.
    exact: leq_trans (H_cost_reduction j ARR) COMP.
  Qed.

  (** Thus, when considering the job's response times in the two schedules, ... *)
  Let reference_job_response_time_bound :=
    @job_response_time_bound _ _ sched_reference job_cost_reference _.
  Let job_response_time_bound_under_reduced_costs :=
    @job_response_time_bound _ _ sched_reduced job_cost_reduced _.

  (** ... a bound in the reference schedule extends to the schedule with reduced
      costs.  *)
  Corollary job_response_time_bound_preserved_under_cost_reduction :
    forall j R,
      arrives_in arr_seq j ->
      reference_job_response_time_bound j R ->
      job_response_time_bound_under_reduced_costs j R.
  Proof.
    move=> j R ARR BOUND.
    exact: completion_preserved_under_cost_reduction.
  Qed.

  (** ** Task Response Times *)

  (** The comparison so far concerns individual jobs. We next lift it to the
      task level. *)
  Section TaskResponseTimes.

    (** Suppose the jobs stem from some tasks ... *)
    Context {Task : TaskType} `{JobTask Job Task}.

    (** ... and consider their response-time bounds w.r.t. the two schedules. *)
    Let reference_task_response_time_bound :=
      @task_response_time_bound _ _ _ job_cost_reference _ _
        arr_seq sched_reference.
    Let task_response_time_bound_under_reduced_costs :=
      @task_response_time_bound _ _ _ job_cost_reduced _ _
        arr_seq sched_reduced.

    (** A task-level response-time bound [R] that holds in the reference
        schedule also holds for the schedule with reduced job costs. *)
    Corollary task_response_time_bound_preserved_under_cost_reduction :
      forall tsk R,
        reference_task_response_time_bound tsk R ->
        task_response_time_bound_under_reduced_costs tsk R.
    Proof.
      move=> tsk R BOUND j ARR TSK.
      by apply: job_response_time_bound_preserved_under_cost_reduction.
    Qed.

  End TaskResponseTimes.

  (** ** Deadlines and Schedulability *)

  (** Next, we express the completion guarantee in terms of deadlines.  This
      will also let us state schedulability guarantees for whole task sets. *)
  Section Deadlines.

    (** Suppose the jobs have absolute deadlines ... *)
    Context `{JobDeadline Job}.

    (** ... and consider whether they are met in both schedules. *)
    Let reference_job_meets_deadline :=
      @job_meets_deadline _ _ sched_reference job_cost_reference _.
    Let job_meets_deadline_under_reduced_costs :=
      @job_meets_deadline _ _ sched_reduced job_cost_reduced _.

    (** Completion-time monotonicity trivially implies that a job that meets its
        deadline in the reference schedule also does so in the schedule with
        reduced costs, ... *)
    Corollary job_deadline_preserved_under_cost_reduction :
      forall j,
        arrives_in arr_seq j ->
        reference_job_meets_deadline j ->
        job_meets_deadline_under_reduced_costs j.
    Proof.
      move=> j ARR DL.
      exact: completion_preserved_under_cost_reduction.
    Qed.

    (** ... which naturally applies to all jobs. *)
    Let all_reference_deadlines_met :=
      @all_deadlines_of_arrivals_met _ job_cost_reference _ _
        arr_seq sched_reference.
    Let all_deadlines_met_under_reduced_costs :=
      @all_deadlines_of_arrivals_met _ job_cost_reduced _ _
        arr_seq sched_reduced.

    (** Applying the individual deadline result to each arriving job gives a
        guarantee for the whole arrival sequence. *)
    Corollary all_deadlines_preserved_under_cost_reduction :
      all_reference_deadlines_met ->
      all_deadlines_met_under_reduced_costs.
    Proof.
      move=> DLS j ARR.
      by apply: job_deadline_preserved_under_cost_reduction.
    Qed.

    (** Finally, for analyses that state their conclusion as schedulability of a
        task set, we restate the above observation at the task level. *)
    Section TaskSetSchedulability.

      (** Suppose the jobs under analysis stem from tasks ... *)
      Context {Task : TaskType} `{JobTask Job Task}.

      (** ... and consider the task-level notion of schedulability. *)
      Let reference_taskset_schedulable :=
        @taskset_schedulable _ _ job_cost_reference _ _ _
          arr_seq sched_reference.
      Let taskset_schedulable_under_reduced_costs :=
        @taskset_schedulable _ _ job_cost_reduced _ _ _
          arr_seq sched_reduced.

      (** To conclude, if the selected task set is schedulable in the reference
          schedule, then the same task set is also schedulable under reduced
          execution costs. *)
      Corollary taskset_schedulability_preserved_under_cost_reduction :
        forall ts,
          reference_taskset_schedulable ts ->
          taskset_schedulable_under_reduced_costs ts.
      Proof.
        move=> ts SCHED tsk IN j ARR TSK.
        apply: job_deadline_preserved_under_cost_reduction => //.
        exact: (SCHED tsk).
      Qed.

    End TaskSetSchedulability.

  End Deadlines.

End CostSustainability.
