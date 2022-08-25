From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop ssrZ.

Require Import prosa.model.readiness.basic.
Require Import prosa.analysis.abstract.ideal_jlfp_rta.
Require Import prosa.analysis.facts.busy_interval.carry_in.
Require Import prosa.analysis.facts.readiness.basic.
Require Import prosa.model.schedule.priority_driven.
Require Import prosa.model.priority.gel.
Require Import analysis.facts.priority.gel.
Require Import prosa.analysis.facts.busy_interval.ideal.inequalities.
Require Import prosa.analysis.facts.model.workload.

(** * Abstract RTA for GEL-Schedulers with Bounded Priority Inversion *)
(** In this module we instantiate the abstract response-time analysis
    (aRTA) for GEL-schedulers assuming the ideal uni-processor model and
    real-time tasks with arbitrary arrival models. *)

(** The important feature of this instantiation is that
    it allows reasoning about the meaningful notion of priority
    inversion. However, we do not specify the exact cause of priority
    inversion (as there may be different reasons for this, like
    execution of a non-preemptive segment or blocking due to resource
    locking). We only assume that the duration of priority inversion is
    bounded. *)

Section AbstractRTAforGELwithArrivalCurves.

  (** We consider tasks and jobs with the given parameters. *)
  Context  {Task : TaskType} `{TaskCost Task} `{TaskRunToCompletionThreshold Task}
    `{TaskMaxNonpreemptiveSegment Task} `{MaxArrivals Task}.
  Context  {Job : JobType} `{JobTask Job Task} {Arrival : JobArrival Job}
    {Cost : JobCost Job} `{JobPreemptable Job} `{PriorityPoint Task}.

  (** We assume the basic readiness model. *)
  #[local] Existing Instance basic_ready_instance.

  (** ** A. Defining the System Model *)

  (** We begin by defining the system model. First,
      we model arrivals using an arrival sequence. We assume
      that the arrival is consistent and does not contain duplicates. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** We consider a valid, ideal uniprocessor schedule... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** ... that respects the GEL policy at every preemption point. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task).

  (** We assume that all arrivals have valid job costs. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** We model the tasks in the system using a task set [ts].
      We assume that all jobs in the system come from this task set. *)
  Variable ts : list Task.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that the task set respects the arrival curve
      defined by [max_arrivals]. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** The task under consideration [tsk] is contained in [ts]. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** While we do not assume an explicit preemption model,
      we assume that any preemption model under consideration
      is valid. We also assume that the run-to-completion-threshold
      of the task [tsk] is valid. *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.
  Hypothesis H_valid_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** As mentioned, we assume that the priority inversion for the task
      [tsk] is bound by [priority_inversion_bound]. *)
  Variable priority_inversion_bound: duration -> duration.
  Hypothesis H_priority_inversion_is_bounded:
    priority_inversion_is_bounded_by arr_seq sched tsk priority_inversion_bound.

  (** ** B. Encoding the Scheduling Policy and Preemption Model *)
  (** Next, we encode the scheduling policy and preemption model
      using the functions [interference] and [interfering_workload].
      To this end, we simply reuse the general definitions of interference
      and interfering workload that apply to any JLFP policy, as defined in
      the module [ideal_jlfp_rta]. *)
  Let interference (j : Job) (t : instant) :=
    ideal_jlfp_rta.interference arr_seq sched j t.

  Let interfering_workload (j : Job) (t : instant) :=
    ideal_jlfp_rta.interfering_workload arr_seq sched j t.

  (** ** C. Abstract Work Conservation *)
  (** Let us recall the abstract and classic notations of work conservation. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** We assume that the schedule is work-conserving in the classic sense,
      which allows us to apply [instantiated_i_and_w_are_coherent_with_schedule]
      to conclude that abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** ** D. Bounding the Maximum Busy-Window Length *)
  (** Next, we define [L] as the fixed point of the given equation.
      Given this definition of [L], we can apply the theorem
      [instantiated_busy_intervals_are_bounded] to prove that [L]
      bounds the length of the busy window. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_request_bound_function ts L.

  (** ** E. Defining [IBF_other] *)
  (** Next, we define [IBF_other] and prove that [IBF_other] bounds
      the interference incurred by any job of [tsk]. *)

  (** Consider the following parametrized interval. *)
  Let interval (tsk_o : Task) (A : instant):=
    (Z.of_nat(A + ε) + task_priority_point tsk - task_priority_point tsk_o)%Z.


  (** We define the bound on the total higher-or-equal-priority (HEP) workload
      produced during the interval [Δ] as the sum of the RBFs of all tasks in
      the task set [ts] (excluding [tsk]) over the minimum of [Δ] and [interval]. *)
  Let bound_on_total_hep_workload (A Δ : duration) :=
        \sum_(tsk_o <- ts | tsk_o != tsk)
          task_request_bound_function tsk_o (minn (Z.to_nat (interval tsk_o A)) Δ).

  (** Finally, [IBF_other] for an interval [R] is defined as the sum of
      [bound_on_total_hep_workload] in [R] and [priority_inversion_bound]. *)
  Let IBF_other (A R : duration) := priority_inversion_bound A + bound_on_total_hep_workload A R.

  (** For convenience, we define the following acronym. *)
  Let PP (task : Task) := (task_priority_point task).

  (** In this section, we prove the soundness of [IBF_other]. We start
      by establishing a bound on the HEP workload.*)
    Section HepWorkloadBound.

      (** Consider any job [j] of task [tsk] that
          has a positive job cost and is in the arrival
          sequence. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      Hypothesis H_job_cost_positive: job_cost_positive j.

      (** Assume the busy interval of [j] is given by <<[t1,t2)>>. *)
      Variable t1 t2 : duration.
      Hypothesis H_busy_interval :
        definitions.busy_interval sched interference interfering_workload j t1 t2.

      (** Assume the relative arrival time of [j] is given by [A]. *)
      Let A := job_arrival j - t1.

      (** Consider any arbitrary interval [Δ] within the busy window. *)
      Variable Δ : duration.
      Hypothesis H_Δ_in_busy : t1 + Δ < t2.

      (** Consider the set of jobs arriving in <<[t1, t1 + Δ)>>. *)
      Let jobs := arrivals_between arr_seq t1 (t1 + Δ).

      (** We define a predicate to identify higher priority jobs coming from the task [tsk]. *)
      Let GEL_from (tsk : Task) := fun (jo : Job) => hep_job jo j && (job_task jo == tsk).

      (** First, consider the case where [interval ≤ Δ]. *)
      Section ShortenRange.


        (** Consider any task [tsk_o] distinct from [tsk].
            Assume [tsk_o] is in [ts]. *)
        Variable tsk_o : Task.
        Hypothesis H_tsko_in_ts: tsk_o \in ts.
        Hypothesis H_neq: tsk_o != tsk.

        (** If [Δ] is greater than [interval] for [tsk_o] and [A], ... *)
        Hypothesis H_Δ_ge: Z.to_nat (interval tsk_o A) <= Δ.

        (** ... then the workload of jobs satisfying the predicate [GEL_from]
            in the interval <<[t1,t1 + Δ)>> is equal to the workload in
            the interval <<[t1, t1 + interval [tsk_o] [A])>>.
            Note that, we use the functions [Z.to_nat] to [Z.of_nat] to convert
            integers to natural numbers and vice-versa. *)
        Lemma total_workload_shorten_range:
          workload_of_jobs (GEL_from tsk_o)
            (arrivals_between arr_seq t1 (t1 + Δ))
          <= workload_of_jobs (GEL_from tsk_o)
              (arrivals_between arr_seq t1
                 (Z.to_nat (Z.of_nat t1 + interval tsk_o A))).
        Proof.
          have BOUNDED: Z.to_nat (Z.of_nat t1 + (interval tsk_o A)) <= t1 + Δ by lia.
          rewrite (workload_of_jobs_nil_tail _ _ BOUNDED) // => j' IN' ARR'; rt_eauto.
          rewrite /GEL_from.
          case: (eqVneq (job_task j') tsk_o) => TSK';
                                               last by rewrite andbF.
          rewrite andbT; apply: contraT  => /negPn HEP.
          move: (hep_job_arrives_after_zero _ j' HEP) => GT0.
          move: (hep_job_arrives_before _ j' HEP) => EARLIEST.
          move: H_job_of_tsk; rewrite /job_of_task => /eqP TSK.
          move: ARR'; rewrite /interval /ε => LATEST.
          have LATEST': (Z.of_nat (t1 + A + 1) + task_priority_point tsk -
                           task_priority_point tsk_o <= Z.of_nat (job_arrival j') )%Z
                          by lia.
          by move: LATEST'; rewrite -TSK -TSK' => LATEST'; lia.
        Qed.

      End ShortenRange.

      (** Using the above lemma, we prove that [bound_on_total_hep_workload]
          bounds the sum of higher-priority workload over all tasks in [ts]. *)
      Corollary sum_of_workloads_is_at_most_bound_on_total_hep_workload :
        \sum_(tsk_o <- ts | tsk_o != tsk) workload_of_jobs (GEL_from tsk_o) jobs
        <= bound_on_total_hep_workload A Δ.
      Proof.
        move: (H_busy_interval) => [[/andP [JINBI JINBI2] [QT _]] _].
        apply leq_sum_seq => tsko INtsko NEQT.
        case ( Δ <= Z.to_nat (interval tsko A)) eqn: EQ.
        - rewrite /minn //= ifF; try by lia.
          by apply (workload_le_rbf arr_seq ts); try by done.
        - rewrite /minn ifT; try by lia.
          eapply leq_trans; first by eapply total_workload_shorten_range; eauto 2; lia.
          rewrite /GEL_from.
          case (interval tsko A >=? 0)%Z eqn: EQ1.
          + have -> : (Z.to_nat (Z.of_nat t1 + interval tsko A)) = t1 + Z.to_nat (interval tsko A)
                                                                         by lia.
            by eapply workload_le_rbf; rt_eauto.
          + rewrite arrivals_between_geq /workload_of_jobs.
            rewrite big_nil.
            have -> : Z.to_nat (interval tsko A) = 0 by lia.
            rewrite task_rbf_0_zero; rt_eauto.
            by lia.
      Qed.

    End HepWorkloadBound.

    (** Finally, we prove that [IBF_other] bounds the interference incurred by [tsk]. *)
    Corollary instantiated_task_interference_is_bounded:
      task_interference_is_bounded_by
        arr_seq sched tsk interference interfering_workload (fun tsk A R => IBF_other A R).
    Proof.
      move => j R2 t1 t2 ARR TSK N NCOMPL BUSY.
      move: (posnP (@job_cost _ Cost j)) => [ZERO|POS].
      - exfalso; move: NCOMPL => /negP COMPL; apply: COMPL.
        by rewrite /completed_by /completed_by ZERO.
      - move: (BUSY) => [[/andP [JINBI JINBI2] [QT _]] _].
        rewrite (cumulative_task_interference_split arr_seq _ sched _ _ _ _ _ tsk j); rt_eauto.
        + rewrite /I leq_add //.
          eapply cumulative_priority_inversion_is_bounded; rt_eauto.
          eapply leq_trans. eapply cumulative_interference_is_bounded_by_total_service; rt_eauto.
          eapply leq_trans. apply service_of_jobs_le_workload; rt_eauto.
          eapply leq_trans. eapply reorder_summation; eauto 2 => j' IN.
          by apply H_all_jobs_from_taskset; eapply in_arrivals_implies_arrived; exact IN.
          eapply leq_trans.
          move : TSK => /eqP TSK; rewrite TSK.
          eapply sum_of_workloads_is_at_most_bound_on_total_hep_workload; eauto 2.
          by apply /eqP.
          by done.
        + by eapply GEL_implies_sequential_tasks; rt_auto.
        + by eapply arrived_between_implies_in_arrivals; rt_eauto.
    Qed.

  (** ** F. Defining the Search Space *)

  (** In this section, we define the concrete search space for [GEL].
      Then, we prove that, if a given [A] is in the abstract search space,
      then it is also included in the concrete search space. *)

  (** In order to define the concrete search space, we
      define the predicates [task_rbf_changes_at], ... *)
  Definition task_rbf_changes_at (A : duration) :=
    task_request_bound_function tsk  A != task_request_bound_function tsk (A + ε).

  (** ... [bound_on_total_hep_workload_changes_at], ... *)
  Definition bound_on_total_hep_workload_changes_at A :=
    has (fun tsko =>
           ((tsk != tsko)  && (interval tsko (A - ε) != interval tsko A)))
      ts.

  (** ... and [priority_inversion_changes_at]. *)
  Definition priority_inversion_changes_at (A : duration) :=
    priority_inversion_bound (A - ε) != priority_inversion_bound A.

  (** Finally, we define the concrete search space as the set containing
      all points less than [L] at which any of the bounds on priority inversion, task [rbf],
      or bound on total HEP workload changes. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && (priority_inversion_changes_at A
                || task_rbf_changes_at A
                || bound_on_total_hep_workload_changes_at A).

  (** In this section, we prove that for any job [j] of [tsk],
      if [A] is in the abstract search space, then it is also in
      the concrete search space. *)
  Section ConcreteSearchSpace.

    (** Consider any job j of [tsk]. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** For [j], the total interference bound is defined as follows. *)
    Let total_interference_bound tsk (A Δ : duration) :=
          task_request_bound_function tsk (A + ε) - task_cost tsk + IBF_other A Δ.

    (** Consider any point [A] in the abstract search space. *)
    Variable A : duration.
    Hypothesis H_A_is_in_abstract_search_space:
      search_space.is_in_search_space tsk L total_interference_bound A.

    (** Then, [A] is also in the concrete search space. *)
    Lemma A_is_in_concrete_search_space:
      is_in_search_space A.
    Proof.
      move: H_A_is_in_abstract_search_space  => [-> | [/andP [POSA LTL] [x [LTx INSP2]]]];
                                               apply/andP; split => //.
      { apply/orP; left; apply/orP; right.
        rewrite /task_rbf_changes_at task_rbf_0_zero //; eauto 2.
        apply contraT => /negPn /eqP ZERO.
        rewrite -(ltnn 0) {2}ZERO add0n.
        apply: (@leq_trans (task_cost tsk));
          last by apply: task_rbf_1_ge_task_cost; rt_eauto.
        apply: (@leq_trans (job_cost j)) => //.
        move: (H_job_of_tsk) => /eqP <-.
        by apply: (H_valid_job_cost _ H_j_arrives). }
      { apply contraT; rewrite !negb_or => /andP [/andP [/negPn/eqP PI /negPn/eqP RBF]  WL].
        exfalso; apply INSP2.
        rewrite /total_interference_bound subnK // RBF.
        apply /eqP; rewrite eqn_add2l /IBF_other PI eqn_add2l.
        rewrite /bound_on_total_hep_workload.
        apply /eqP; rewrite big_seq_cond [RHS]big_seq_cond.
        apply eq_big => // tsk_i /andP [TS OTHER].
        move: WL; rewrite /bound_on_total_hep_workload_changes_at => /hasPn WL.
        move: {WL} (WL tsk_i TS) =>  /nandP [/negPn/eqP EQ|/negPn/eqP WL];
                                    first by move: OTHER; rewrite EQ => /neqP.
        case: (ltngtP (Z.to_nat (interval tsk_i A)) x) => [ltn_x|gtn_x|eq_x];
                                                         rewrite /minn;
                                                         first by rewrite ifT // WL.
        - rewrite ifF // WL.
          by lia.
        - by case: (Z.to_nat (interval tsk_i (A - ε)) < x)%nat; [rewrite WL| rewrite eq_x]. }
    Qed.

  End ConcreteSearchSpace.

  (** ** G. Stating the Response-Time Bound [R] *)

  (** Finally, we define the response-time bound [R] as follows. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum:
    forall (A : duration),
      is_in_search_space A ->
      exists (F : duration),
        A + F >= priority_inversion_bound A
                + (task_request_bound_function tsk (A + ε) - (task_cost tsk - task_rtct tsk))
                + bound_on_total_hep_workload  A (A + F) /\
          R >= F + (task_cost tsk - task_rtct tsk).

  Section ResponseTimeReccurence.

    (** In order to connect the concrete definition of [R]
        with the shape of response-time bound equation that aRTA expects,
        we prove the theorem [correct_search_space]. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** We define the total interference as defined above. *)
    Let total_interference_bound tsk (A Δ : duration) :=
          task_request_bound_function tsk (A + ε) - task_cost tsk + IBF_other A Δ.

    (** We know that if [A] is in the abstract search then it is in the concrete search space.
        We also know that if [A] is in the concrete search space then there exists an [R] that
        satisfies [H_R_is_maximum]. Using these facts, here we prove that if [A]
        is in the abstract search space then, there exists a solution to the response-time
        equation as stated in the aRTA. *)
    Corollary correct_search_space:
      forall A,
        search_space.is_in_search_space tsk L total_interference_bound A ->
        exists F,
          A + F >= task_request_bound_function tsk (A + ε) - (task_cost tsk - task_rtct tsk) +
                    IBF_other A (A + F) /\ R >= F + (task_cost tsk - task_rtct tsk).
    Proof.
      move => A IN.
      edestruct H_R_is_maximum as [F [FIX NEQ]].
      eapply A_is_in_concrete_search_space; rt_eauto.
      exists F; split; last by done.
      rewrite -{2}(leqRW FIX).
      by rewrite addnA [_ + priority_inversion_bound A]addnC -!addnA.
    Qed.

  End ResponseTimeReccurence.




  (** ** H. Soundness of the Response-Time Bound *)

  (** Finally, we prove that [R] is a bound on the response time of the
      task [tsk]. *)
  Theorem uniprocessor_response_time_bound_edf:
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => js ARRs TSKs.
    move: (posnP (@job_cost _ Cost js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }
    ( try ( eapply uniprocessor_response_time_bound_seq with
          (interference0 := interference) (interfering_workload0 := interfering_workload)
          (task_interference_bound_function := fun tsk A R => IBF_other A R) (L0 := L) ) ||
        eapply uniprocessor_response_time_bound_seq with
      (interference := interference) (interfering_workload := interfering_workload)
      (task_interference_bound_function := fun tsk A R => IBF_other A R) (L := L)); rt_eauto.
    - by eapply instantiated_i_and_w_are_coherent_with_schedule; rt_eauto.
      * eapply GEL_implies_sequential_tasks; rt_eauto.
    - by eapply instantiated_interference_and_workload_consistent_with_sequential_tasks; rt_eauto.
    - by eapply instantiated_busy_intervals_are_bounded; rt_eauto.
    - by apply instantiated_task_interference_is_bounded.
    - by eapply correct_search_space; eauto 2.
  Qed.


End AbstractRTAforGELwithArrivalCurves.
