Require Export prosa.model.schedule.priority_driven.
Require Export prosa.analysis.abstract.ideal.iw_instantiation.
Require Export prosa.analysis.abstract.IBF.task.
Require Export prosa.analysis.facts.busy_interval.existence.
Require Export prosa.analysis.abstract.ideal.cumulative_bounds.
Require Export prosa.analysis.abstract.ideal.abstract_rta.

(** * Abstract RTA Instantiation for FP-Schedulers with Bounded Priority Inversion *)
(** In this module we instantiate the abstract response-time analysis
    (aRTA) for FP-schedulers assuming the ideal uniprocessor model and
    real-time tasks with arbitrary arrival models. *)

(** The important feature of this instantiation is that
    it allows reasoning about the notion of priority
    inversion. However, we do not specify the exact cause of priority
    inversion (as there may be different reasons for this, like
    execution of a non-preemptive segment or blocking due to resource
    locking). We only assume that the duration of priority inversion is
    bounded. *)

(** The difference in this RTA and the other RTA for FP (from the file bounded_pi.v)
    is that here we drop the sequential-tasks assumption and instead explicitly
    account for self-interference. *)

Section AbstractRTAforFPwithArrivalCurves.

  (** We consider tasks and jobs with the listed parameters. *)
  Context {Task : TaskType}
          `{TaskCost Task}
          `{TaskRunToCompletionThreshold Task}
          `{!MaxArrivals Task}.
  Context {Job : JobType}
          `{JobTask Job Task}
          `{Arrival : !JobArrival Job}
          `{Cost : !JobCost Job}
          `{!JobPreemptable Job}.

  (** We allow for any _work-bearing_ readiness model.
      (The [work_bearing_readiness] restriction is introduced further down
      because it requires a schedule to be introduced first; see [H_job_ready] below.) *)
  Context `{!JobReady Job (ideal.processor_state Job)}.

  (** ** A. Defining the System Model *)

  (** We begin by defining the system model. First,
      we model arrivals using an arrival sequence. We assume
      that the arrival sequence is valid and that all arriving jobs
      comply with the WCET assumption. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** Next, we consider any fixed-priority policy that is reflexive. *)
  Context `{FP : !FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_task_priorities FP.

  (** We consider a valid, ideal uniprocessor schedule that follows a
      work-bearing readiness model. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.


  (** We model the tasks in the system using a task set [ts].
      We assume that all jobs in the system come from this task set. *)
  Variable ts : seq Task.
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** We assume that the task set respects the arrival curve
      defined by [max_arrivals]. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** The task under consideration [tsk] is contained in [ts]. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** While we do not assume an explicit preemption model,
      we require that any preemption model under consideration
      is valid. We also assume that the run-to-completion-threshold
      of the task [tsk] is valid. *)
  Hypothesis H_valid_preemption_model :
    valid_preemption_model arr_seq sched.
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** As mentioned, we assume that the duration of priority inversion
      incurred by the task [tsk] is bounded by [priority_inversion_bound]. *)
  Variable priority_inversion_bound : duration.
  Hypothesis H_priority_inversion_is_bounded :
    priority_inversion_is_bounded_by arr_seq sched tsk (constant priority_inversion_bound).

  (** ** B. Encoding the Scheduling Policy and Preemption Model *)
  (** Next, we encode the scheduling policy and preemption model using
      the functions [interference] and [interfering_workload]. To this
      end, we simply reuse the general definitions of interference and
      interfering workload that apply to any JLFP policy, as defined
      in the module [analysis.abstract.ideal.iw_instantiation]. *)
  #[local] Instance ideal_jlfp_interference : Interference Job :=
    ideal_jlfp_interference arr_seq sched.

  #[local] Instance ideal_jlfp_interfering_workload : InterferingWorkload Job :=
    ideal_jlfp_interfering_workload arr_seq sched.

  (** ** C. Abstract Work Conservation *)
  (** Let us recall the abstract and classic notations of work conservation. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** We assume that the schedule is work-conserving in the classic sense,
      which allows us to apply [instantiated_i_and_w_are_coherent_with_schedule]
      to conclude that abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** ** D. Bounding the Maximum Busy-Window Length *)

  (** For convenience, we define the following acronyms. *)
  Let task_rbf := task_request_bound_function tsk.
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.

  (** Next, we define [L] as a positive fixed point of the given equation ... *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point :
    L = priority_inversion_bound + total_hep_rbf L.

  (** ... and prove that it is a bound on the maximum length of a busy interval. *)
  Lemma instantiated_busy_intervals_are_bounded :
    busy_intervals_are_bounded_by arr_seq sched tsk L.
  Proof.
    move => j ARR TSK POS.
    edestruct (exists_busy_interval) with
      (delta := L) (priority_inversion_bound := (fun (d : duration) => priority_inversion_bound))
      as [t1 [t2 [T1 [T2 BI]]]] => //; last first.
    { exists t1, t2; split=> [//|]; split=> [//|].
      by eapply instantiated_busy_interval_equivalent_busy_interval. }
    { intros; rewrite {2}H_fixed_point leq_add //.
      by apply: hep_workload_le_total_hep_rbf. }
  Qed.

  (** ** E. Defining the Interference Bound Function (IBF) *)
  (** Next, we define [task_IBF] and prove that [task_IBF] bounds
      the interference incurred by any job of [tsk]. Note that the [maxn] here
      is required to avoid the case in which the interval under consideration is
      shorter than [A]. While intuitively it might seem that this case
      is irrelevant, aRTA does not allow for this case to be ignored. *)
  Definition IBF (A : instant) (Δ : duration) :=
    priority_inversion_bound
    + (task_rbf (maxn (A + ε) Δ) - task_cost tsk)
    + total_ohep_rbf (Δ).

  (** First we prove bounds on self-interference, that is, interference
      incurred from other jobs of the same task. Note that since we do not
      require a sequential task model, we need to account for the case of _later_ jobs
      of the same task causing interference. *)
  Section SelfInterferenceBound.

    (** Consider any interval <<[t1, t1 + Δ)>>. *)
    Variable t1 : instant.
    Variable Δ : duration.

    (** Next, consider any job [j] of the task [tsk] that has a positive cost
        and arrives in the arrival sequence _after_ the interval under
        consideration has started. *)
    Variable j : Job.
    Hypothesis H_job_cost_positive : job_cost_positive j.
    Hypothesis H_job_of_task : job_of_task tsk j.
    Hypothesis H_j_in_arr_seq : arrives_in arr_seq j.
    Hypothesis H_t1_le_job_arrival : t1 <= job_arrival j.

    (** First, we consider the case where the job arrives _before_ the end of
        the interval under consideration. *)

    (** Under the assumption that [j] arrives before [t1 + Δ], the interference
        caused by the task under consideration itself is bounded by the cost of
        the workload released by the tasks in the interval (given by the
        RBF). However, we do not want to account for the job under consideration
        itself as interference and hence we subtract the cost of the task. *)
    Lemma self_intf_bound_case1 :
      job_arrival j < t1 + Δ ->
      workload_of_jobs
        (another_hep_job_of_same_task^~ j)
        (arrivals_between arr_seq t1 (t1 + Δ))
      <= task_rbf Δ - task_cost (tsk).
    Proof.
      move=> LT.
      eapply leq_trans; last eapply leq_trans;
        last eapply task_rbf_without_job_under_analysis => //=.
      - rewrite (workload_of_jobs_equiv_pred _  _
                   (another_hep_job_of_same_task^~ j));
          last by move => jo IN1; lia.
        set (hep_job_of_same_task := (fun x : Job => hep_job x j && (job_task x == tsk))).
        rewrite (workload_of_jobs_equiv_pred _ _ (fun x => hep_job_of_same_task x && (x != j) ));
          last first.
        { move => j' _.
          rewrite /another_hep_job_of_same_task /hep_job_of_same_task /another_hep_job.
          move : H_job_of_task => /eqP ->.
          lia. }
        rewrite workload_minus_job_cost'; [apply leqnn| by done|].
        rewrite job_arrival_in_bounds //=.
        by split; [| apply /andP; split] => //=.
      -  rewrite /task_workload_between /task_workload.
         move : H_job_of_task => TSK.
         move : TSK => /eqP TSK.
         rewrite  /hep_job /FP_to_JLFP H_priority_is_reflexive andTb TSK eq_refl //=.
         apply leq_sub; last by done.
         apply workload_of_jobs_weaken.
         move => ? /andP[_  /eqP EQ].
         by apply /eqP.
    Qed.

    (** Next, we consider the case where the job arrives _after_ the interval
        under consideration has ended.  Here, we proceed similarly to the first
        case. However in order to safely subtract the task cost from the RBF,
        we need to consider the interval up to the arrival of the job under
        consideration. *)
    Lemma self_intf_bound_case2 :
      t1 + Δ <= job_arrival j ->
      workload_of_jobs
        (another_hep_job_of_same_task^~ j)
        (arrivals_between arr_seq t1 (t1 + Δ))
      <= task_rbf ((job_arrival j - t1) + ε) - task_cost tsk.
    Proof.
      move=> LEQ.
      eapply leq_trans with
        (workload_of_jobs (another_hep_job_of_same_task^~ j)
           (arrivals_between arr_seq t1 ( (job_arrival j) + 1)));
        first by apply workload_of_jobs_reduce_range => //=;lia.
      eapply leq_trans; last first.
      - eapply task_rbf_without_job_under_analysis with (t1 := t1) => //=.
        lia.
      - set (hep_job_of_same_task := (fun x : Job => hep_job x j && (job_task x == tsk))).
        rewrite (workload_of_jobs_equiv_pred _ _ (fun x => hep_job_of_same_task x && (x != j) ));
          last first.
        { move => j' _.
          rewrite /another_hep_job_of_same_task /hep_job_of_same_task /another_hep_job.
          move : H_job_of_task => /eqP ->.
          lia. }
        rewrite workload_minus_job_cost' //=.
        + apply leq_sub; last first.
          * rewrite /hep_job_of_same_task.
            case (hep_job j j && (job_task j == tsk)) eqn: EQ1; try done.
            contradict EQ1.
            move : H_job_of_task => /eqP TSK.
            by rewrite /hep_job /FP_to_JLFP H_priority_is_reflexive TSK eq_refl  //=.
          * rewrite /task_workload_between /task_workload addnA.
            have ->  :t1 + (job_arrival j - t1) + ε = job_arrival j + ε by lia.
            apply workload_of_jobs_weaken.
            move : H_job_of_task => /eqP TSK.
            by move => jo /andP[_ /eqP TSK']; apply /eqP; rewrite -TSK TSK'.
        + apply arrived_between_implies_in_arrivals => //=.
          apply /andP; split; [done| lia].
    Qed.

    (** Combining the above two bounds, we obtain the final bound on the
        self-interference incurred by any job [j] of task [tsk]. *)
    Lemma self_intf_bound :
      workload_of_jobs
        (another_hep_job_of_same_task^~ j)
        (arrivals_between arr_seq t1 (t1 + Δ))
      <= task_rbf (maxn ((job_arrival j - t1) + ε) Δ) - (task_cost tsk).
    Proof.
      case ((t1 + Δ) > (job_arrival j)) eqn: MAX.
      - have ->: maxn ((job_arrival j - t1) + ε) Δ = Δ by lia.
        by apply self_intf_bound_case1 => //=.
      - have ->: maxn ((job_arrival j - t1) + ε) Δ = ((job_arrival j - t1) + ε) by lia.
        apply self_intf_bound_case2 => //=.
        by lia.
    Qed.

  End SelfInterferenceBound.

  (** Next, we use the above bound on self-interference to state a bound on the
      total interference incurred by any job [j] of task [tsk]. *)
  Lemma instantiated_task_interference_is_bounded :
    job_interference_is_bounded_by arr_seq sched tsk IBF
      (relative_arrival_time_of_job_is_A sched).
  Proof.
    move => t1 t2 Δ j ARR TSK BUSY LT NCOMPL A OFF.
    rewrite /IBF.
    move: (posnP (@job_cost _ Cost j)) => [ZERO''|POS];
                                          first by exfalso; rewrite /completed_by ZERO'' in NCOMPL.
    have X := cumulative_interference_split.
    rewrite /cumulative_interference in X.
    rewrite X //=.
    clear X.
    rewrite /IBF -addnA leq_add //.
    - pose PI_fun :duration -> duration := fun=> priority_inversion_bound.
      have: cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) <= PI_fun 0;
        last by apply.
      apply: cumulative_priority_inversion_is_bounded => //.
    - erewrite cumulative_i_ohep_eq_service_of_ohep => //;
                                                         last by eauto 6 with basic_rt_facts.
      apply: leq_trans; first by apply service_of_jobs_le_workload => //=.
      rewrite workload_of_other_jobs_split.
      rewrite -[leqLHS]addnC.
      apply leq_add.
      + specialize (OFF t1 t2 BUSY).
        rewrite OFF.
        by eapply self_intf_bound => //=.
      + by apply ohep_workload_le_rbf => //.
  Qed.

  (** ** F. Defining the Search Space *)

  (** In this section, we define the concrete search space for [FP] scheduling.
      Then, we prove that, if a given [A] is in the abstract search space,
      then it is also included in the concrete search space. *)
  (** First, let us recall the definition of the abstract search space as
      defined in the aRTA framework. *)
  Let is_in_abstract_search_space A := search_space.is_in_search_space L IBF A.

  Section ConcreteSearchSpace.

    (** We begin by defining the concrete search space as follows. *)
    Definition is_in_concrete_search_space A :=
      (A < L) && (task_rbf A != task_rbf (A + ε)).

    (** To rule out pathological cases with the concrete search space,
        we assume that the task cost is positive and the arrival curve
        is non-pathological. *)
    Hypothesis H_task_cost_pos : 0 < task_cost tsk.
    Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

    (** Then, for any relative arrival time [A], we prove that, ... *)
    Variable A : duration.

    (** ... if [A] is in the abstract search space, ... *)
    Hypothesis H_A_is_in_abstract_search_space :
     is_in_abstract_search_space A.

    (** ... then [A] is also in the concrete search space. *)
    Lemma A_is_in_concrete_search_space :
      is_in_concrete_search_space A.
    Proof.
      move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
      - rewrite INSP.
        apply/andP; split; first by done.
        rewrite neq_ltn; apply/orP; left.
        rewrite {1}/task_rbf; erewrite task_rbf_0_zero; eauto 2; try done.
        rewrite add0n /task_rbf; apply leq_trans with (task_cost tsk); try lia.
        exact: task_rbf_1_ge_task_cost.
      - apply/andP; split; first by done.
        apply/negP; intros EQ; move: EQ => /eqP EQ.
        rewrite /IBF subn1 addn1 prednK // in INSP2.
        apply INSP2.
        case (A < x) eqn: EQ1.
        + have ->: maxn A x = x by lia.
          by have ->: maxn (A + ε) x = x by lia.
        + have ->: maxn A x = A by lia.
          by have ->: maxn (A + ε) x = (A + ε) by lia.
    Qed.

  End ConcreteSearchSpace.

  (** ** G. Stating the Response-Time Bound [R] *)

  (** Finally, we define the response-time bound [R] as follows. Note the
      condition [0 < F] in the equation below. While this condition is
      not needed in the RTAs for sequential tasks, it is required here to ensure
      that we consider the least _positive_ fix point. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum :
    forall (A : duration),
      is_in_concrete_search_space A ->
      exists (F : duration),
        0 < F
        /\ A + F >= priority_inversion_bound + total_hep_rbf (A + F)
                    - (task_cost tsk - task_rtct tsk)
        /\ R >= F + (task_cost tsk - task_rtct tsk).

  (** Next, in this section, we prove that, if a solution to the above equation
      exists, then a solution to the response-time equation as stated in aRTA
      also exists. *)
  Section ResponseTimeReccurence.

    (** To rule out pathological cases with the concrete search space,
        we assume that the task cost is positive and the arrival curve
        is non-pathological. *)
    Hypothesis H_task_cost_pos : 0 < task_cost tsk.
    Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

    (** We know that, if [A] is in the abstract search, then it is in the concrete search space, too.
        We also know that, if [A] is in the concrete search space, then there exists an [R] that
        satisfies [H_R_is_maximum]. Using these facts, here we prove that, if [A]
        is in the abstract search space then, there exists a solution to the response-time
        equation as stated in the aRTA. *)
    Corollary correct_search_space :
      forall A,
        is_in_abstract_search_space A ->
        exists F : nat,
          task_rtct tsk + IBF A (A + F) <= A + F
          /\ F + (task_cost tsk - task_rtct tsk) <= R.
    Proof.
      move => A IN.
      move: (H_R_is_maximum A) => FIX.
      feed FIX; first by apply A_is_in_concrete_search_space.
      move: FIX => [F  [GE1 [FIX NEQ]]].
      rewrite /IBF.
      exists F.
      split; last by done.
      rewrite /IBF.
      eapply leq_trans; last by apply FIX.
      move: H_valid_run_to_completion_threshold => [BOUND _].
      rewrite /task_rtc_bounded_by_cost in BOUND.
      have F2 : task_rbf (maxn (A + ε) (A + F)) >= task_cost tsk.
      { eapply (task_rbf_ge_task_cost _ _ _ _) => //=.
        lia. }
      have MAXX :  maxn (A + 1) (A + F) =  A + F by lia.
      rewrite MAXX in F2.
      rewrite MAXX.
      have SPLITLE : total_hep_rbf (A + F) >= total_ohep_rbf (A + F) + task_rbf (A + F).
      { apply split_hep_rbf_weaken => //. }
      by lia.
      Unshelve.
      all: by done.
    Qed.

  End ResponseTimeReccurence.

  (** ** H. Soundness of the Response-Time Bound *)

  (** Finally, we prove that [R] is a bound on the response time of task [tsk]. *)
  Theorem uniprocessor_response_time_bound_fp :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    intros js ARRs TSKs.
    move: (posnP (@job_cost _ Cost js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }
    eapply uniprocessor_response_time_bound_ideal => //.
    - exact: instantiated_i_and_w_are_coherent_with_schedule.
    - exact: instantiated_busy_intervals_are_bounded.
    - exact: instantiated_task_interference_is_bounded.
    - by apply : correct_search_space => //.
  Qed.

End AbstractRTAforFPwithArrivalCurves.
