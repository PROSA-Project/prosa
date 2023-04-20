From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop ssrZ.

Require Import prosa.util.int.
Require Export prosa.analysis.facts.busy_interval.ideal.inequalities.
Require Export prosa.analysis.facts.priority.elf.
Require Export prosa.analysis.facts.interference.
Require Export prosa.analysis.facts.busy_interval.carry_in.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.analysis.facts.priority.jlfp_with_fp.

(** * Response-Time Analysis for the ELF Scheduling Policy *)

(** In the following, we derive a response-time analysis for ELF schedulers,
    assuming a workload of sporadic real-time tasks characterized by arbitrary
    arrival curves executing upon an ideal uniprocessor. To this end, we
    instantiate the _abstract Response-Time Analysis_ (aRTA) as provided in the
    [prosa.analysis.abstract] module. *)

Section AbstractRTAforELFwithArrivalCurves.

  (** ** A. Defining the System Model *)

  (** Before any formal claims can be stated, an initial setup is needed to
      define the system model under consideration. To this end, we next
      introduce and define the following notions using Prosa's standard
      definitions and behavioral semantics:
      - tasks, jobs, and their parameters,
      - the sequence of job arrivals,
      - worst-case execution time (WCET) and the absence of self-suspensions,
      - the set of tasks under analysis,
      - the task under analysis, and, finally,
      - an arbitrary schedule of the task set. *)

  (** *** Tasks and Jobs  *)

  (** Consider any type of tasks, each characterized by a WCET [task_cost],
      a run-to-completion threshold [task_rtct], a maximum non-preemptive segment
      length [task_max_nonpreemptive_segment], an arrival curve [max_arrivals], and
      a relative priority point [task_priority_point] ... *)
  Context  {Task : TaskType} `{TaskCost Task} `{TaskRunToCompletionThreshold Task}
    `{TaskMaxNonpreemptiveSegment Task} `{MaxArrivals Task} `{PriorityPoint Task}.

  (** ... and any type of jobs associated with these tasks, where each job has
      an arrival time [job_arrival], a cost [job_cost], and an arbitrary
      preemption model indicated by [job_preemptable]. *)
  Context  {Job : JobType} `{JobTask Job Task} {Arrival : JobArrival Job}
    {Cost : JobCost Job} `{JobPreemptable Job}.

  (** *** The Job Arrival Sequence *)

  (** Consider any valid arrival sequence [arr_seq]. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence (arr_seq).

  (** *** Absence of Self-Suspensions and WCET Compliance *)

  (** We assume the classic (i.e., Liu & Layland) model of readiness without
      jitter or self-suspensions, wherein [pending] jobs are always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** We further require that a job's cost cannot exceed its task's stated
      WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** *** The Task Set *)

  (** We consider an arbitrary task set [ts]... *)
  Variable ts : list Task.
  Hypothesis H_task_set : uniq ts.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Furthermore, we assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for any task
      [tsk] in [ts], [max_arrival tsk] is (1) an arrival bound of [tsk], and ... *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** ... (2) a monotonic function that equals [0] for the empty interval [delta = 0]. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** *** The Task Under Analysis *)

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** We assume that [tsk] is described by a valid task _run-to-completion
      threshold_. That is, there exists a task parameter [task_rtct] such
      that [task_rtct tsk] is
      - (1) no larger than [tsk]'s WCET, and
      - (2) for any job of task [tsk], the job's run-to-completion threshold
            [job_rtct] is bounded by [task_rtct tsk]. *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** *** The Schedule *)

  (** Finally, we consider any arbitrary, valid ideal uni-processor schedule of
      the given arrival sequence [arr_seq]. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.

  (** Now, we assume that the fixed-priority policy [FP] that parameterizes the
      ELF policy is... *)
  Variable FP : FP_policy Task.

  (** ... reflexive, transitive, and total. *)
  Hypothesis H_reflexive_priorities : reflexive_task_priorities FP.
  Hypothesis H_transitive_priorities : transitive_task_priorities FP.
  Hypothesis H_total_priorities : total_task_priorities FP.

  (** We assume that the schedule complies with the preemption model ... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ... and finally, that it respects the [ELF] scheduling policy. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched (ELF FP).

  (** In this file, we assume that there exists a bound on the length of any
      priority inversion experienced by any job of task [tsk]. *)
  Variable priority_inversion_bound : duration -> duration.
  Hypothesis H_priority_inversion_is_bounded :
    priority_inversion_is_bounded_by arr_seq sched tsk priority_inversion_bound.

  (** ** B. Interference and Interfering Workload *)

  (** With the system model in place, the next step is to encode the scheduling
      policy and preemption model such that aRTA becomes applicable. To this
      end, we encode the semantics of the scheduling policy and preemption model
      by instantiating two functions, called [interference] and
      [interfering_workload].

      We can simply reuse the existing general definitions of _interference_ and
      _interfering workload_ that apply to job-level fixed-priority (JLFP)
      policy (as provided in the module
      [analysis.abstract.ideal.iw_instantiation]).*)
  #[local] Instance ideal_elf_interference : Interference Job :=
    ideal_jlfp_interference arr_seq sched.

  #[local] Instance ideal_elf_interfering_workload : InterferingWorkload Job :=
    ideal_jlfp_interfering_workload arr_seq sched.

  (** ** C. Classic and Abstract Work Conservation *)

  (** We assume that the schedule is work-conserving in the classic sense. *)
  Hypothesis H_work_conserving : work_conserving.work_conserving arr_seq sched.

  (** This allows us to apply [instantiated_i_and_w_are_coherent_with_schedule]
      to conclude that abstract work-conservation also holds. *)

  (** ** D. Maximum Busy-Window Length *)

  (** The next step is to establish a bound on the maximum busy-window length,
      which aRTA requires to be given. *)

  (** To this end, we assume that we are given a positive value [L] ...*)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.

  (** ... that is a fixed point of the following equation. *)
  Hypothesis H_fixed_point : L = total_request_bound_function ts L.

  (** Given this definition of [L], we can apply the theorem
      [instantiated_busy_intervals_are_bounded] to prove that [L] bounds the
      length of the busy window. *)

  (** ** E. The Interference-Bound Function *)

  (** Next, we define the interference [IBF_other] and prove that [IBF_other]
      bounds the interference incurred by any job of [tsk]. Note that
      [IBF_other] only takes the interference from jobs of other tasks into
      account i.e., self-interference is not included. *)

  (** We first consider the interference incurred due to strictly
      higher-priority tasks i.e., those which have strictly higher-priority
      according to the FP policy. *)
  Definition total_hp_rbf := total_hp_request_bound_function_FP ts tsk.

  (** We define the following parameterized end point of the interval during
      which interfering jobs of equal-priority tasks must arrive. The implicit
      beginning of the interval is the start of the busy window, i.e., at time
      [t1]. *)
  Definition ep_task_intf_interval (tsk_o : Task) (A : instant) :=
    ((A + ε)%:R + task_priority_point tsk - task_priority_point tsk_o)%R.

  (** Using this interval end point, we define the bound on the total
      equal-priority ([EP]) workload produced during the interval [Δ] as the sum
      of the RBFs of all tasks (with equal priority as [tsk]) in the task set
      [ts] (excluding [tsk]) over the minimum of [Δ] and
      [ep_task_intf_interval]. *)
  Definition bound_on_total_ep_workload (A Δ : duration) :=
    \sum_(tsk_o <- ts | ep_task tsk tsk_o && (tsk_o != tsk))
      task_request_bound_function tsk_o (minn `|Num.max 0%R (ep_task_intf_interval tsk_o A)| Δ).

  (** Finally, [IBF_other] for an interval [Δ] is defined as the sum of
      [priority_inversion_bound], [bound_on_total_ep_workload], and
      [total_hp_rbf] on [Δ]. *)
  Definition IBF_other (tsk : Task) (A Δ : duration) :=
    priority_inversion_bound A + bound_on_total_ep_workload A Δ + total_hp_rbf Δ.

  (** In this section, we prove the soundness of [IBF_other].*)
  Section BoundingIBF.

    (** Consider any job [j] of task [tsk] that has a positive job cost and is
        in the arrival sequence. *)
    Variable j : Job.
    Hypothesis H_job_of_task : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.
    Hypothesis H_j_in_arr_seq : arrives_in arr_seq j.

    (** Assume the busy interval of [j] (in the abstract sense) is given by <<[t1,t2)>>. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_window : definitions.busy_interval sched j t1 t2.

    (** Consider any arbitrary length [Δ] interval <<[t1, t1+ Δ)>> within the
        busy window. *)
    Variable Δ : duration.
    Hypothesis H_Δ_in_busy : t1 + Δ <= t2.

    (** We define the service needed by jobs belongings to other equal-priority
        tasks, that have higher-or-equal priority than [j]... *)
    Definition service_of_hp_jobs_from_other_ep_tasks (j : Job) (t1 t2 : instant) :=
      service_of_jobs sched (fun jhp => other_ep_task_hep_job jhp j)
        (arrivals_between arr_seq t1 t2) t1 t2.

    (** ...and show that it is equivalent to the cumulative interference
        incurred by [j] due to these jobs. *)
    Lemma cumulative_intf_ep_task_service_equiv :
      cumulative_interference_from_hep_jobs_from_other_ep_tasks arr_seq sched j t1 (t1 + Δ)
      = service_of_hp_jobs_from_other_ep_tasks  j t1 (t1 + Δ).
    Proof.
      rewrite /cumulative_interference_from_hep_jobs_from_other_ep_tasks
        /service_of_hp_jobs_from_other_ep_tasks
        /hep_job_from_other_ep_task_interference.
      rewrite (cumulative_pred_eq_service arr_seq _ sched _ _ _ j t1) //;
        first by eauto 6 with basic_rt_facts.
      by move => j' /andP[/andP[HEP _] _].
    Qed.

    (** Similarly, we define the service required by jobs belonging to other
        strictly higher-priority tasks, that have higher-or-equal priority than
        [j], ... *)
    Definition service_of_hp_jobs_from_other_hp_tasks (j : Job) (t1 t2 : instant) :=
      service_of_jobs sched (fun jhp => hp_task_hep_job jhp j)
        (arrivals_between arr_seq t1 t2) t1 t2.

    (** ... and show that it is equivalent to the cumulative interference
        incurred by [j] due to these jobs. *)
    Lemma cumulative_intf_hp_task_service_equiv :
      cumulative_interference_from_hep_jobs_from_hp_tasks arr_seq sched j t1 (t1 + Δ)
      = service_of_hp_jobs_from_other_hp_tasks j t1 (t1 + Δ).
    Proof.
      rewrite /cumulative_interference_from_hep_jobs_from_hp_tasks
        /service_of_hp_jobs_from_other_hp_tasks
        /hep_job_from_hp_task_interference.
      rewrite (cumulative_pred_eq_service arr_seq _ sched _ _ _ j t1) //;
        first by eauto 6 with basic_rt_facts.
      by move => j' /andP[HEP HP].
    Qed.

    (** Assume the arrival time of [j] relative to the busy window start is
        given by [A]. *)
    Let A := job_arrival j - t1.

    (** First, consider the case where [ep_task_intf_interval ≤ Δ]. *)
    Section ShortenRange.

      (** Consider any equal-priority task [tsk_o] distinct from [tsk].  Assume
          that [tsk_o] is in [ts]. *)
      Variable tsk_o : Task.
      Hypothesis H_tsko_in_ts : tsk_o \in ts.
      Hypothesis H_neq : tsk_o != tsk.
      Hypothesis H_task_priority : ep_task tsk tsk_o.

      (** We define a predicate to identify higher-or-equal-priority jobs coming
          from the task [tsk]. *)
      Let hep_jobs_from (tsk : Task) :=
        fun (jo : Job) =>
          hep_job jo j
          && ep_task (job_task jo) (job_task j)
          && (job_task jo == tsk).

      (** If [Δ] is greater than [ep_task_intf_interval] for [tsk_o] and [A], ... *)
      Hypothesis H_Δ_ge : (ep_task_intf_interval tsk_o A <= Δ%:R)%R.

      (** ... then the workload of jobs satisfying the predicate [hp_jobs_from]
              in the interval <<[t1,t1 + Δ)>> is bounded by the workload in the
              interval <<[t1, t1 + ep_task_intf_interval [tsk_o] [A])>>. *)
      Lemma total_workload_shorten_range :
        workload_of_jobs [eta hep_jobs_from tsk_o]
          (arrivals_between arr_seq t1 (t1 + Δ))
        <= workload_of_jobs [eta hep_jobs_from tsk_o]
            (arrivals_between arr_seq t1
               `|Num.max 0%R (t1%:R + ep_task_intf_interval tsk_o A)%R|).
      Proof.
        have BOUNDED: `|Num.max 0%R (t1%:R + (ep_task_intf_interval tsk_o A))%R| <= t1 + Δ
          by clear - H_Δ_ge; lia.
        rewrite /hep_jobs_from /hep_job /ELF.
        rewrite (workload_of_jobs_nil_tail _ _ BOUNDED) // => j' IN' ARR'.
        apply/contraT => /negPn /andP [/andP [/orP[/andP [_ /negP+]|/andP [_ HEP]] /andP [_ _]] /eqP TSKo] //.
        move: ARR'; rewrite /ep_task_intf_interval /ε -TSKo.
        move: H_job_of_task => /eqP <-.
        move: HEP; rewrite /hep_job /GEL /job_priority_point.
        by clear; lia.
      Qed.

    End ShortenRange.

    (** Then, we establish that the cumulative interference incurred by [j] due
        to all higher-or-equal-priority jobs from equal-priority tasks is
        bounded by the [bound_on_ep_workload], ... *)
    Lemma bound_on_ep_workload :
      cumulative_interference_from_hep_jobs_from_other_ep_tasks arr_seq sched j t1 (t1 + Δ)
        <= bound_on_total_ep_workload (job_arrival j - t1) Δ.
    Proof.
      move: H_job_of_task => /eqP TSK.
      rewrite cumulative_intf_ep_task_service_equiv /service_of_hp_jobs_from_other_ep_tasks
        /service_of_jobs.
      apply: leq_trans; first by apply: service_of_jobs_le_workload.
      rewrite /bound_on_total_ep_workload /ep_task_hep_job
        /other_ep_task_hep_job /ep_task_hep_job.
      rewrite (workload_of_hep_jobs_partitioned_by_tasks _ _ ts _  _ tsk) //.
      apply: leq_sum_seq => tsk_o IN /andP[EP OTHER].
      apply: leq_trans.
      { apply: (workload_of_jobs_weaken _
                  (fun j0 : Job => hep_job j0 j
                                && ep_task (job_task j0) (job_task j)
                                && (job_task j0 == tsk_o)))
             => i /andP[/andP[? ?] ?].
        by apply /andP; split. }
      { have [LEQ|GT] := leqP Δ `|Num.max 0%R (ep_task_intf_interval tsk_o A)%R|; [| apply ltnW in GT].
        { apply: leq_trans; last by eapply task_workload_le_task_rbf.
          apply: (workload_of_jobs_weaken _ (fun j0 => (job_task j0 == tsk_o))).
          by move => j'/ andP[_ EXACT]. }
        { apply: leq_trans;
            first by apply total_workload_shorten_range => //; clear - GT H_Δ_in_busy; lia.
          rewrite (workload_of_jobs_equiv_pred _ _ (fun jo : Job => hep_job jo j && (job_task jo == tsk_o))).
          { case EQ: (0 <= ep_task_intf_interval tsk_o A)%R;
              last by rewrite arrivals_between_geq; [rewrite workload_of_jobs0|clear - EQ; lia].
            have -> : `|Num.max 0%R (t1%:R + ep_task_intf_interval tsk_o A)%R|
                     = t1 + `|Num.max 0%R (ep_task_intf_interval tsk_o A)|
              by clear -EQ; lia.
            by apply: (workload_le_rbf' arr_seq tsk_o _ _  t1 _ (fun jo => hep_job jo j)). }
          { move => j' IN1.
            have [TSK'|_] := (eqVneq  (job_task j') tsk_o).
            - by rewrite !andbT TSK TSK' ep_task_sym EP andbT.
            - by rewrite !andbF. }}}
    Qed.

    (** ... and that the cumulative interference incurred by [j] due to all
        higher-or-equal priority jobs from higher-priority tasks is bounded by
        the [total_hp_rbf]]. *)
    Lemma bound_on_hp_workload :
      cumulative_interference_from_hep_jobs_from_hp_tasks arr_seq sched j t1 (t1 + Δ)
        <= total_hp_rbf Δ.
    Proof.
      rewrite cumulative_intf_hp_task_service_equiv /total_hp_rbf.
      apply: leq_trans;
        first by apply service_of_jobs_le_workload.
      rewrite /workload_of_jobs /total_hp_request_bound_function_FP.
      rewrite [X in X <= _](eq_big (fun j0 => hp_task (job_task j0) tsk) job_cost) //;
        first by apply: sum_of_jobs_le_sum_rbf; eauto.
      rewrite /hp_task_hep_job  => j'.
      rewrite andb_idl => [|?].
      - by move: H_job_of_task => /eqP ->.
      - by apply/orP; left.
    Qed.

  End BoundingIBF.

  (** Finally, we use the above two lemmas to prove that [IBF_other] bounds the
      interference incurred by [tsk]. *)
  Lemma instantiated_task_interference_is_bounded :
    task_interference_is_bounded_by arr_seq sched tsk IBF_other.
  Proof.
    rewrite /task_interference_is_bounded_by => j Δ t1 t2 ARR TSK IN NCOMPL BUSY.
    have [ZERO|POS] := posnP (job_cost j).
    - exfalso; move: NCOMPL => /negP COMPL; apply: COMPL.
      by rewrite /completed_by /completed_by ZERO.
    - rewrite (cumulative_task_interference_split _  _ _  _ _ _ _ _ _ j) //.
      rewrite /IBF_other -addnA.
      apply: leq_add;
        first by apply: cumulative_priority_inversion_is_bounded.
      rewrite cumulative_hep_interference_split_tasks_new // addnC.
      apply: leq_add.
      + by apply: bound_on_ep_workload.
      + by apply: bound_on_hp_workload.
  Qed.

  (** ** F. Defining the Search Space *)

  (** In this section, we define the concrete search space for [ELF].  Then, we
      prove that, if a given [A] is in the abstract search space, then it is
      also included in the concrete search space. *)

  (** For [tsk], the total interference bound is defined as the sum of the interference
      due to (1) jobs belonging to same task (self interference) and
             (2) jobs belonging to other tasks [IBF_other]. *)
  Let total_interference_bound tsk (A Δ : duration) :=
    task_request_bound_function tsk (A + ε) - task_cost tsk + IBF_other tsk A Δ.

  (** In the case of ELF, of the four terms that constitute the total
      interference bound, only the [priority_inversion_bound], task RBF and the
      bound on total equal-priority workload are dependent on the offset [A]. *)

  (** Therefore, in order to define the concrete search space, we define
      predicates that capture when they change for successive values of the
      offset [A]. *)

  Definition task_rbf_changes_at (A : duration) :=
    task_request_bound_function tsk  A != task_request_bound_function tsk (A + ε).

  Definition bound_on_total_ep_workload_changes_at A :=
    has (fun tsk_o => ep_task tsk tsk_o
                   && (tsk_o != tsk)
                   && (ep_task_intf_interval tsk_o (A - ε) != ep_task_intf_interval tsk_o A))
      ts.

  Definition priority_inversion_changes_at (A : duration) :=
    priority_inversion_bound (A - ε) != priority_inversion_bound A.

  (** Finally, we define the concrete search space as the set containing all
      points less than [L] at which any of the bounds on priority inversion,
      task RBF, or total equal priority workload changes. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && (priority_inversion_changes_at A
                || task_rbf_changes_at A
                || bound_on_total_ep_workload_changes_at A).

  (** In this section, we prove that, for any job [j] of task [tsk], if [A] is
      in the abstract search space, then it is also in the concrete search
      space. *)
  Section ConcreteSearchSpace.

    (** Consider any job [j] of [tsk]. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Any point [A] in the abstract search space... *)
    Variable A : duration.
    Hypothesis H_A_is_in_abstract_search_space :
      search_space.is_in_search_space tsk L total_interference_bound A.

    (** ... is also in the concrete search space. *)
    Lemma A_is_in_concrete_search_space :
      is_in_search_space A.
    Proof.
      move: H_A_is_in_abstract_search_space  => [-> | [/andP [POSA LTL] [x [LTx INSP2]]]]
        ; apply/andP; split => //.
      { apply /orP; left; apply/orP; right.
        rewrite /task_rbf_changes_at task_rbf_0_zero //; eauto 2.
        apply contraT => /negPn /eqP ZERO.
        rewrite -(ltnn 0) {2}ZERO add0n.
        apply: (@leq_trans (task_cost tsk));
          last by apply: task_rbf_1_ge_task_cost.
        apply: (@leq_trans (job_cost j)) => //.
        move: (H_job_of_tsk) => /eqP <-.
        by apply: (H_valid_job_cost _ H_j_arrives). }
      apply contraT; rewrite !negb_or => /andP [/andP [/negPn/eqP PI /negPn/eqP RBF]  WL].
      exfalso; apply INSP2.
      rewrite /total_interference_bound subnK // RBF.
      apply /eqP; rewrite eqn_add2l /IBF_other PI !addnACl eqn_add2r.
      rewrite /bound_on_total_ep_workload.
      apply /eqP; rewrite big_seq_cond [RHS]big_seq_cond.
      apply eq_big => // tsk_i /andP [TS OTHER].
      move: WL; rewrite /bound_on_total_ep_workload_changes_at => /hasPn WL.
      move: {WL} (WL tsk_i TS) =>  /nandP [/negbTE EQ|/negPn/eqP WL].
      { by move: OTHER; rewrite EQ. }
      have [leq_x|gtn_x] := leqP `|Num.max 0%R (ep_task_intf_interval tsk_i A)| x.
      - by rewrite WL (minn_idPl leq_x).
      - by rewrite WL (minn_idPr (ltnW gtn_x)).
    Qed.

  End ConcreteSearchSpace.


  (** ** G. The Response-Time Bound [R] *)

  (** Finally, we define the response-time bound [R] as the maximum offset by
      which any job [j] of task [tsk] has completed. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum :
    forall (A : duration),
      is_in_search_space A ->
      exists (F : duration),
        A + F >= IBF_other tsk A (A + F)
                + (task_request_bound_function tsk (A + ε)
                   - (task_cost tsk - task_rtct tsk))
        /\ R >= F + (task_cost tsk - task_rtct tsk).

  Section ResponseTimeReccurence.

    (** Consider any job [j] of task [tsk] that has a positive job cost and is
        in the arrival sequence. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** We have established that if [A] is in the abstract search then it is in
        the concrete search space, too.  We also know that by assumption that,
        if [A] is in the concrete search space, then there exists an [R] that
        satisfies [H_R_is_maximum]. *)

    (** Using these facts, here we prove that if, [A] is in the abstract search
        space, ... *)
    Let is_in_search_space := search_space.is_in_search_space tsk L total_interference_bound.

    (** ... then there exists a solution to the response-time equation as stated
            in the aRTA.  *)
    Corollary response_time_recurrence_solution_exists :
      forall A,
        is_in_search_space A ->
        exists F,
          A + F >= task_request_bound_function tsk (A + ε)
                  - (task_cost tsk - task_rtct tsk)
                  + IBF_other tsk A (A + F)
          /\ R >= F + (task_cost tsk - task_rtct tsk).
    Proof.
      move => A0 IN.
      have [|F [FIX NEQ]] := H_R_is_maximum A0;
        first by apply: A_is_in_concrete_search_space.
      exists F; split =>//.
      by rewrite -{2}(leqRW FIX) addnC.
    Qed.

  End ResponseTimeReccurence.

  (** ** H. Soundness of the Response-Time Bound *)

  (** Finally, we prove that [R] is a bound on the response time of the task
      [tsk]. *)
  Theorem uniprocessor_response_time_bound_elf :
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => j ARRs TSKs.
    have [ZERO|POS] := posnP (job_cost j);
      first by rewrite /job_response_time_bound /completed_by ZERO.
    eapply uniprocessor_response_time_bound_seq with (L := L) => //.
    - by apply: instantiated_i_and_w_are_coherent_with_schedule.
    - by apply: instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - by apply: instantiated_busy_intervals_are_bounded.
    - by apply: instantiated_task_interference_is_bounded.
    - by apply: response_time_recurrence_solution_exists.
  Qed.

End AbstractRTAforELFwithArrivalCurves.
