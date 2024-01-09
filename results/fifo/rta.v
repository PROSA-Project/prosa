Require Import prosa.model.readiness.basic.
Require Import prosa.model.priority.fifo.
Require Import prosa.analysis.facts.priority.fifo.
Require Export prosa.analysis.abstract.ideal.cumulative_bounds.
Require Export prosa.analysis.facts.busy_interval.carry_in.
Require Import prosa.analysis.facts.model.task_cost.

(** The formal development and the proofs in this file are described in-depth in
    the following paper:

    - Bedarkar et al., _"From Intuition to Coq: A Case Study in Verified
      Response-Time Analysis of FIFO Scheduling"_, RTSS'22.

    The interested reader is invited to follow along in parallel both in the
    paper and here. In particular, the below sections labeled _A_ through _H_
    correspond directly to the equivalently labeled subsections in Section IV of
    the paper. *)


(** * Response-Time Analysis for FIFO Schedulers *)

(** In the following, we derive a response-time analysis for FIFO schedulers,
    assuming a workload of sporadic real-time tasks characterized by arbitrary
    arrival curves executing upon an ideal uniprocessor. To this end, we
    instantiate the _abstract Response-Time Analysis_ (aRTA) as provided in the
    [prosa.analysis.abstract] module. *)

Section AbstractRTAforFIFOwithArrivalCurves.

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

  (** Consider any type of tasks, each characterized by a WCET [task_cost], an arrival
      curve [max_arrivals], and a run-to-completion threshold [task_rtct], ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (** ... and any type of jobs associated with these tasks, where each job has
      an arrival time [job_arrival], a cost [job_cost], and an arbitrary
      preemption model indicated by [job_preemptable]. *)
  Context {Job : JobType} `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** *** The Job Arrival Sequence *)

  (** Consider any arrival sequence [arr_seq] with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** *** Absence of Self-Suspensions and WCET Compliance *)

  (** We assume the classic (i.e., Liu & Layland) model of readiness without
      jitter or self-suspensions, wherein [pending] jobs are always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** We further require that a job's cost cannot exceed its task's stated
      WCET. *)
  Hypothesis H_valid_job_cost : arrivals_have_valid_job_costs arr_seq.

  (** *** The Task Set *)

  (** We consider an arbitrary task set [ts]... *)
  Variable ts : seq Task.

  (** ... and assume that all jobs stem from tasks in this task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Furthermore, we assume that [max_arrivals] is a family of valid arrival
      curves that constrains the arrival sequence [arr_seq], i.e., for any task
      [tsk] in [ts], [max_arrival tsk] is (1) an arrival bound of [tsk], and ... *)
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** ... (2) a monotonic function that equals 0 for the empty interval [delta = 0]. *)
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

  (** Finally, consider any arbitrary, valid ideal uni-processor schedule of the
      given arrival sequence [arr_seq] (and hence the given task set [ts]). *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** We assume that the schedule complies with the preemption model ... *)
  Hypothesis H_valid_preemption_model : valid_preemption_model arr_seq sched.

  (** ... and, last but not least, that it respects the [FIFO] scheduling
          policy. *)
  Hypothesis H_respects_policy_at_preemption_point :
    respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job).


  (** ** B. Encoding the Scheduling Policy and Preemption Model *)

  (** With the system model in place, the next step is to encode the
      scheduling policy and preemption model such that aRTA becomes
      applicable. To this end, we encode the semantics of the
      scheduling policy and preemption model using two functions, by
      convention called [interference] and [interfering_workload]. The
      paper explains the idea behind these two functions and how they
      interact in much more detail. At the code level, we fortunately
      can simply reuse the existing general definitions of
      _interference_ and _interfering workload_ that apply to any
      job-level fixed-priority (JLFP) policy (as provided in the
      module [analysis.abstract.ideal.iw_instantiation]). *)
  #[local] Instance ideal_jlfp_interference : Interference Job :=
    ideal_jlfp_interference arr_seq sched.

  #[local] Instance ideal_jlfp_interfering_workload : InterferingWorkload Job :=
    ideal_jlfp_interfering_workload arr_seq sched.

  (** Please refer to the general definitions (by clicking on the links above)
      to see how they correspond to the definitions provided in Listing 3 of the
      paper (they are identical). *)

  (** ** C. Classic and Abstract Work Conservation *)

  (** The next step is to connect the classic notion of work conservation with
      the abstract notion assumed by aRTA. First, let us recall the abstract and
      classic notations of work conservation as [work_conserving_ab] and
      [work_conserving_cl], respectively. *)
  Let work_conserving_ab := abstract.definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** In the following, we make the standard assumption that the schedule is
      work-conserving in the classic sense. *)
  Hypothesis H_work_conserving : work_conserving_cl.

  (** As explained in much detail in the paper, a general proof obligation of
      aRTA is to show that its abstract notion of work conservation is also
      satisfied. That is, the classic, policy-specific notion assumed in
      [H_work_conserving] needs to be "translated" into the abstract notion
      understood by aRTA. Fortunately, in our case the proof is trivial: as a
      benefit of reusing the general definitions of [interference] and
      [interfering_workload] for JLFP policies, we can reuse the existing
      general lemma [instantiated_i_and_w_are_coherent_with_schedule]. This
      lemma immediately allows us to conclude that the schedule is
      work-conserving in the abstract sense with respect to [interference] and
      [interfering_workload]. *)
  Fact abstractly_work_conserving : work_conserving_ab.
  Proof. exact: instantiated_i_and_w_are_coherent_with_schedule. Qed.

  (** The preceding fact [abstractly_work_conserving] corresponds to Lemma 1 in
      the paper. To see the correspondence, refer to the definition of
      [definitions.work_conserving] (by clicking the link in the above
      definition). *)

  (** ** D. Bounding the Maximum Busy-Window Length *)

  (** The next step is to establish a bound on the maximum busy-window length,
      which aRTA requires to be given. *)

  (** To this end, we assume that we are given a positive value [L] ...*)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.

  (** ... that is a fixed point of the following equation. *)
  Hypothesis H_fixed_point : L = total_request_bound_function ts L.

  (** Given this definition of [L], it is our proof obligation to show that all
      busy windows (in the _abstract_ sense) are indeed bounded by [L]. To this
      end, let us first recall the notion of a bound on the maximum busy-window
      length (or, interchangeably, busy-interval length) as understood by
      aRTA. *)
  Let busy_windows_are_bounded_by L :=
    busy_intervals_are_bounded_by arr_seq sched tsk L.

  (** We observe that the length of any (abstract) busy window in [sched] is
      indeed bounded by [L]. Again, the proof is trivial because we can reuse a
      general lemma, namely [instantiated_busy_intervals_are_bounded] in this
      case, due to the choice to reuse the existing JLFP definitions of
      [interference] and [interfering_workload]. *)
  Fact busy_windows_are_bounded : busy_windows_are_bounded_by L.
  Proof. exact: instantiated_busy_intervals_are_bounded. Qed.

  (** The preceding fact [busy_windows_are_bounded] correspond to Lemma 2 in the
      paper. To clearly see the correspondence, refer to the definition of
      [busy_intervals_are_bounded_by] (by clicking on the link in the definition
      above). *)

  (** ** E. Defining the Interference Bound Function (IBF) *)

  (** Finally, we define the _interference bound function_ ([IBF]). [IBF] bounds
      the cumulative interference incurred by a job in its busy window. In
      general, aRTA expects to reason about an IBF parametric in two parameters,
      a _relative arrival offset_ [A] and an _interval length_ [Δ], as described
      in the paper. In our specific case, for [FIFO] scheduling, only [A] is
      actually relevant. We therefore define [IBF] as the sum, across all
      tasks, of the per-task request-bound functions (RBFs) in the interval [A +
      ε] minus the WCET of the task under analysis [tsk]. *)
  Let IBF tsk (A Δ : duration) :=
        (\sum_(tsko <- ts) task_request_bound_function tsko (A + ε)) - task_cost tsk.

  (** As discussed in the paper, our proof obligation now is to show that the
      stated [IBF] is indeed correct. To this end, we first establish two
      auxiliary lemmas. *)

  (** *** Absence of Priority Inversion *)

  (** Because we reuse the general JLFP notions of [interference] and
      [interfering_workload], which allowed us to save much proof effort in the
      preceding sections, we must reason about priority inversion. While
      priority inversion is _conceptually_ not relevant under FIFO scheduling,
      it clearly is a factor in the general JLFP case, and hence shows up in the
      definitions of [interference] and [interfering_workload]. We therefore
      next show it to be _actually_ impossible, too, by proving that, under FIFO
      scheduling, the cumulative priority inversion experienced by a job [j] in
      any interval within its busy window is always [0]. *)
  Section AbsenceOfPriorityInversion.

    (** Consider any job [j] of the task under analysis [tsk]. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.

    (** Assume that the job has a positive cost (as we later do not need to
        reason about zero-cost jobs). *)
    Hypothesis H_job_cost_positive: job_cost_positive j.

    (** Assume the busy interval of the job [j] is given by <<[t1,t2)>>. *)
    Variable t1 t2 : duration.
    Hypothesis H_busy_interval :
      definitions.busy_interval sched j t1 t2.

    (** Consider any sub-interval <<[t1, t1 + Δ)>> of the busy interval of [j]. *)
    Variable Δ : duration.
    Hypothesis H_Δ_in_busy : t1 + Δ < t2.

    (** We prove that the cumulative priority inversion in the interval <<[t1, t1 + Δ)>>
        is indeed [0]. *)
    Lemma no_priority_inversion:
      cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) = 0.
    Proof.
      apply /eqP; rewrite -leqn0.
      pose zf : nat -> nat := (fun=> 0).
      have: cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) <= zf (job_arrival j - t1);
        last by apply.
      apply: cumulative_priority_inversion_is_bounded => //.
      have -> : priority_inversion_is_bounded_by arr_seq sched tsk zf
               = priority_inversion_is_bounded_by arr_seq sched tsk (constant 0) by [].
      exact: FIFO_implies_no_pi.
    Qed.

  End AbsenceOfPriorityInversion.

  (** *** Higher- and Equal-Priority Interference *)

  (** Next, we establish a bound on the interference produced by higher- and
      equal-priority jobs. *)
  Section BoundOnHEPWorkload.

    (** Consider again a job [j] of the task under analysis [tsk] with a positive cost. *)
    Variable j : Job.
    Hypothesis H_job_of_task : job_of_task tsk j.
    Hypothesis H_j_in_arrivals : arrives_in arr_seq j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** Consider the (abstract) busy window of [j] and denote it as  <<[t1, t2)>>. *)
    Variable t1 t2 : instant.
    Hypothesis H_busy_window :
      definitions.busy_interval sched j t1 t2.

    (** Consider any arbitrary sub-interval <<[t1, Δ)>> within the busy window
        of [j]. *)
    Variable Δ : instant.
    Hypothesis H_in_busy : t1 + Δ < t2.

    (** The cumulative interference from higher- and equal-priority jobs during
        <<[t1, Δ)>> is bounded as follows. *)
    Lemma bound_on_hep_workload :
      cumulative_another_hep_job_interference arr_seq sched j t1 (t1 + Δ) <=
        \sum_(tsko <- ts) task_request_bound_function tsko (job_arrival j - t1 + ε) - task_cost tsk.
    Proof.
      rewrite (cumulative_i_ohep_eq_service_of_ohep arr_seq) => //;
        last by eauto 6 with basic_rt_facts.
      eapply leq_trans; first exact: service_of_jobs_le_workload.
      rewrite (leqRW (workload_equal_subset _ _ _ _ _ _  _)) => //.
      rewrite (workload_minus_job_cost j)//;
        last by apply job_in_arrivals_between => //; apply/andP; split => //; rewrite -addn1.
      rewrite /workload_of_jobs /IBF (big_rem tsk) //=
        (addnC (task_request_bound_function tsk (job_arrival j - t1 + ε))).
      rewrite -addnBA; last first.
      - apply leq_trans with (task_request_bound_function tsk ε);
          first exact: (task_rbf_1_ge_task_cost arr_seq).
        by apply task_rbf_monotone; [apply H_valid_arrival_curve | lia].
      - eapply leq_trans;
          last by erewrite leq_add2l; eapply task_rbf_excl_tsk_bounds_task_workload_excl_j; eauto 1.
        rewrite addnBA.
        + rewrite leq_sub2r //; eapply leq_trans.
          * apply sum_over_partitions_le => j' inJOBS => _.
            by apply H_all_jobs_from_taskset, (in_arrivals_implies_arrived _ _ _ _ inJOBS).
          * rewrite (big_rem tsk) //= addnC leq_add //; last by rewrite subnKC.
            rewrite big_seq_cond [in X in _ <= X]big_seq_cond big_mkcond [in X in _ <= X]big_mkcond //=.
            apply leq_sum => tsk' _; rewrite andbC //=.
            destruct (tsk' \in rem (T:=Task) tsk ts) eqn:IN; last by [].
            apply rem_in in IN.
            eapply leq_trans;
              last by apply (task_workload_le_task_rbf _ _ _ IN H_valid_job_cost H_is_arrival_curve t1).
            by rewrite addnBAC //= subnKC //= addn1; apply leqW.
        + move : H_job_of_task => TSKj.
          rewrite /task_workload_between /task_workload /workload_of_jobs (big_rem j) //=;
            first by rewrite TSKj; apply leq_addr.
          apply job_in_arrivals_between => //.
          by apply /andP; split; [| rewrite subnKC; [rewrite addn1 |]].
    Qed.

  End BoundOnHEPWorkload.

  (** *** Correctness of [IBF]  *)

  (** Combining the bound on interference due to lower-priority jobs
      (priority inversion, i.e., [no_priority_inversion]) and the
      interference due to higher- or equal-priority jobs
      ([bound_on_hep_workload]), we can prove that [IBF] indeed bounds
      the total interference.

      Notice that, unlike the aRTA framework published at ECRTS'20,
      generalized aRTA supports custom parameters for [IBF]. Hence, we
      have to specify that the first argument of [IBF] represents the
      relative arrival time of a job under analysis by passing a
      proposition [relative_arrival_time_of_job_is_A]. *)
  Lemma IBF_correct :
    job_interference_is_bounded_by
      arr_seq sched tsk IBF (relative_arrival_time_of_job_is_A sched).
  Proof.
    move => t1 t2 Δ j ARRj TSKj BUSY IN_BUSY NCOMPL A Pred.
    rewrite fold_cumul_interference cumulative_interference_split //.
    have JPOS: job_cost_positive j by rewrite -ltnNge in NCOMPL; unfold job_cost_positive; lia.
    rewrite (no_priority_inversion j ARRj _ JPOS _ t2) //= add0n.
    have ->: A = job_arrival j - t1 by erewrite Pred with (t1 := t1); [lia | apply BUSY].
    exact: bound_on_hep_workload.
  Qed.

  (** The preceding lemma [IBF_correct] corresponds to Lemma 3 in the paper. To
      see the correspondence more clearly, refer to the definition of
      [job_interference_is_bounded_by] in the above lemma. *)

  (** ** F. Defining the Search Space *)

  (** In this section, we define the concrete search space for [FIFO] and relate
      it to the abstract search space of aRTA. In the case of [FIFO], the concrete
      search space is the set of offsets less than [L] such that there exists a
      task [tsk'] in [ts] such that [r bf tsk' (A) ≠ rbf tsk' (A + ε)]. *)
  Definition is_in_concrete_search_space (A : duration) :=
    (A < L) && has (fun tsk' => task_request_bound_function tsk' (A) !=
                               task_request_bound_function tsk' ( A + ε )) ts.

  (** To enable the use of aRTA, we must now show that any offset [A] included
      in the abstract search space is also included in the concrete search
      space. That is, we must show that the concrete search space is a
      refinement of the abstract search space assumed by aRTA. *)

  (** To this end, first recall the notion of the abstract search space in aRTA. *)
  Let is_in_abstract_search_space A := abstract.search_space.is_in_search_space tsk L IBF A.

  Section SearchSpaceRefinement.

    (** Suppose we are given a job [j] of the task under analysis [tsk] with
        positive cost. We use the existence of such a job in the subsequent
        proof, even if it does not feature in the claim directly. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_positive_cost : 0 < task_cost tsk.

    (** Under this assumption, given any [A] from the _abstract_ search space, ... *)
    Variable A : nat.
    Hypothesis H_in_abstract : is_in_abstract_search_space A.

    (** ... we prove that [A] is also in the concrete search space. In other
        words, we prove that the abstract search space is a subset of the
        concrete search space. *)
    Lemma search_space_refinement : is_in_concrete_search_space A.
    Proof.
      move: H_in_abstract => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
      { subst A.
        apply/andP; split=> [//|].
        apply /hasP. exists tsk => [//|].
        rewrite neq_ltn;apply/orP; left.
        erewrite task_rbf_0_zero; eauto 2.
        rewrite add0n ; apply leq_trans with (task_cost tsk).
        - by eapply leq_trans; eauto 2.
        - exact: task_rbf_1_ge_task_cost. }
      { apply /andP; split=> [//|].
        apply /hasPn.
        move => EQ2. unfold IBF in INSP2.
        rewrite subnK in INSP2 => //.
        apply INSP2; clear INSP2.
        have ->// : \sum_(tsko <- ts) task_request_bound_function tsko A =
                   \sum_(tsko <- ts)  task_request_bound_function tsko (A + ε).
        apply eq_big_seq => //= task IN.
        by move: (EQ2 task IN) => /negPn /eqP. }
    Qed.

    (** The preceding lemma [search_space_refinement] corresponds to Lemma 4 in
        the paper, which is apparent after consulting the definitions of the
        abstract and concrete search spaces. *)

  End SearchSpaceRefinement.

  (** ** G. Stating the Response-Time Bound [R] *)

  (** Having established all necessary preliminaries, it is finally time to
      state the claimed response-time bound [R]. *)
  Variable R : duration.
  Hypothesis H_R_max:
    forall (A : duration),
      is_in_concrete_search_space A ->
      exists (F : nat),
        A + F >= \sum_(tsko <- ts) task_request_bound_function tsko (A + ε) /\
          F <= R.

  (** Ultimately, we seek to apply aRTA to prove the correctness of this [R].
      However, in order to connect the concrete definition of [R] with aRTA, we
      must first restate the bound in the shape of the abstract response-time
      bound equation that aRTA expects, which we do next. *)

  Section ResponseTimeBoundRestated.
    (** Suppose again we are given a job [j] of the task under analysis [tsk]
        with positive cost. We use the existence of such a job in the subsequent
        proof, even if it does not feature in the claim directly. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_of_task tsk j.
    Hypothesis H_job_cost_positive : job_cost_positive j.

    (** We know that:
        - if [A] is in the abstract search space, then it is also in
           the concrete search space; and
        - if [A] is in the concrete search space, then there exists a solution
          that satisfies the inequalities stated in [H_R_is_maximum].
        Using these facts, we prove that, if [A] is in the abstract search
        space, then there also exists a solution [F] to the response-time
        equation as expected by aRTA. *)
    Lemma soln_abstract_response_time_recurrence :
      forall A,
        is_in_abstract_search_space A ->
        exists (F : nat),
          A + F >= task_rtct tsk + IBF tsk A (A + F) /\
            F + (task_cost tsk - task_rtct tsk) <= R.
    Proof.
      move => A IN.
      eapply search_space_refinement in IN => //.
      move: (H_R_max _ IN) => [F [FIX NEQ]].
      have R_GE_TC: task_cost tsk <= R.
      { move : (H_R_max 0) => SEARCH; feed SEARCH;
          first by eapply search_space_refinement => //; left.
        move: SEARCH => [F' [LE1 LE2]].
        rewrite !add0n in LE1.
        rewrite -(leqRW LE2) -(leqRW LE1).
        exact: (task_cost_le_sum_rbf arr_seq). }
      exists (R - (task_cost tsk - task_rtct tsk)); split.
      - rewrite /IBF.
        rewrite (leqRW FIX) addnC -subnA; first last.
        + rewrite -(leqRW FIX).
          apply: (task_cost_le_sum_rbf _ _ _ ) => //.
          by rewrite addn1.
        + by move : H_valid_run_to_completion_threshold => [TASKvalid JOBvalid].
        + rewrite addnBA; first by rewrite leq_sub2r // leq_add2l.
          by apply leq_trans with (task_cost tsk); [lia|].
      - rewrite subnK; first by done.
        by apply leq_trans with (task_cost tsk); [lia| ].
    Qed.

    (** Lemma [soln_abstract_response_time_recurrence] is shown in Listing 3 in
        the paper. *)
  End ResponseTimeBoundRestated.

  (** ** H. Soundness of the Response-Time Bound *)

  (** Finally, we are in a position to establish the soundness of the claimed
      response-time bound [R] by applying the main general aRTA theorem
      [uniprocessor_response_time_bound]. *)
  Theorem uniprocessor_response_time_bound_FIFO:
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    move => js ARRs TSKs.
    rewrite /job_response_time_bound /completed_by.
    case: (posnP (@job_cost _ _ js)) => [ -> |POS]; first by done.
    eapply uniprocessor_response_time_bound_ideal => //.
    - exact: abstractly_work_conserving.
    - exact: busy_windows_are_bounded.
    - exact: IBF_correct.
    - by apply: soln_abstract_response_time_recurrence; eauto.
  Qed.

  (** The preceding theorem [uniprocessor_response_time_bound_FIFO] corresponds
      to Theorem 2 in the paper. The correspondence becomes clearer when referring
      to the definition of [task_response_time_bound], and then in turn to the
      definitions of [job_of_task] and [job_response_time_bound].  *)

End AbstractRTAforFIFOwithArrivalCurves.
