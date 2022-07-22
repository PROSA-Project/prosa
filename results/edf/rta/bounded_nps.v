Require Import prosa.model.readiness.basic.
Require Import prosa.model.priority.edf.
Require Import prosa.model.schedule.work_conserving.
Require Import prosa.model.task.preemption.parameters.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.model.arrival_curves.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.facts.busy_interval.ideal.priority_inversion_bounded.
Require Export prosa.results.edf.rta.bounded_pi.

(** * RTA for EDF  with Bounded Non-Preemptive Segments *)

(** In this section we instantiate the Abstract RTA for EDF-schedulers
    with Bounded Priority Inversion to EDF-schedulers for ideal
    uni-processor model of real-time tasks with arbitrary
    arrival models _and_ bounded non-preemptive segments. *)

(** Recall that Abstract RTA for EDF-schedulers with Bounded Priority
    Inversion does not specify the cause of priority inversion. In
    this section, we prove that the priority inversion caused by
    execution of non-preemptive segments is bounded. Thus the Abstract
    RTA for EDF-schedulers is applicable to this instantiation. *)
Section RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskRunToCompletionThreshold Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{Arrival : JobArrival Job}.
  Context `{Cost : JobCost Job}.

  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For clarity, let's denote the relative deadline of a task as [D]. *)
  Let D tsk := task_deadline tsk.

  (** Consider the EDF policy that indicates a higher-or-equal priority relation.
     Note that we do not relate the EDF policy with the scheduler. However, we 
     define functions for Interference and Interfering Workload that actively use
     the concept of priorities. *)
  Let EDF := EDF Job.

  (** Consider any arrival sequence with consistent, non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.
  
  (** Next, consider any valid ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_sched_valid : valid_schedule sched arr_seq.
  
  (** In addition, we assume the existence of a function mapping jobs
      to their preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption model with
      bounded non-preemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and the schedule respects the scheduling policy at every preemption point. *)
  Hypothesis H_respects_policy : respects_JLFP_policy_at_preemption_point arr_seq sched EDF.

  (** Consider an arbitrary task set ts, ... *)
  Variable ts : list Task.

  (** ... assume that all jobs come from the task set, ... *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** ... and the cost of a job cannot be larger than the task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for
     any task [tsk] in ts [max_arrival tsk] is (1) an arrival bound of
     [tsk], and (2) it is a monotonic function that equals 0 for the
     empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
  Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider a valid preemption model... *)
  Hypothesis H_valid_preemption_model:
    valid_preemption_model arr_seq sched.

  (** ...and a valid task run-to-completion threshold function. That
     is, [task_rtct tsk] is (1) no bigger than [tsk]'s cost, (2) for
     any job of task [tsk] [job_rtct] is bounded by [task_rtct]. *)
  Hypothesis H_valid_run_to_completion_threshold:
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** We introduce as an abbreviation [rbf] for the task request bound function,
     which is defined as [task_cost(T) × max_arrivals(T,Δ)] for a task T. *)
  Let rbf := task_request_bound_function.
  
  (** Next, we introduce [task_rbf] as an abbreviation for the task
     request bound function of task [tsk]. *)
  Let task_rbf := rbf tsk.
  
  (** Using the sum of individual request bound functions, we define the request bound 
     function of all tasks (total request bound function). *)
  Let total_rbf := total_request_bound_function ts.
  
  (** Next, we define an upper bound on interfering workload received from jobs 
     of other tasks with higher-than-or-equal priority. *)
  Let bound_on_total_hep_workload  A Δ :=
    \sum_(tsk_o <- ts | tsk_o != tsk)
     rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

  (** Let's define some local names for clarity. *)
  Let max_length_of_priority_inversion :=
    max_length_of_priority_inversion arr_seq.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.

  (** For a job with the relative arrival offset [A] within its busy window, we
      define the following blocking bound. Only other tasks that potentially
      release non-zero-cost jobs are relevant, so we define a predicate to
      exclude pathological cases. *)
  Definition blocking_relevant (tsk_o : Task) :=
    (max_arrivals tsk_o ε > 0) && (task_cost tsk_o > 0).
  Definition blocking_bound (A : duration)  :=
    \max_(tsk_o <- ts | blocking_relevant tsk_o && (D tsk_o > D tsk + A))
     (task_max_nonpreemptive_segment tsk_o - ε).

  (** ** Search Space *)

  (** If priority inversion is caused exclusively by non-preemptive sections,
      then we do not need to consider the priority-inversion bound in the search
      space. Hence we define the following search space, which refines the more
      general [bounded_pi.is_in_search_space] for our specific setting. *)
  Definition is_in_search_space (L A : duration) :=
    (A < L) && (task_rbf_changes_at tsk A
                || bound_on_total_hep_workload_changes_at ts tsk A).

  (** For the following proof, we exploit the fact that the blocking bound is
      monotonically decreasing in [A], which we note here. *)
  Fact blocking_bound_decreasing :
    forall A1 A2,
      A1 <= A2 ->
      blocking_bound A1 >= blocking_bound A2.
  Proof.
    move=> A1 A2 LEQ.
    rewrite /blocking_bound.
    apply: bigmax_subset => tsk_o IN /andP[/andP[OTHER LT] ARR].
    by repeat (apply /andP; split) => //; lia.
  Qed.

  (** To use the refined search space with the abstract theorem, we must show
      that it still includes all relevant points. To this end, we first observe
      that a step in the blocking bound implies the existence of a task that
      could release a job with an absolute deadline equal to the absolute
      deadline of the job under analysis. *)
  Lemma task_with_equal_deadline_exists :
    forall {A},
      priority_inversion_changes_at blocking_bound A ->
      exists tsk_o, (tsk_o \in ts)
                 && (blocking_relevant tsk_o)
                 && (tsk_o != tsk)
                 && (D tsk_o == D tsk + A).
  Proof.
    move=> A. rewrite /priority_inversion_changes_at => NEQ.
    have LEQ: blocking_bound A <= blocking_bound (A - ε) by apply: blocking_bound_decreasing; lia.
    have LT: blocking_bound A < blocking_bound (A - ε) by lia.
    move: LT; rewrite /blocking_bound => LT {LEQ} {NEQ}.
    move: (bigmax_witness_diff LT) => [tsk_o [IN [NOT HOLDS]]].
    move: HOLDS => /andP[REL LTeps].
    exists tsk_o; repeat (apply /andP; split) => //;
      first by apply /eqP => EQ; move: LTeps; rewrite EQ; lia.
    move: NOT; rewrite negb_and => /orP[/negP // |].
    by move: LTeps; rewrite /ε => LTeps; lia.
  Qed.

  (** With the above setup in place, we can show that the search space defined
      above by [is_in_search_space] covers the the more abstract search space
      defined by [bounded_pi.is_in_search_space]. *)
  Lemma search_space_inclusion :
     forall {A L},
       bounded_pi.is_in_search_space ts tsk blocking_bound L A ->
       is_in_search_space L A.
   Proof.
     move=> A L /andP[BOUND STEP].
     apply /andP; split => //; apply /orP.
     move: STEP => /orP[/orP[STEP|RBF] | IBF]; [right| by left| by right].
     move: (task_with_equal_deadline_exists STEP) => [tsk_o /andP[/andP[/andP[IN REL] OTHER] EQ]].
     rewrite /bound_on_total_hep_workload_changes_at.
     apply /hasP; exists tsk_o => //.
     apply /andP; split; first by rewrite eq_sym.
     move: EQ. rewrite /D => /eqP EQ.
     rewrite /task_request_bound_function EQ.
     move: REL; rewrite /blocking_relevant => /andP [ARRIVES COST].
     rewrite eqn_pmul2l //.
     have -> : A + task_deadline tsk - (task_deadline tsk + A)
              = 0 by lia.
     have -> : A + ε + task_deadline tsk - (task_deadline tsk + A)
              = ε by lia.
     by move: (H_valid_arrival_curve tsk_o IN) => [-> _]; lia.
   Qed.


  (** ** Priority inversion is bounded *)
  (** In this section, we prove that a priority inversion for task [tsk] is bounded by 
      the maximum length of non-preemptive segments among the tasks with lower priority. *)
  Section PriorityInversionIsBounded.

    (** First, we observe that the maximum non-preemptive segment length of any
        task that releases a job with an earlier absolute deadline (w.r.t. a
        given job [j]) and non-zero execution cost upper-bounds the maximum
        possible length of priority inversion (of said job [j]).  *)
    Lemma priority_inversion_is_bounded_by_max_np_segment :
      forall {j t1},
        max_length_of_priority_inversion j t1
        <= \max_(j_lp <- arrivals_between arr_seq 0 t1 | (~~ EDF j_lp j)
                                                         && (job_cost j_lp > 0))
           (task_max_nonpreemptive_segment (job_task j_lp) - ε).
    Proof.
      move=> j t1.
      rewrite /max_length_of_priority_inversion /max_length_of_priority_inversion.
      apply: leq_big_max => j' JINB NOTHEP.
      rewrite leq_sub2r //.
      apply in_arrivals_implies_arrived in JINB.
      by apply H_valid_model_with_bounded_nonpreemptive_segments.
    Qed.

    (** Second, we prove that the maximum length of a priority inversion of a
        given job [j] is indeed bounded by defined the blocking bound. *)
    Lemma priority_inversion_is_bounded_by_blocking:
      forall j t1 t2,
        arrives_in arr_seq j ->
        job_of_task tsk j ->
        busy_interval_prefix  arr_seq sched j t1 t2 ->
        max_length_of_priority_inversion j t1 <= blocking_bound (job_arrival j - t1).
    Proof.
      intros j t1 t2 ARR TSK BUSY; unfold max_length_of_priority_inversion, blocking_bound.
      destruct BUSY as [TT [QT [_ LE]]]; move: LE => /andP [GE LT].
      apply: leq_trans; first by apply: priority_inversion_is_bounded_by_max_np_segment.
      apply /bigmax_leq_seqP => j' JINB NOTHEP.
      have ARR': arrives_in arr_seq j'
        by apply: in_arrivals_implies_arrived; exact: JINB.
      apply leq_bigmax_cond_seq with (x := (job_task j')) (F := fun tsk => task_max_nonpreemptive_segment tsk - 1);
        first by apply H_all_jobs_from_taskset.
      eapply in_arrivals_implies_arrived_between in JINB; last by eauto 2.
      move: JINB; move => /andP [_ TJ'].
      repeat (apply/andP; split); last first.
      { rewrite /EDF -ltnNge in NOTHEP.
        move: TSK => /eqP <-.
        have ARRLE: job_arrival j' < job_arrival j by apply leq_trans with t1.
        move: NOTHEP; rewrite /job_deadline /absolute_deadline.job_deadline_from_task_deadline /D.
        by lia. }
      { move: NOTHEP => /andP [_ NZ].
        move: (H_valid_job_cost j' ARR'); rewrite /valid_job_cost.
        by lia. }
      { apply: non_pathological_max_arrivals; last first.
          - exact: ARR'.
          - by rewrite /job_of_task.
          - by apply H_is_arrival_curve, H_all_jobs_from_taskset, ARR'. }
    Qed.

    (** Using the lemma above, we prove that the priority inversion of the task is bounded by 
       the maximum length of a nonpreemptive section of lower-priority tasks. *)
    Lemma priority_inversion_is_bounded:
      priority_inversion_is_bounded_by arr_seq sched tsk blocking_bound.
    Proof.
      move => j ARR TSK POS t1 t2 PREF; move: (PREF) => [_ [_ [_ /andP [T _]]]].
      move: H_sched_valid => [COARR MBR].
      destruct (leqP (t2 - t1) (blocking_bound (job_arrival j - t1))) as [NEQ|NEQ].
      { apply leq_trans with (t2 - t1); last by done.
        rewrite /cumulative_priority_inversion.
        rewrite -[X in _ <= X]addn0 -[t2 - t1]mul1n -iter_addn -big_const_nat. 
        by rewrite leq_sum //; intros t _; destruct (priority_inversion_dec).
      }
      edestruct @preemption_time_exists as [ppt [PPT NEQ2]]; rt_eauto.
      move: NEQ2 => /andP [GE LE].
      apply leq_trans with (cumulative_priority_inversion arr_seq sched j t1 ppt);
        last apply leq_trans with (ppt - t1).
      - rewrite /cumulative_priority_inversion. 
        rewrite (@big_cat_nat _ _ _ ppt) //=; last first.
        { rewrite ltn_subRL in NEQ.
          apply leq_trans with (t1 + blocking_bound (job_arrival j - t1)); last by apply ltnW. 
          apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
          by rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2; apply/eqP. }
        rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
        rewrite big_nat_cond big1 //; move => t /andP [/andP [GEt LTt] _ ].
        edestruct @not_quiet_implies_exists_scheduled_hp_job
          with (K := ppt - t1) (t := t) as [j_hp [ARRB [HP SCHEDHP]]]; rt_eauto.
        { by exists ppt; split; [done | rewrite subnKC //; apply/andP; split]. } 
        { by rewrite subnKC //; apply/andP; split. }
        apply/eqP; rewrite eqb0; apply/negP; move => /priority_inversion_P INV.
        feed_n 3 INV; rt_eauto; last move: INV => [_ [j_lp /andP[SCHED PRIO]]].
        enough (EQ : j_lp = j_hp); first by subst; rewrite HP in PRIO.
        by eapply ideal_proc_model_is_a_uniprocessor_model; rt_eauto. 
      - rewrite /cumulative_priority_inversion. 
        rewrite -[X in _ <= X]addn0 -[ppt - t1]mul1n -iter_addn -big_const_nat. 
        by rewrite leq_sum //; intros t _; destruct (priority_inversion_dec).
      - rewrite leq_subLR.
        apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
        by rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2; apply/eqP.
    Qed.
    
  End PriorityInversionIsBounded.
        
  (** ** Response-Time Bound *)
  (** In this section, we prove that the maximum among the solutions of the response-time 
      bound recurrence is a response-time bound for [tsk]. *)
  Section ResponseTimeBound.

    (** Let L be any positive fixed point of the busy interval recurrence. *)
    Variable L : duration.
    Hypothesis H_L_positive : L > 0.
    Hypothesis H_fixed_point : L = total_rbf L.
    
    (** Consider any value [R], and assume that for any given arrival
        offset [A] in the search space, there is a solution of the
        response-time bound recurrence which is bounded by [R]. *)
    Variable R : duration.
    Hypothesis H_R_is_maximum:
      forall (A : duration),
        is_in_search_space L A ->
        exists (F : duration),
          A + F >= blocking_bound A
                  + (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk))
                  + bound_on_total_hep_workload  A (A + F) /\
          R >= F + (task_cost tsk - task_rtct tsk).

    (** Then, using the results for the general RTA for EDF-schedulers, we establish a 
         response-time bound for the more concrete model of bounded nonpreemptive segments.
         Note that in case of the general RTA for EDF-schedulers, we just _assume_ that 
         the priority inversion is bounded. In this module we provide the preemption model
         with bounded nonpreemptive segments and _prove_ that the priority inversion is 
         bounded. *)
    Theorem uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments:
      response_time_bounded_by tsk R.
    Proof.
      eapply uniprocessor_response_time_bound_edf; rt_eauto.
      - by  apply priority_inversion_is_bounded.
      - move=> A BPI_SP.
        by apply H_R_is_maximum, search_space_inclusion.
    Qed.

  End ResponseTimeBound.

End RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.
