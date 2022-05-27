From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Require Export prosa.analysis.facts.priority.edf.
Require Export prosa.analysis.definitions.schedulability.
Require Import prosa.model.readiness.basic.
Require Import prosa.model.priority.edf.
Require Import prosa.model.task.absolute_deadline.
Require Import prosa.analysis.abstract.ideal_jlfp_rta.
Require Import prosa.analysis.facts.busy_interval.carry_in.
Require Import prosa.analysis.facts.readiness.basic.


(** * Abstract RTA for EDF-schedulers with Bounded Priority Inversion *)
(** In this module we instantiate the Abstract Response-Time analysis
    (aRTA) to EDF-schedulers for ideal uni-processor model of
    real-time tasks with arbitrary arrival models. *)

(** Given EDF priority policy and an ideal uni-processor scheduler
    model, we can explicitly specify [interference],
    [interfering_workload], and [interference_bound_function]. In this
    settings, we can define natural notions of service, workload, busy
    interval, etc. The important feature of this instantiation is that
    we can induce the meaningful notion of priority
    inversion. However, we do not specify the exact cause of priority
    inversion (as there may be different reasons for this, like
    execution of a non-preemptive segment or blocking due to resource
    locking). We only assume that that a priority inversion is
    bounded. *)

Section AbstractRTAforEDFwithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskRunToCompletionThreshold Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.


  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context {Arrival : JobArrival Job}.
  Context {Cost : JobCost Job}.
  Context `{JobPreemptable Job}. 
  
  (** We assume the classic (i.e., Liu & Layland) model of readiness
      without jitter or self-suspensions, wherein pending jobs are
      always ready. *)
  #[local] Existing Instance basic_ready_instance.

  (** For clarity, let's denote the relative deadline of a task as D. *)
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

  (** Note that we differentiate between abstract and 
     classical notions of work conserving schedule. *)
  Let work_conserving_ab := definitions.work_conserving arr_seq sched.
  Let work_conserving_cl := work_conserving.work_conserving arr_seq sched.

  (** We assume that the schedule is a work-conserving schedule 
     in the _classical_ sense, and later prove that the hypothesis 
     about abstract work-conservation also holds. *)
  Hypothesis H_work_conserving : work_conserving_cl.
  
  (** Assume that a job cost cannot be larger than a task cost. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.
  
  (** Assume we have sequential tasks, i.e, jobs from the 
      same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.
  
  (** Consider an arbitrary task set ts. *)
  Variable ts : list Task.

  (** Next, we assume that all jobs come from the task set. *)
  Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task [tsk] in ts 
     [max_arrival tsk] is (1) an arrival bound of [tsk], and (2) it is a monotonic function 
     that equals 0 for the empty interval delta = 0. *)
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

  (** We introduce [rbf] as an abbreviation of the task request bound function,
     which is defined as [task_cost(T) × max_arrivals(T,Δ)] for some task T. *)
  Let rbf  := task_request_bound_function.
  
  (** Next, we introduce [task_rbf] as an abbreviation 
     of the task request bound function of task [tsk]. *)
  Let task_rbf := rbf tsk.

  (** Using the sum of individual request bound functions, we define the request bound 
       function of all tasks (total request bound function). *)
  Let total_rbf := total_request_bound_function ts.

  (** Assume that there exists a bound on the length of any priority inversion experienced 
     by any job of task [tsk]. Since we analyze only task [tsk], we ignore the lengths of priority 
     inversions incurred by any other tasks.*)
  Variable priority_inversion_bound: duration -> duration.
  Hypothesis H_priority_inversion_is_bounded:
    priority_inversion_is_bounded_by
     arr_seq sched tsk priority_inversion_bound.

  (** Let L be any positive fixed point of the busy interval recurrence. *)
  Variable L : duration.
  Hypothesis H_L_positive : L > 0.
  Hypothesis H_fixed_point : L = total_rbf L.

  (** Next, we define an upper bound on interfering workload received from jobs 
     of other tasks with higher-than-or-equal priority. *)
  Let bound_on_total_hep_workload (A Δ : duration) :=
    \sum_(tsk_o <- ts | tsk_o != tsk)
     rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

  (** To reduce the time complexity of the analysis, we introduce the notion of search space for EDF.
     Intuitively, this corresponds to all "interesting" arrival offsets that the job under
     analysis might have with regard to the beginning of its busy-window. *) 

  (** In the case of the search space for EDF, we consider three conditions.
      First, we ask whether [task_rbf A ≠ task_rbf (A + ε)]. *)
  Definition task_rbf_changes_at (A : duration) := task_rbf A != task_rbf (A + ε).

  (** Second, we ask whether there exists a task [tsko] from ts such that [tsko
      ≠ tsk] and [rbf(tsko, A + D tsk - D tsko) ≠ rbf(tsko, A + ε + D tsk - D
      tsko)].  Note that we use a slightly uncommon notation [has (λ tsko ⇒ P
      tskₒ) ts], which can be interpreted as follows: the task set [ts] contains
      a task [tsko] such that a predicate [P] holds for [tsko]. *)
  Definition bound_on_total_hep_workload_changes_at A :=
    has (fun tsko =>
           (tsk != tsko)
             && (rbf tsko (A + D tsk - D tsko)
                     != rbf tsko ((A + ε) + D tsk - D tsko))) ts.

  (** Third, we ask whether [priority_inversion_bound (A - ε) ≠ priority_inversion_bound A]. *)
  Definition priority_inversion_changes_at (A : duration) :=
    priority_inversion_bound (A - ε) != priority_inversion_bound A.

  (** The final search space for EDF is a set of offsets that are less than [L]
      and where [priority_inversion_bound], [task_rbf], or
      [bound_on_total_hep_workload] changes in value. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && (priority_inversion_changes_at A
                || task_rbf_changes_at A
                || bound_on_total_hep_workload_changes_at A).

  (** Let [R] be a value that upper-bounds the solution of each
      response-time recurrence, i.e., for any relative arrival time [A]
      in the search space, there exists a corresponding solution [F]
      such that [R >= F + (task cost - task lock-in service)]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum: 
    forall (A : duration),
      is_in_search_space A -> 
      exists (F : duration),
        A + F >= priority_inversion_bound A
                + (task_rbf (A + ε) - (task_cost tsk - task_rtct tsk))
                + bound_on_total_hep_workload  A (A + F) /\
        R >= F + (task_cost tsk - task_rtct tsk).
  
  (** To use the theorem uniprocessor_response_time_bound_seq from the Abstract RTA module, 
     we need to specify functions of interference, interfering workload and [IBF_other].  *)

  (** Instantiation of Interference *)
  (** We say that job j incurs interference at time t iff it cannot execute due to 
     a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. *)
  Let interference (j : Job) (t : instant) :=
    ideal_jlfp_rta.interference sched j t.

  (** Instantiation of Interfering Workload *)
  (** The interfering workload, in turn, is defined as the sum of the priority inversion 
     function and interfering workload of jobs with higher or equal priority. *)
  Let interfering_workload (j : Job) (t : instant) :=
    ideal_jlfp_rta.interfering_workload arr_seq sched j t.

  (** Finally, we define the interference bound function ([IBF_other]). [IBF_other] bounds 
      the interference if tasks are sequential. Since tasks are sequential, we exclude 
      interference from other jobs of the same task. For EDF, we define [IBF_other] as 
      the sum of the priority interference bound and the higher-or-equal-priority workload. *)
  Let IBF_other (A R : duration) := priority_inversion_bound A + bound_on_total_hep_workload A R.

  (** ** Filling Out Hypothesis Of Abstract RTA Theorem *)
  (** In this section we prove that all hypotheses necessary 
      to use the abstract theorem are satisfied. *)
  Section FillingOutHypothesesOfAbstractRTATheorem.

    (** First, we prove that in the instantiation of interference and interfering workload, 
       we really take into account everything that can interfere with [tsk]'s jobs, and thus, 
       the scheduler satisfies the abstract notion of work conserving schedule. *)
    Lemma instantiated_i_and_w_are_coherent_with_schedule:
      work_conserving_ab tsk interference interfering_workload.
    Proof.
      unfold EDF in *.
      intros j t1 t2 t ARR TSK POS BUSY NEQ; split; intros HYP;
        [move: HYP => /negP | rewrite scheduled_at_def in HYP; move: HYP => /eqP HYP ].
      move: H_sched_valid => [CARR MBR].
      { rewrite negb_or /is_priority_inversion /is_priority_inversion
                /is_interference_from_another_hep_job. 
        move => /andP [HYP1 HYP2].
        ideal_proc_model_sched_case_analysis_eq sched t jo.
        { exfalso; clear HYP1 HYP2.
          eapply instantiated_busy_interval_equivalent_busy_interval in BUSY; rt_eauto.
          move: BUSY => [PREF _].
          by eapply not_quiet_implies_not_idle; rt_eauto. }
        { clear EqSched_jo; move: Sched_jo; rewrite scheduled_at_def; move => /eqP EqSched_jo.
          rewrite EqSched_jo in HYP1, HYP2. 
          move: HYP1 HYP2.
          rewrite Bool.negb_involutive negb_and.
          move => HYP1 /orP [/negP HYP2| /eqP HYP2].
          - by exfalso.
          - rewrite Bool.negb_involutive in HYP2.
            move: HYP2 => /eqP /eqP HYP2.
              by subst jo; rewrite scheduled_at_def EqSched_jo. 
        }
      }
      { apply/negP;
          rewrite /interference /ideal_jlfp_rta.interference /is_priority_inversion
                  /is_interference_from_another_hep_job 
                  HYP negb_or; apply/andP; split.
        - by rewrite Bool.negb_involutive; eapply (EDF_is_reflexive 0).
        - by rewrite negb_and Bool.negb_involutive; apply/orP; right.
      }
    Qed.

    (** Next, we prove that the interference and interfering workload 
       functions are consistent with sequential tasks. *)
    Lemma instantiated_interference_and_workload_consistent_with_sequential_tasks:
      interference_and_workload_consistent_with_sequential_tasks
        arr_seq sched tsk interference interfering_workload.          
    Proof.
      unfold EDF in *.
      intros j t1 t2 ARR TSK POS BUSY.
      move: H_sched_valid => [CARR MBR].
      eapply instantiated_busy_interval_equivalent_busy_interval in BUSY; rt_eauto.
      eapply all_jobs_have_completed_equiv_workload_eq_service; rt_eauto.
      intros s INs TSKs.
      rewrite /arrivals_between in INs. 
      move: (INs) => NEQ.
      eapply in_arrivals_implies_arrived_between in NEQ; eauto 2.
      move: NEQ => /andP [_ JAs].
      move: (BUSY) => [[ _ [QT [_ /andP [JAj _]]] _]].
      apply QT; try done.
      - eapply in_arrivals_implies_arrived; eauto 2.
      - unfold edf.EDF, EDF; move: TSK TSKs => /eqP TSK /eqP TSKs.
        rewrite /job_deadline /job_deadline_from_task_deadline /hep_job TSK TSKs leq_add2r.
          by apply leq_trans with t1; [apply ltnW | ].
    Qed.

    (** Recall that L is assumed to be a fixed point of the busy interval recurrence. Thanks to
       this fact, we can prove that every busy interval (according to the concrete definition) 
       is bounded. In addition, we know that the conventional concept of busy interval and the 
       one obtained from the abstract definition (with the interference and interfering 
       workload) coincide. Thus, it follows that any busy interval (in the abstract sense) 
       is bounded. *)
    Lemma instantiated_busy_intervals_are_bounded:
      busy_intervals_are_bounded_by arr_seq sched tsk interference interfering_workload L.
    Proof.
      unfold EDF in *.
      intros j ARR TSK POS.
      move: H_sched_valid => [CARR MBR].
      edestruct exists_busy_interval_from_total_workload_bound
        with (Δ := L) as [t1 [t2 [T1 [T2 GGG]]]]; rt_eauto.
      { by intros; rewrite {2}H_fixed_point; apply total_workload_le_total_rbf. }
      exists t1, t2; split; first by done.
      split; first by done.
      by eapply instantiated_busy_interval_equivalent_busy_interval; rt_eauto.
    Qed.
    
    (** Next, we prove that [IBF_other] is indeed an interference bound. *)
    Section TaskInterferenceIsBoundedByIBF_other.

      (** We show that task_interference_is_bounded_by is bounded by [IBF_other] by 
          constructing a sequence of inequalities. *) 
      Section Inequalities.

        (** Consider an arbitrary job j of [tsk]. *)
        Variable j : Job.
        Hypothesis H_j_arrives : arrives_in arr_seq j.
        Hypothesis H_job_of_tsk : job_of_task tsk j.
        Hypothesis H_job_cost_positive: job_cost_positive j.

        (** Consider any busy interval <<[t1, t2)>> of job [j]. *)
        Variable t1 t2 : duration.
        Hypothesis H_busy_interval :
          definitions.busy_interval sched interference interfering_workload j t1 t2.

        (** Let's define A as a relative arrival time of job j (with respect to time t1). *)
        Let A := job_arrival j - t1.

        (** Consider an arbitrary shift Δ inside the busy interval ...  *)
        Variable Δ : duration.
        Hypothesis H_Δ_in_busy : t1 + Δ < t2.

        (** ... and the set of all arrivals between [t1] and [t1 + Δ]. *)
        Let jobs := arrivals_between arr_seq t1 (t1 + Δ).
        
        (** Next, we define two predicates on jobs by extending EDF-priority relation. *)

        (** Predicate [EDF_from tsk] holds true for any job [jo] of
            task [tsk] such that [job_deadline jo <= job_deadline j]. *)
        Let EDF_from (tsk : Task) := fun (jo : Job) => EDF jo j && (job_task jo == tsk).

        (** Predicate [EDF_not_from tsk] holds true for any job [jo]
            such that [job_deadline jo <= job_deadline j] and [job_task jo ≠ tsk]. *)
        Let EDF_not_from (tsk : Task) := fun (jo : Job) => EDF jo j && (job_task jo != tsk).
        
        (** Recall that [IBF_other(A, R) := priority_inversion_bound +
            bound_on_total_hep_workload(A, R)]. The fact that
            [priority_inversion_bound] bounds cumulative priority inversion 
            follows from assumption [H_priority_inversion_is_bounded]. *)
        Lemma cumulative_priority_inversion_is_bounded:
          cumulative_priority_inversion sched j t1 (t1 + Δ) <= priority_inversion_bound (job_arrival j - t1).
        Proof.
          unfold priority_inversion_is_bounded_by, EDF in *.
          move: H_sched_valid => [CARR MBR].
          apply leq_trans with (cumulative_priority_inversion sched j t1 t2).
          - rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1  + Δ)) //=.
            + by rewrite leq_addr.
            + by rewrite /is_priority_inversion leq_addr.
            + by rewrite ltnW.
          - apply H_priority_inversion_is_bounded; try done.
            eapply instantiated_busy_interval_equivalent_busy_interval in H_busy_interval; rt_eauto.
            by move: H_busy_interval => [PREF _].
        Qed.

        (** Next, we show that [bound_on_total_hep_workload(A, R)] bounds 
            interference from jobs with higher-or-equal priority. *)
        
        (** From lemma
            [instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks]
            it follows that cumulative interference from jobs with
            higher-or-equal priority from other tasks is equal to the
            total service of jobs with higher-or-equal priority from
            other tasks. Which in turn means that cumulative
            interference is bounded by service. *)
        Lemma cumulative_interference_is_bounded_by_total_service:
          cumulative_interference_from_hep_jobs_from_other_tasks sched j t1 (t1 + Δ)
          <= service_of_jobs sched (EDF_not_from tsk) jobs t1 (t1 + Δ).
        Proof.
          move: (H_busy_interval) => [[/andP [JINBI JINBI2] [QT _]] _].
          move: H_sched_valid => [CARR MBR].
          erewrite instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks;
            rt_eauto.
          - by move: (H_job_of_tsk) => /eqP ->; rewrite /jobs.
          - by rewrite instantiated_quiet_time_equivalent_quiet_time; rt_eauto.
        Qed.

        (** By lemma [service_of_jobs_le_workload], the total
            _service_ of jobs with higher-or-equal priority from other
            tasks is at most the total _workload_ of jobs with
            higher-or-equal priority from other tasks. *)
        Lemma total_service_is_bounded_by_total_workload:
          service_of_jobs sched (EDF_not_from tsk) jobs t1 (t1 + Δ)
          <= workload_of_jobs (EDF_not_from tsk) jobs.
        Proof.
            by apply service_of_jobs_le_workload; rt_eauto.
        Qed.

        (** Next, we prove that the total workload of jobs
            with higher-or-equal priority from other tasks is bounded by
            the sum over all tasks [tsk_o] that are not equal to task
            [tsk] of workload of jobs with higher-or-equal priority from
            task [tsk_o].*)
        Lemma reorder_summation:
          workload_of_jobs (EDF_not_from tsk) jobs
          <= \sum_(tsk_o <- ts | tsk_o != tsk) workload_of_jobs (EDF_from tsk_o) jobs.
        Proof.
          unfold EDF_from.
          move: (H_busy_interval) => [[/andP [JINBI JINBI2] [QT _]] _].
          intros.
          rewrite (exchange_big_dep (EDF_not_from tsk)) //=.
          - rewrite /workload_of_jobs big_seq_cond [X in _ <= X]big_seq_cond.
            apply leq_sum; move => jo /andP [ARRo /andP [HEQ TSKo]].
            rewrite (big_rem (job_task jo)) //=.
            rewrite /EDF_from HEQ eq_refl TSKo andTb andTb leq_addr //.
          - eapply H_all_jobs_from_taskset, in_arrivals_implies_arrived; eauto 2.
          - move => tsko jo /negP NEQ /andP [EQ1 /eqP EQ2].
            rewrite /EDF_not_from EQ1 Bool.andb_true_l; apply/negP; intros CONTR.
            apply: NEQ; clear EQ1.
              by rewrite -EQ2.
        Qed.

        (** Next we focus on one task [tsk_o ≠ tsk] and consider two cases. *)
        
        (** Case 1: [Δ ≤ A + ε + D tsk - D tsk_o]. *)
        Section Case1.

          (** Consider an arbitrary task [tsk_o ≠ tsk] from [ts]. *)
          Variable tsk_o : Task.
          Hypothesis H_tsko_in_ts: tsk_o \in ts.
          Hypothesis H_neq: tsk_o != tsk.
          
          (** And assume that [Δ ≤ A + ε + D tsk - D tsk_o]. *)
          Hypothesis H_Δ_le: Δ <= A + ε + D tsk - D tsk_o.

          (** Then by definition of [rbf], the total workload of jobs
              with higher-or-equal priority from task [tsk_o] is
              bounded [rbf(tsk_o, Δ)].  *)
          Lemma workload_le_rbf:
            workload_of_jobs (EDF_from tsk_o) jobs <= rbf tsk_o Δ.
          Proof.
            unfold workload_of_jobs, EDF_from.
            apply leq_trans with (task_cost tsk_o * number_of_task_arrivals arr_seq tsk_o t1 (t1 + Δ)).
            { apply leq_trans with (\sum_(j0 <- arrivals_between arr_seq t1 (t1 + Δ) | job_task j0 == tsk_o)
                                     job_cost j0).
              { rewrite big_mkcond [X in _ <= X]big_mkcond //= leq_sum //.
                  by intros s _; case (job_task s == tsk_o); case (EDF s j). }
              { rewrite /number_of_task_arrivals /task.arrivals.number_of_task_arrivals
                -sum1_size big_distrr /= big_filter  muln1.
                apply leq_sum_seq; move => jo IN0 /eqP EQ.
                  by rewrite -EQ; apply H_valid_job_cost; apply in_arrivals_implies_arrived in IN0.
              }
            }
            { rewrite leq_mul2l; apply/orP; right.
              rewrite -{2}[Δ](addKn t1).
                by apply H_is_arrival_curve; auto using leq_addr.
            }
          Qed.

        End Case1.

        (** Case 2: [A + ε + D tsk - D tsk_o ≤ Δ]. *)
        Section Case2.

          (** Consider an arbitrary task [tsk_o ≠ tsk] from [ts]. *)
          Variable tsk_o : Task.
          Hypothesis H_tsko_in_ts: tsk_o \in ts.
          Hypothesis H_neq: tsk_o != tsk.

          (** And assume that [A + ε + D tsk - D tsk_o ≤ Δ]. *)
          Hypothesis H_Δ_ge: A + ε + D tsk - D tsk_o <= Δ.

          (** Important step. *)
          (** Next we prove that the total workload of jobs with
              higher-or-equal priority from task [tsk_o] over time
              interval [t1, t1 + Δ] is bounded by workload over time
              interval [t1, t1 + A + ε + D tsk - D tsk_o]. 
              The intuition behind this inequality is that jobs which arrive 
              after time instant [t1 + A + ε + D tsk - D tsk_o] has smaller priority than job [j] due to 
              the term [D tsk - D tsk_o]. *)
          Lemma total_workload_shorten_range:
            workload_of_jobs (EDF_from tsk_o) (arrivals_between arr_seq t1 (t1 + Δ)) 
            <= workload_of_jobs (EDF_from tsk_o) (arrivals_between arr_seq t1 (t1 + (A + ε + D tsk - D tsk_o))).
          Proof.
            unfold workload_of_jobs, EDF_from.
            move: (H_busy_interval) => [[/andP [JINBI JINBI2] [QT _]] _].
            set (V := A + ε + D tsk - D tsk_o) in *.
            rewrite (arrivals_between_cat _ _ (t1 + V)); [ |rewrite leq_addr //|rewrite leq_add2l //].
            rewrite big_cat //=. 
            rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
            rewrite big_seq_cond.
            apply/eqP; apply big_pred0.
            intros jo; apply/negP; intros CONTR.
            move: CONTR => /andP [ARRIN /andP [HEP /eqP TSKo]].
            eapply in_arrivals_implies_arrived_between in ARRIN; eauto 2.
            move: ARRIN => /andP [ARRIN _]; unfold V in ARRIN.
            edestruct (leqP (D tsk_o) (A + ε + D tsk)) as [NEQ2|NEQ2]. 
            - move: ARRIN; rewrite leqNgt; move => /negP ARRIN; apply: ARRIN.
              rewrite -(ltn_add2r (D tsk_o)).
              apply leq_ltn_trans with (job_arrival j + D tsk); first by move: (H_job_of_tsk) => /eqP <-; rewrite -TSKo.
              rewrite addnBA // addnA addnA subnKC // subnK.
              + by rewrite ltn_add2r addn1.
              + apply leq_trans with (A + ε + D tsk); first by done.
                  by rewrite !leq_add2r leq_subr. 
            - move: HEP; rewrite /EDF /edf.EDF leqNgt; move => /negP HEP; apply: HEP.                      
              apply leq_ltn_trans with (job_arrival jo + (A + D tsk)). 
              + rewrite addnBAC // addnBA.
                rewrite [in X in _ <= X]addnC -addnBA.
                * rewrite /job_deadline /job_deadline_from_task_deadline;
                    by move: (H_job_of_tsk) => /eqP ->; rewrite leq_addr.
                * by apply leq_trans with (t1 + (A + ε + D tsk - D tsk_o)); first rewrite leq_addr.
                    by apply leq_trans with (job_arrival j); [ | by rewrite leq_addr].
              + rewrite ltn_add2l.
                apply leq_ltn_trans with (A + ε + D tsk).
                * by rewrite leq_add2r leq_addr.
                * by rewrite TSKo.
          Qed.
          
          (** And similarly to the previous case, by definition of
              [rbf], the total workload of jobs with higher-or-equal
              priority from task [tsk_o] is bounded [rbf(tsk_o, Δ)].
              *)
          Lemma workload_le_rbf':
            workload_of_jobs (EDF_from tsk_o) (arrivals_between arr_seq t1 (t1 + (A + ε + D tsk - D tsk_o)))
            <= rbf tsk_o (A + ε + D tsk - D tsk_o).
          Proof.
            unfold workload_of_jobs, EDF_from.
            move: (H_busy_interval) => [[/andP [JINBI JINBI2] [QT _]] _].
            set (V := A + ε + D tsk - D tsk_o) in *.
            apply leq_trans with
                (task_cost tsk_o * number_of_task_arrivals arr_seq tsk_o t1 (t1 + (A + ε + D tsk - D tsk_o))).
            -  apply leq_trans with
                   (\sum_(jo <- arrivals_between arr_seq t1 (t1 + V) | job_task jo == tsk_o) job_cost jo).
               + rewrite big_mkcond [X in _ <= X]big_mkcond //=.
                 rewrite leq_sum //; intros s _.
                   by case (EDF s j).
               + rewrite /number_of_task_arrivals /task.arrivals.number_of_task_arrivals
                 -sum1_size big_distrr /= big_filter.
                 rewrite  muln1.
                 apply leq_sum_seq; move => j0 IN0 /eqP EQ.
                 rewrite -EQ.
                 apply H_valid_job_cost.
                   by apply in_arrivals_implies_arrived in IN0.
            - unfold V in *; clear V.
              set (V := A + ε + D tsk - D tsk_o) in *.
              rewrite leq_mul2l; apply/orP; right.
              rewrite -{2}[V](addKn t1).
                by apply H_is_arrival_curve; auto using leq_addr.
          Qed.
          
        End Case2.

        (** By combining case 1 and case 2 we prove that total
            workload of tasks is at most [bound_on_total_hep_workload(A, Δ)]. *)
        Corollary sum_of_workloads_is_at_most_bound_on_total_hep_workload :
          \sum_(tsk_o <- ts | tsk_o != tsk) workload_of_jobs (EDF_from tsk_o) jobs
          <= bound_on_total_hep_workload A Δ.
        Proof.
          move: (H_busy_interval) => [[/andP [JINBI JINBI2] [QT _]] _].
          apply leq_sum_seq; intros tsko INtsko NEQT.
          edestruct (leqP Δ (A + ε + D tsk - D tsko)) as [NEQ|NEQ]; [ | apply ltnW in NEQ].
          - by apply workload_le_rbf.
          - eapply leq_trans; first by eapply total_workload_shorten_range; eauto 2.
              by eapply workload_le_rbf'.
        Qed.
        
    End Inequalities.

    (** Recall that in module abstract_seq_RTA hypothesis
        task_interference_is_bounded_by expects to receive a function
        that maps some task t, the relative arrival time of a job j of
        task t, and the length of the interval to the maximum amount
        of interference.

        However, in this module we analyze only one task -- [tsk],
        therefore it is “hard-coded” inside the interference bound
        function [IBF_other]. Therefore, in order for the [IBF_other] signature to
        match the required signature in module abstract_seq_RTA, we
        wrap the [IBF_other] function in a function that accepts, but simply
        ignores the task. *)
      Corollary instantiated_task_interference_is_bounded:
        task_interference_is_bounded_by
          arr_seq sched tsk interference interfering_workload (fun tsk A R => IBF_other A R).
      Proof.
        unfold EDF in *.
        intros j R2 t1 t2 ARR TSK N NCOMPL BUSY.
        move: H_sched_valid => [CARR MBR].
        move: (posnP (@job_cost _ Cost j)) => [ZERO|POS].
        - exfalso; move: NCOMPL => /negP COMPL; apply: COMPL.
            by rewrite /completed_by /completed_by ZERO. 
        - move: (BUSY) => [[/andP [JINBI JINBI2] [QT _]] _]. 
          rewrite (cumulative_task_interference_split arr_seq sched _ _ _ tsk j);
            rt_eauto; last first.
          { by eapply arrived_between_implies_in_arrivals; eauto. }
          rewrite /I leq_add //.  
          + by apply cumulative_priority_inversion_is_bounded with t2.
          + eapply leq_trans. eapply cumulative_interference_is_bounded_by_total_service; eauto 2.
            eapply leq_trans. eapply total_service_is_bounded_by_total_workload; eauto 2.
            eapply leq_trans. eapply reorder_summation; eauto 2.
            eapply leq_trans. eapply sum_of_workloads_is_at_most_bound_on_total_hep_workload; eauto 2.
            by done. 
      Qed.

    End TaskInterferenceIsBoundedByIBF_other.
    
    (** Finally, we show that there exists a solution for the response-time recurrence. *)
    Section SolutionOfResponseTimeReccurenceExists.

      (** Consider any job j of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      Hypothesis H_job_cost_positive : job_cost_positive j.

      (** Given any job j of task [tsk] that arrives exactly A units after the beginning of 
         the busy interval, the bound of the total interference incurred by j within an 
         interval of length Δ is equal to [task_rbf (A + ε) - task_cost tsk + IBF_other(A, Δ)]. *)
      Let total_interference_bound tsk (A Δ : duration) :=
            task_rbf (A + ε) - task_cost tsk + IBF_other A Δ.

      (** Next, consider any A from the search space (in abstract sense). *)
      Variable A : duration.
      Hypothesis H_A_is_in_abstract_search_space:
        search_space.is_in_search_space tsk L total_interference_bound A.

      (** We prove that A is also in the concrete search space. *)
      Lemma A_is_in_concrete_search_space:
        is_in_search_space A.
      Proof.
        move: H_A_is_in_abstract_search_space  => [-> | [/andP [POSA LTL] [x [LTx INSP2]]]];
          apply/andP; split => //.
        { apply/orP; left; apply/orP; right.
          rewrite /task_rbf_changes_at /task_rbf /rbf task_rbf_0_zero //; eauto 2.
          apply contraT => /negPn /eqP ZERO.
          rewrite -(ltnn 0) {2}ZERO add0n.
          apply: (@leq_trans (task_cost tsk));
            last by apply: task_rbf_1_ge_task_cost; eauto.
          apply: (@leq_trans (job_cost j)) => //.
          move: (H_job_of_tsk) => /eqP <-.
          by apply: (H_valid_job_cost _ H_j_arrives). }
        { apply contraT; rewrite !negb_or => /andP [/andP [/negPn/eqP PI /negPn/eqP RBF]  WL].
          exfalso; apply INSP2.
          rewrite /total_interference_bound subnK // RBF.
          apply /eqP; rewrite eqn_add2l /IBF_other PI eqn_add2l.
          rewrite /bound_on_total_hep_workload subnK //.
          apply /eqP; rewrite big_seq_cond [RHS]big_seq_cond.
          apply eq_big => // tsk_i /andP [TS OTHER].
          move: WL; rewrite /bound_on_total_hep_workload_changes_at => /hasPn WL.
          move: {WL} (WL tsk_i TS) =>  /nandP [/negPn/eqP EQ|/negPn/eqP WL];
            first by move: OTHER; rewrite EQ => /neqP.
          case: (ltngtP (A + ε + D tsk - D tsk_i) x) => [ltn_x|gtn_x|eq_x];
            rewrite /minn.
          { by rewrite ifT //; lia. }
          { rewrite ifF //.
            by move: gtn_x; rewrite leq_eqVlt /ε => /orP [/eqP EQ|LEQ]; lia. }
          { case: (A + D tsk - D tsk_i < x).
            - by rewrite WL.
            - by rewrite eq_x. } }
      Qed.

      (** Then, there exists solution for response-time recurrence (in the abstract sense). *)
      Corollary correct_search_space:
        exists F,
          A + F >= task_rbf (A + ε) - (task_cost tsk - task_rtct tsk) + IBF_other A (A + F) /\
          R >= F + (task_cost tsk - task_rtct tsk).
      Proof.
        edestruct H_R_is_maximum as [F [FIX NEQ]].
        - by apply A_is_in_concrete_search_space.
        - exists F; split; last by done.
          rewrite -{2}(leqRW FIX).
          by rewrite addnA [_ + priority_inversion_bound A]addnC -!addnA.
      Qed.
         
      End SolutionOfResponseTimeReccurenceExists.       
    
  End FillingOutHypothesesOfAbstractRTATheorem.

  (** ** Final Theorem *)
  (** Based on the properties established above, we apply the abstract analysis 
     framework to infer that R is a response-time bound for [tsk]. *)
  Theorem uniprocessor_response_time_bound_edf:
    task_response_time_bound arr_seq sched tsk R.
  Proof.
    intros js ARRs TSKs.
    move: H_sched_valid => [CARR MBR].
    move: (posnP (@job_cost _ Cost js)) => [ZERO|POS].
    { by rewrite /job_response_time_bound /completed_by ZERO. }    
    ( try ( eapply uniprocessor_response_time_bound_seq with
        (interference0 := interference) (interfering_workload0 := interfering_workload)
        (task_interference_bound_function := fun tsk A R => IBF_other A R) (L0 := L) ) ||
    eapply uniprocessor_response_time_bound_seq with
        (interference := interference) (interfering_workload := interfering_workload)
        (task_interference_bound_function := fun tsk A R => IBF_other A R) (L := L)); rt_eauto.
    - by apply instantiated_i_and_w_are_coherent_with_schedule.
    - by apply instantiated_interference_and_workload_consistent_with_sequential_tasks.
    - by apply instantiated_busy_intervals_are_bounded.
    - by apply instantiated_task_interference_is_bounded.
    - by eapply correct_search_space; eauto 2.
  Qed.
  
End AbstractRTAforEDFwithArrivalCurves. 
