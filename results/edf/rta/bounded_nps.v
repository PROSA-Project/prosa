Require Import prosa.model.priority.edf.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.results.edf.rta.bounded_pi.
Require Export prosa.analysis.facts.busy_interval.priority_inversion.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.readiness.basic.

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
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

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
  
  (** Next, consider any ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** In addition, we assume the existence of a function mapping jobs
      to theirs preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ... and assume that it defines a valid preemption
     model with bounded non-preemptive segments. *)
  Hypothesis H_valid_model_with_bounded_nonpreemptive_segments:
    valid_model_with_bounded_nonpreemptive_segments
      arr_seq sched.
  
  (** Assume we have sequential tasks, i.e, jobs from the 
     same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks sched.
  
  (** Next, we assume that the schedule is a work-conserving schedule... *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... and the schedule respects the policy defined by the [job_preemptable]
     function (i.e., jobs have bounded non-preemptive segments). *)
  Hypothesis H_respects_policy : respects_policy_at_preemption_point arr_seq sched.

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

  (** ...and a valid task run-to-completion threshold function. That is, 
     [task_run_to_completion_threshold tsk] is (1) no bigger than [tsk]'s 
     cost, (2) for any job of task [tsk] job_run_to_completion_threshold 
     is bounded by task_run_to_completion_threshold. *)
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
  Let task_rbf_changes_at A := task_rbf_changes_at tsk A.
  Let bound_on_total_hep_workload_changes_at :=
    bound_on_total_hep_workload_changes_at ts tsk.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.
  Let is_in_search_space := is_in_search_space ts tsk.
                         
  (** We also define a bound for the priority inversion caused by jobs with lower priority. *)
  Definition blocking_bound :=
    \max_(tsk_o <- ts | (tsk_o != tsk) && (D tsk < D tsk_o))
     (task_max_nonpreemptive_segment tsk_o - ε).
  
  (** ** Priority inversion is bounded *)
  (** In this section, we prove that a priority inversion for task [tsk] is bounded by 
      the maximum length of non-preemptive segments among the tasks with lower priority. *)
  Section PriorityInversionIsBounded.

    (** First, we prove that the maximum length of a priority
        inversion of job j is bounded by the maximum length of a
        non-preemptive section of a task with lower-priority task
        (i.e., the blocking term). *)
    Lemma priority_inversion_is_bounded_by_blocking:
      forall j t,
        arrives_in arr_seq j ->
        job_task j = tsk ->
        t <= job_arrival j ->
        max_length_of_priority_inversion j t <= blocking_bound.
    Proof.
      intros j t ARR TSK LE; unfold max_length_of_priority_inversion, blocking_bound. 
      apply leq_trans with
          (\max_(j_lp <- arrivals_between arr_seq 0 t | ~~ EDF j_lp j)
            (task_max_nonpreemptive_segment (job_task j_lp) - ε)).
      - apply leq_big_max.
        intros j' JINB NOTHEP.        
        rewrite leq_sub2r //.
        apply in_arrivals_implies_arrived in JINB.
          by apply H_valid_model_with_bounded_nonpreemptive_segments. 
      - apply /bigmax_leq_seqP. 
        intros j' JINB NOTHEP.
        apply leq_bigmax_cond_seq with (i0 := (job_task j')) (F := fun tsk => task_max_nonpreemptive_segment tsk - 1). 
        { apply H_all_jobs_from_taskset.
          apply mem_bigcat_nat_exists in JINB.
            by inversion JINB as [ta' [JIN' _]]; exists ta'. }
        { have NINTSK: job_task j' != tsk.
          { apply/eqP; intros TSKj'.
            rewrite /EDF -ltnNge in NOTHEP.
            rewrite /job_deadline /absolute_deadline.job_deadline_from_task_deadline in NOTHEP.
            rewrite TSKj' TSK ltn_add2r in NOTHEP.
            move: NOTHEP; rewrite ltnNge; move => /negP T; apply: T.
            apply leq_trans with t; last by done.
            eapply in_arrivals_implies_arrived_between in JINB; last by eauto 2.
            move: JINB; move => /andP [_ T].
              by apply ltnW.
          }
          apply/andP; split; first by done.
          rewrite /EDF -ltnNge in NOTHEP.
          rewrite -TSK.
          have ARRLE: job_arrival j' < job_arrival j.
          { apply leq_trans with t; last by done.
            eapply in_arrivals_implies_arrived_between in JINB; last by eauto 2.
              by move: JINB; move => /andP [_ T].
          }
          rewrite /job_deadline /absolute_deadline.job_deadline_from_task_deadline in NOTHEP.
          rewrite /D; ssromega.
        }
    Qed.
    
    (** Using the lemma above, we prove that the priority inversion of the task is bounded by 
       the maximum length of a nonpreemptive section of lower-priority tasks. *)
    Lemma priority_inversion_is_bounded:
      priority_inversion_is_bounded_by arr_seq sched tsk blocking_bound.
    Proof.
      move => j ARR TSK POS t1 t2 PREF; move: (PREF) => [_ [_ [_ /andP [T _]]]].
      destruct (leqP (t2 - t1) blocking_bound) as [NEQ|NEQ].
      { apply leq_trans with (t2 - t1); last by done. 
        rewrite /cumulative_priority_inversion /is_priority_inversion. 
        rewrite -[X in _ <= X]addn0 -[t2 - t1]mul1n -iter_addn -big_const_nat. 
        rewrite leq_sum //.
        intros t _; case: (sched t); last by done.
          by intros s; destruct (hep_job s j).
      }
      edestruct @preemption_time_exists as [ppt [PPT NEQ2]]; eauto 2 with basic_facts.
      move: NEQ2 => /andP [GE LE].
      apply leq_trans with (cumulative_priority_inversion sched j t1 ppt);
        last apply leq_trans with (ppt - t1).
      - rewrite /cumulative_priority_inversion /is_priority_inversion. 
        rewrite (@big_cat_nat _ _ _ ppt) //=; last first.
        { rewrite ltn_subRL in NEQ.
          apply leq_trans with (t1 + blocking_bound); last by apply ltnW. 
          apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
            by rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2. }
        rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
        rewrite big_nat_cond big1 //; move => t /andP [/andP [GEt LTt] _ ].
        case SCHED: (sched t) => [s | ]; last by done. 
        edestruct @not_quiet_implies_exists_scheduled_hp_job
          with (K := ppt - t1) (t := t) as [j_hp [ARRB [HP SCHEDHP]]]; eauto 2 with basic_facts.
        { exists ppt; split.  by done.  by rewrite subnKC //; apply/andP; split. } 
        { by rewrite subnKC //; apply/andP; split. }
        apply/eqP; rewrite eqb0 Bool.negb_involutive.
        enough (EQ : s = j_hp); first by subst.
        move: SCHED => /eqP SCHED; rewrite -scheduled_at_def in SCHED.
          by eapply ideal_proc_model_is_a_uniprocessor_model; [exact SCHED | exact SCHEDHP].
      - rewrite /cumulative_priority_inversion /is_priority_inversion. 
        rewrite -[X in _ <= X]addn0 -[ppt - t1]mul1n -iter_addn -big_const_nat. 
        rewrite leq_sum //.
        intros t _; case: (sched t); last by done.
          by intros s; destruct (hep_job s j).
      -  rewrite leq_subLR.
         apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
           by rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2.
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
          A + F = blocking_bound
                  + (task_rbf (A + ε) - (task_cost tsk - task_run_to_completion_threshold tsk))
                  + bound_on_total_hep_workload  A (A + F) /\
          F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.

    (** Then, using the results for the general RTA for EDF-schedulers, we establish a 
         response-time bound for the more concrete model of bounded nonpreemptive segments.
         Note that in case of the general RTA for EDF-schedulers, we just _assume_ that 
         the priority inversion is bounded. In this module we provide the preemption model
         with bounded nonpreemptive segments and _prove_ that the priority inversion is 
         bounded. *)
    Theorem uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments:
      response_time_bounded_by tsk R.
    Proof.
      eapply uniprocessor_response_time_bound_edf; eauto 2.
        by apply priority_inversion_is_bounded. 
    Qed.
           
  End ResponseTimeBound.

End RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.
