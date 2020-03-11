Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.analysis.definitions.request_bound_function.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.analysis.facts.busy_interval.priority_inversion.
Require Export prosa.results.fixed_priority.rta.bounded_pi.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.

(** Throughout this file, we assume the basic (i.e., Liu & Layland) readiness model. *)
Require Import prosa.model.readiness.basic.

(** * RTA for FP-schedulers with Bounded Non-Preemptive Segments *)

(** In this section we instantiate the Abstract RTA for FP-schedulers
    with Bounded Priority Inversion to FP-schedulers for ideal
    uni-processor model of real-time tasks with arbitrary
    arrival models _and_ bounded non-preemptive segments. *)

(** Recall that Abstract RTA for FP-schedulers with Bounded Priority
    Inversion does not specify the cause of priority inversion. In
    this section, we prove that the priority inversion caused by
    execution of non-preemptive segments is bounded. Thus the Abstract
    RTA for FP-schedulers is applicable to this instantiation. *)
Section RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}. 
  Context `{TaskMaxNonpreemptiveSegment Task}.
  
  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
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
    valid_model_with_bounded_nonpreemptive_segments arr_seq sched.

  (** Consider an FP policy that indicates a higher-or-equal priority
      relation, and assume that the relation is reflexive and
      transitive. *)
  Context `{FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.
  Hypothesis H_priority_is_transitive : transitive_priorities.
  
  (** Assume we have sequential tasks, i.e, jobs from the same task
      execute in the order of their arrival. *)
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
  
  (** Let's define some local names for clarity. *)
  Let max_length_of_priority_inversion :=
    max_length_of_priority_inversion arr_seq.
  Let task_rbf := task_request_bound_function tsk.
  Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.
  
  (** We also define a bound for the priority inversion caused by jobs with lower priority. *)
  Definition blocking_bound :=
    \max_(tsk_other <- ts | ~~ hep_task tsk_other tsk)
     (task_max_nonpreemptive_segment tsk_other - ε).
  
  (** ** Priority inversion is bounded *)
  (** In this section, we prove that a priority inversion for task [tsk] is bounded by 
      the maximum length of non-preemptive segments among the tasks with lower priority. *)
  Section PriorityInversionIsBounded.

    (** First, we prove that the maximum length of a priority inversion of a job j is 
       bounded by the maximum length of a non-preemptive section of a task with 
       lower-priority task (i.e., the blocking term). *)
    Lemma priority_inversion_is_bounded_by_blocking:
      forall j t, 
        arrives_in arr_seq j ->
        job_task j = tsk -> 
        max_length_of_priority_inversion j t <= blocking_bound.
    Proof.
      intros j t ARR TSK.
      rewrite /max_length_of_priority_inversion /blocking_bound /FP_to_JLFP
              /priority_inversion.max_length_of_priority_inversion.
      apply leq_trans with
          (\max_(j_lp <- arrivals_between arr_seq 0 t
                | ~~ hep_task (job_task j_lp) tsk)
            (task_max_nonpreemptive_segment (job_task j_lp) - ε)).
      { rewrite /hep_job TSK.
        apply leq_big_max.
        intros j' JINB NOTHEP.
        rewrite leq_sub2r //.
        apply H_valid_model_with_bounded_nonpreemptive_segments.
          by eapply in_arrivals_implies_arrived; eauto 2.
      }
      { apply /bigmax_leq_seqP. 
        intros j' JINB NOTHEP.
        apply leq_bigmax_cond_seq with
            (i0 := (job_task j')) (F := fun tsk => task_max_nonpreemptive_segment tsk - 1); last by done.
        apply H_all_jobs_from_taskset.
        apply mem_bigcat_nat_exists in JINB.
          by inversion JINB as [ta' [JIN' _]]; exists ta'.
      }
    Qed.
    
    (** Using the above lemma, we prove that the priority inversion of the task is bounded by blocking_bound. *) 
    Lemma priority_inversion_is_bounded:
      priority_inversion_is_bounded_by
        arr_seq sched tsk blocking_bound.
    Proof.
      intros j ARR TSK POS t1 t2 PREF.
      case NEQ: (t2 - t1 <= blocking_bound). 
      { apply leq_trans with (t2 - t1); last by done.
        rewrite /cumulative_priority_inversion /is_priority_inversion.
        rewrite -[X in _ <= X]addn0 -[t2 - t1]mul1n -iter_addn -big_const_nat leq_sum //. 
        intros t _; case: (sched t); last by done.
          by intros s; case: (hep_job s j). 
      } 
      move: NEQ => /negP /negP; rewrite -ltnNge; move => BOUND.
      edestruct (@preemption_time_exists) as [ppt [PPT NEQ]]; eauto 2; move: NEQ => /andP [GE LE].
      apply leq_trans with (cumulative_priority_inversion sched j t1 ppt);
        last apply leq_trans with (ppt - t1); first last.
      - rewrite leq_subLR.
        apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
          by rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2.
      - rewrite /cumulative_priority_inversion /is_priority_inversion.
        rewrite -[X in _ <= X]addn0 -[ppt - t1]mul1n -iter_addn -big_const_nat. 
        rewrite leq_sum //; intros t _; case: (sched t); last by done.
          by intros s; case: (hep_job s j).
      - rewrite /cumulative_priority_inversion /is_priority_inversion. 
        rewrite (@big_cat_nat _ _ _ ppt) //=; last first.
        { rewrite ltn_subRL in BOUND.
          apply leq_trans with (t1 + blocking_bound); last by apply ltnW. 
          apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
          rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2.
        }
        rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
        rewrite big_nat_cond big1 //; move => t /andP [/andP [GEt LTt] _ ].
        case SCHED: (sched t) => [s | ]; last by done.
        edestruct (@not_quiet_implies_exists_scheduled_hp_job)
          with (K := ppt - t1) (t1 := t1) (t2 := t2) (t := t) as [j_hp [ARRB [HP SCHEDHP]]]; eauto 2.
        { by exists ppt; split; [done | rewrite subnKC //; apply/andP]. } 
        { by rewrite subnKC //; apply/andP; split. }
        apply/eqP; rewrite eqb0 Bool.negb_involutive.
        enough (EQef : s = j_hp); first by subst;auto.
        eapply ideal_proc_model_is_a_uniprocessor_model; eauto 2.
          by rewrite scheduled_at_def SCHED.
    Qed.
    
  End PriorityInversionIsBounded. 

  (** ** Response-Time Bound *)
  (** In this section, we prove that the maximum among the solutions of the response-time 
      bound recurrence is a response-time bound for [tsk]. *)
  Section ResponseTimeBound.

    (** Let L be any positive fixed point of the busy interval recurrence. *)
    Variable L : duration.
    Hypothesis H_L_positive : L > 0.
    Hypothesis H_fixed_point : L = blocking_bound + total_hep_rbf L.

    (** To reduce the time complexity of the analysis, recall the notion of search space. *)
    Let is_in_search_space := is_in_search_space tsk L.
    
    (** Next, consider any value R, and assume that for any given arrival offset A from the search 
       space there is a solution of the response-time bound recurrence that is bounded by R. *)
    Variable R : duration.
    Hypothesis H_R_is_maximum:
      forall (A : duration), 
        is_in_search_space A -> 
        exists (F : duration),
          A + F = blocking_bound
                  + (task_rbf (A + ε) - (task_cost tsk - task_run_to_completion_threshold tsk))
                  + total_ohep_rbf (A + F) /\
          F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.

    (** Then, using the results for the general RTA for FP-schedulers, we establish a 
       response-time bound for the more concrete model of bounded nonpreemptive segments. 
       Note that in case of the general RTA for FP-schedulers, we just _assume_ that 
       the priority inversion is bounded. In this module we provide the preemption model
       with bounded nonpreemptive segments and _prove_ that the priority inversion is 
       bounded. *)
    Theorem uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments:
      response_time_bounded_by tsk R.
    Proof.
      eapply uniprocessor_response_time_bound_fp;
        eauto using priority_inversion_is_bounded. 
    Qed.
    
  End ResponseTimeBound.
  
End RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.
