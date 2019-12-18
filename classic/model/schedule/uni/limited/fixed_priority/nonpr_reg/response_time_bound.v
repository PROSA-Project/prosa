Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.curves.bounds
               prosa.classic.analysis.uni.arrival_curves.workload_bound.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.limited.platform.definitions
               prosa.classic.model.schedule.uni.limited.platform.priority_inversion_is_bounded
               prosa.classic.model.schedule.uni.limited.schedule
               prosa.classic.model.schedule.uni.limited.busy_interval
               prosa.classic.model.schedule.uni.limited.fixed_priority.response_time_bound
               prosa.classic.model.schedule.uni.limited.rbf.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * RTA for FP-schedulers with bounded nonpreemptive segments *)
(** In this module we prove a general RTA theorem for FP-schedulers *)
Module RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.

  Import Job ArrivalCurves TaskArrival Priority  UniprocessorSchedule Workload Service
         ResponseTime MaxArrivalsWorkloadBound LimitedPreemptionPlatform RBF
         AbstractRTAforFPwithArrivalCurves BusyIntervalJLFP PriorityInversionIsBounded. 

  Section Analysis.

    Context {Task: eqType}.
    Variable task_max_nps task_cost: Task -> time.    
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_max_nps job_cost: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any arrival sequence with consistent, non-duplicate arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.
 
    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched. 

    (* Assume we have sequential jobs, i.e, jobs from the same 
       task execute in the order of their arrival. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.

    (* Assume that a job cost cannot be larger than a task cost. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq.
    
    (* Consider an FP policy that indicates a higher-or-equal priority relation,
       and assume that the relation is reflexive and transitive. *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.

    (* We consider an arbitrary function can_be_preempted which defines 
       a preemption model with bounded nonpreemptive segments. *)
    Variable can_be_preempted: Job -> time -> bool.
    Let preemption_time := preemption_time sched can_be_preempted.
    Hypothesis H_correct_preemption_model:
      correct_preemption_model arr_seq sched can_be_preempted.
    Hypothesis H_model_with_bounded_nonpreemptive_segments:
      model_with_bounded_nonpreemptive_segments
        job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps. 

    (* Next, we assume that the schedule is a work-conserving schedule... *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

    (* ... and the schedule respects the policy defined by the 
       can_be_preempted function (i.e., bounded nonpreemptive segments). *)
    Hypothesis H_respects_policy:
      respects_FP_policy_at_preemption_point
        job_arrival job_cost job_task arr_seq sched can_be_preempted higher_eq_priority.

    (* Consider an arbitrary task set ts... *)    
    Variable ts: list Task.

    (* ..and assume that all jobs come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Let max_arrivals be a family of proper arrival curves, i.e., for any task tsk in ts 
       [max_arrival tsk] is (1) an arrival bound of tsk, and (2) it is a monotonic function 
       that equals 0 for the empty interval delta = 0. *)
    Variable max_arrivals: Task -> time -> nat.
    Hypothesis H_family_of_proper_arrival_curves:
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts.

    (* Consider a proper job lock-in service and task lock-in functions, i.e... *)
    Variable job_lock_in_service: Job -> time.
    Variable task_lock_in_service: Task -> time.

    (* ...we assume that for all jobs in the arrival sequence the lock-in service is 
       (1) positive, (2) no bigger than costs of the corresponding jobs, and (3) a job
       becomes nonpreemptive after it reaches its lock-in service... *)
    Hypothesis H_proper_job_lock_in_service:
      proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service.

    (* ...and that [task_lock_in_service tsk] is (1) no bigger than tsk's cost, (2) for any
       job of task tsk job_lock_in_service is bounded by task_lock_in_service. *)
    Hypothesis H_proper_task_lock_in_service:
      proper_task_lock_in_service
        task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk.

    (* We also lift the FP priority relation to a corresponding JLFP priority relation. *)
    Let jlfp_higher_eq_priority := FP_to_JLFP job_task higher_eq_priority.
    
    (* Let's define some local names for clarity. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_backlogged_at := backlogged job_arrival job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    Let max_length_of_priority_inversion :=
      max_length_of_priority_inversion job_max_nps arr_seq jlfp_higher_eq_priority.
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.
    Let total_hep_rbf :=
      total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.
    Let total_ohep_rbf :=
      total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.

    (* We also define a bound for the priority inversion caused by jobs with lower priority. *)
    Definition blocking_bound :=
      \max_(tsk_other <- ts | ~~ higher_eq_priority tsk_other tsk)
       (task_max_nps tsk_other - ε).
    
    (** ** Priority inversion is bounded *)
    (** In this section, we prove that a priority inversion for task tsk is bounded by 
       the maximum length of nonpreemtive segments among the tasks with lower priority. *)
    Section PriorityInversionIsBounded.

      (* First, we prove that the maximum length of a priority inversion of a job j is 
         bounded by the maximum length of a nonpreemptive section of a task with 
         lower-priority task (i.e., the blocking term). *)
      Lemma priority_inversion_is_bounded_by_blocking:
        forall j t, 
          arrives_in arr_seq j ->
          job_task j = tsk -> 
          max_length_of_priority_inversion j t <= blocking_bound.
      Proof.
        intros j t ARR TSK.
        rewrite /max_length_of_priority_inversion
                /PriorityInversionIsBounded.max_length_of_priority_inversion
                /blocking_bound /jlfp_higher_eq_priority /FP_to_JLFP.
        apply leq_trans with
            (\max_(j_lp <- jobs_arrived_between arr_seq 0 t
                  | ~~ higher_eq_priority (job_task j_lp) tsk)
              (task_max_nps (job_task j_lp) - ε)
            ).
        { rewrite TSK.
          apply leq_big_max.
          intros j' JINB NOTHEP. 
          specialize (H_job_cost_le_task_cost j').
          feed H_job_cost_le_task_cost.
          { apply mem_bigcat_nat_exists in JINB.
              by move: JINB => [ta' [JIN' _]]; exists ta'.
          }
          rewrite leq_sub2r //.
          apply in_arrivals_implies_arrived in JINB.
          move: (H_model_with_bounded_nonpreemptive_segments j' JINB) => [_ [_ [T _]]].
            by apply T.
        }
        { apply /bigmax_leq_seqP. 
          intros j' JINB NOTHEP.
          apply leq_bigmax_cond_seq with
              (i0 := (job_task j')) (F := fun tsk => task_max_nps tsk - 1); last by done.
          apply H_all_jobs_from_taskset.
          apply mem_bigcat_nat_exists in JINB.
            by inversion JINB as [ta' [JIN' _]]; exists ta'.
        }
      Qed.
      
      (* Using the above lemma, we prove that the priority inversion of the task is bounded by blocking_bound. *) 
      Lemma priority_inversion_is_bounded:
        priority_inversion_is_bounded_by
          job_arrival job_cost job_task arr_seq sched jlfp_higher_eq_priority tsk blocking_bound.
      Proof. 
        intros j ARR TSK POS t1 t2 PREF.
        case NEQ: (t2 - t1 <= blocking_bound). 
        { apply leq_trans with (t2 - t1); last by done.
          rewrite /cumulative_priority_inversion /BusyIntervalJLFP.is_priority_inversion.
          rewrite -[X in _ <= X]addn0 -[t2 - t1]mul1n -iter_addn -big_const_nat. 
          rewrite leq_sum //.
          intros t _; case: (sched t); last by done.
            by intros s; case: jlfp_higher_eq_priority.
        }
        move: NEQ => /negP /negP; rewrite -ltnNge; move => NEQ.
        have PPE := preemption_time_exists
                      task_max_nps job_arrival job_max_nps job_cost job_task arr_seq _ sched
                      _ _ _ jlfp_higher_eq_priority _ _ can_be_preempted
                      _ _ _ _ j ARR _ t1 t2 PREF .
        feed_n 11 PPE; try done.
        { unfold JLFP_is_reflexive, jlfp_higher_eq_priority, FP_to_JLFP. by done. }
        { unfold JLFP_is_transitive, jlfp_higher_eq_priority, FP_to_JLFP, transitive. eauto 2. }
        move: PPE => [ppt [PPT /andP [GE LE]]].
        apply leq_trans with (cumulative_priority_inversion sched jlfp_higher_eq_priority j t1 ppt);
          last apply leq_trans with (ppt - t1).
        - rewrite /cumulative_priority_inversion /BusyIntervalJLFP.is_priority_inversion.
          rewrite (@big_cat_nat _ _ _ ppt) //=.
          rewrite -[X in _ <= X]addn0 leq_add2l.
          rewrite leqn0.
          rewrite big_nat_cond big1 //; move => t /andP [/andP [GEt LTt] _ ].
          case SCHED: (sched t) => [s | ]; last by done.
          have SCHEDHP := not_quiet_implies_exists_scheduled_hp_job
                            task_max_nps job_arrival job_max_nps job_cost job_task arr_seq _ sched
                            _ _ _ jlfp_higher_eq_priority _ _ can_be_preempted
                            _ _ _ _ j ARR _ t1 t2 _ (ppt - t1) _ t.
          feed_n 14 SCHEDHP; try done.
          { unfold JLFP_is_reflexive, jlfp_higher_eq_priority, FP_to_JLFP. by done. }
          { unfold JLFP_is_transitive, jlfp_higher_eq_priority, FP_to_JLFP, transitive. eauto 2. }          
          { exists ppt; split.  by done.  by rewrite subnKC //; apply/andP; split. } 
          { by rewrite subnKC //; apply/andP; split. }
          move: SCHEDHP => [j_hp [ARRB [HP SCHEDHP]]].
          apply/eqP; rewrite eqb0 Bool.negb_involutive.
          have EQ: s = j_hp.
          { by apply only_one_job_scheduled with (sched0 := sched) (t0 := t); [apply/eqP | ]. }
            by rewrite EQ.
          rewrite ltn_subRL in NEQ.
          apply leq_trans with (t1 + blocking_bound); last by apply ltnW. 
          apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
          rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2.
        - rewrite /cumulative_priority_inversion /BusyIntervalJLFP.is_priority_inversion.
          rewrite -[X in _ <= X]addn0 -[ppt - t1]mul1n -iter_addn -big_const_nat. 
          rewrite leq_sum //.
          intros t _; case: (sched t); last by done.
            by intros s; case: jlfp_higher_eq_priority.
        - rewrite leq_subLR.
          apply leq_trans with (t1 + max_length_of_priority_inversion j t1); first by done.
          rewrite leq_add2l; eapply priority_inversion_is_bounded_by_blocking; eauto 2.
      Qed.
      
    End PriorityInversionIsBounded. 

    (** ** Response-Time Bound *)
    (** In this section, we prove that the maximum among the solutions of the response-time 
       bound recurrence is a response-time bound for tsk. *)
    Section ResponseTimeBound.

      (* Let L be any positive fixed point of the busy interval recurrence. *)
      Variable L: time.
      Hypothesis H_L_positive: L > 0.
      Hypothesis H_fixed_point: L = blocking_bound + total_hep_rbf L.

      (* To reduce the time complexity of the analysis, recall the notion of search space. *)
      Let is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).
      
      (* Next, consider any value R, and assume that for any given arrival offset A from the search 
         space there is a solution of the response-time bound recurrence that is bounded by R. *)
      Variable R: nat.
      Hypothesis H_R_is_maximum:
        forall A, 
          is_in_search_space A -> 
          exists  F,
            A + F = blocking_bound
                    + (task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk))
                    + total_ohep_rbf (A + F) /\
            F + (task_cost tsk - task_lock_in_service tsk) <= R.

      (* Then, using the results for the general RTA for FP-schedulers, we establish a 
         response-time bound for the more concrete model of bounded nonpreemptive segments. 
         Note that in case of the general RTA for FP-schedulers, we just _assume_ that 
         the priority inversion is bounded. In this module we provide the preemption model
         with bounded nonpreemptive segments and _prove_ that the priority inversion is 
         bounded. *)
      Theorem uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments:
        response_time_bounded_by tsk R.
      Proof.
        eapply uniprocessor_response_time_bound_fp; eauto 2.
          by apply priority_inversion_is_bounded. 
      Qed.
       
    End ResponseTimeBound.
      
  End Analysis. 
   
End RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.