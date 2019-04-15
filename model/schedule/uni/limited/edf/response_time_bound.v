Require Import rt.util.all.
Require Import rt.model.arrival.basic.job
               rt.model.arrival.basic.task_arrival
               rt.model.priority.
Require Import rt.model.schedule.uni.service
               rt.model.schedule.uni.workload
               rt.model.schedule.uni.schedule
               rt.model.schedule.uni.response_time
               rt.model.schedule.uni.schedule_of_task.
Require Import rt.model.schedule.uni.limited.platform.definitions
               rt.model.schedule.uni.limited.schedule
               rt.model.schedule.uni.limited.busy_interval
               rt.model.schedule.uni.limited.rbf
               rt.model.schedule.uni.limited.abstract_RTA.definitions
               rt.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space
               rt.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.
Require Import rt.model.arrival.curves.bounds. 
Require Import rt.analysis.uni.arrival_curves.workload_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Abstract RTA for EDF-schedulers *)
(** In this module we propose the abstract response-time analysis (RTA) for 
    EDF uniprocessor scheduling of real-time tasks with arbitrary arrival models.  *)
Module AbstractRTAforEDFwithArrivalCurves.
  
  Import Job Epsilon ArrivalCurves TaskArrival ScheduleOfTask Priority
         UniprocessorSchedule Workload Service ResponseTime MaxArrivalsWorkloadBound
         BusyIntervalJLFP LimitedPreemptionPlatform RBF Service.
 
  Section AbstractResponseTimeAnalysisForEDF.
     
    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_deadline: Task -> time.
    
    Context {Job: eqType}. 
    Variable job_arrival: Job -> time. 
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* For clarity, let's denote the relative deadline of a task as D. *)
    Let D tsk := task_deadline tsk.
    
    (* The deadline of a job is equal to the deadline of the corresponding task. *)
    Let job_deadline j := D (job_task j).

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

    (* Next, assume that the schedule is a work-conserving schedule. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

    (* Assume we have sequential jobs, i.e, jobs from the 
       same task execute in the order of their arrival. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.

    (* Assume that a job cost cannot be larger than a task cost. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq.

    (* Consider an arbitrary task set ts. *)
    Variable ts: list Task.

    (* Next, we assume that all jobs come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

   (* Let max_arrivals be a family of proper arrival curves, i.e., for any task tsk in ts 
      [max_arrival tsk] is (1) an arrival bound of tsk, and (2) it is a monotonic function 
      that equals 0 for the empty interval delta = 0. *)
    Variable max_arrivals: Task -> time -> nat.
    Hypothesis H_family_of_proper_arrival_curves:
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts.

    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Consider proper job lock-in service and task lock-in functions, i.e... *)
    Variable job_lock_in_service: Job -> time.
    Variable task_lock_in_service: Task -> time.

    (* ...we assume that for all jobs with positive cost in the arrival sequence the 
       lock-in service is (1) positive, (2) no bigger than costs of the corresponding
       jobs, and (3) a job becomes nonpreemptive after it reaches its lock-in service... *)
    Hypothesis H_proper_job_lock_in_service:
      proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service.

    (* ...and that [task_lock_in_service tsk] is (1) no bigger than tsk's cost, (2) for any
       job of task tsk job_lock_in_service is bounded by task_lock_in_service. *)
    Hypothesis H_proper_task_lock_in_service:
      proper_task_lock_in_service
        task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk.

    (* Consider the EDF policy that indicates a higher-or-equal priority relation.
       Note that we do not relate the EDF policy with the scheduler. However, we 
       define functions for Interference and Interfering Workload that actively use
       the concept of priorities. *)
    Let higher_eq_priority: JLFP_policy Job := EDF job_arrival job_deadline.

    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_backlogged_at := backlogged job_arrival job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    Let task_scheduled_at :=  task_scheduled_at job_task sched.
    Let quiet_time := quiet_time job_arrival job_cost arr_seq sched higher_eq_priority.
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    Let cumulative_task_interference :=
      AbstractSeqRTA.cumul_task_interference job_task arr_seq sched.

    (* We introduce "rbf" as an abbreviation of the task request bound function,
       which is defined as [task_cost(T) × max_arrivals(T,Δ)] for some task T. *)
    Let rbf := task_request_bound_function task_cost max_arrivals.
    
    (* Next, we introduce task_rbf as an abbreviation of the task request bound function of task tsk. *)
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.

    (* Using the sum of individual request bound functions, we define the request bound 
       function of all tasks (total request bound function). *)
    Let total_rbf := total_request_bound_function task_cost max_arrivals ts.

    (* For proper calculation of interference and interfering workload of a job, we need to distinguish 
       interference received from other jobs of the same task and other jobs of other tasks. In that 
       regard, we introduce two additional relations. The first relation defines whether job j1 has a
       higher-than-or-equal-priority than job j2 and j1 is not equal to j2... *)
    Let another_job_with_higher_eq_priority: JLFP_policy Job :=
      fun j1 j2 => higher_eq_priority j1 j2 && (j1 != j2).

    (* ...and the second relation defines whether a job j1 has a higher-or-equal-priority than 
       job j2 and the task of j1 is not equal to task of j2. *)
    Let job_from_another_task_with_higher_eq_priority: JLFP_policy Job :=
      fun j1 j2 => higher_eq_priority j1 j2 && (job_task j1 != job_task j2).

    (* Assume that there eixsts a constant priority_inversion_bound that bounds 
       the length of any priority inversion experienced by any job of tsk. 
       Sinse we analyze only task tsk, we ignore the lengths of priority 
       inversions incurred by any other tasks. *)
     Variable priority_inversion_bound: time.
    Hypothesis H_priority_inversion_is_bounded:
      priority_inversion_is_bounded_by
        job_arrival job_cost job_task arr_seq sched higher_eq_priority tsk priority_inversion_bound.

    (* Let L be any positive fixed point of the busy interval recurrence. *)
    Variable L: time.
    Hypothesis H_L_positive: L > 0.
    Hypothesis H_fixed_point: L = priority_inversion_bound + total_rbf L.

    (* Next, we define an upper bound on interfering workload received from jobs
       with higher-than-or-equal priority. Note that this term looks the same as 
       the conventional expression of RTA for EDF. *)
    Let W A Δ :=
      \sum_(tsk_o <- ts | tsk_o != tsk)
       rbf tsk_o (minn ((A + ε) + D tsk - D tsk_o) Δ).

    (* To reduce the time complexity of the analysis, recall the notion of search space.
       Intuitively, this corresponds to all "interesting" arrival offsets that the job under
       analysis might have with regard to the beginning of its busy-window. Note that we use
       a slightly uncommon notation [has (λ tsko ⇒ P tsko) ts] which can be interpreted as 
       follows: task-set ts contains a task tsko such that a predicate P holds for tsko. 
       In case of search space for EDF we ask whether [task_rbf A ≠ task_rbf (A + ε)] or there
       exists a task tsko from ts such that [tsko ≠ tsk] and [rbf(tsko, A + D tsk - D tsko) ≠
       rbf(tsko, A + ε + D tsk - D tsko)]. I.e. [IBF(A - ε, x) ≠ IBF(A, ε)]. *)
    Let is_in_search_space A :=
      (A < L)
        && ((task_rbf A != task_rbf (A + ε))
            || has (fun tsko =>
                     (tsk != tsko)
                       && (rbf tsko (A +     D tsk - D tsko    )
                               != rbf tsko ((A + ε) + D tsk - D tsko))) ts).
    
    (* Let R be a value that upper-bounds the solution of each response-time recurrence, 
       i.e., for any relative arrival time A in the search space, there exists a corresponding 
       solution F such that [F + (task cost - task lock-in service) <= R]. *)
    Variable R: nat.
    Hypothesis H_R_is_maximum: 
      forall A,
        is_in_search_space A -> 
        exists F,
          A + F = priority_inversion_bound
                  + (task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk))
                  + W A (A + F) /\
          F + (task_cost tsk - task_lock_in_service tsk) <= R.

    (** ** Interference and Interfering Workload *)
    (** In this section, we introduce definitions of interference, 
        interfering workload and a function that bounds cumulative interference. *)

    (* In order to introduce the interference, first we need to recall the definition 
       of priority inversion introduced in module limited.fixed_priority.busy_interval: 
         [ Definition is_priority_inversion t := ]
         [   if sched t is Some jlp then         ]
         [     ~~ jlfp_higher_eq_priority jlp j  ]
         [   else false.                         ]
       I.e., we say that job j is incurring a priority inversion at time t
       if there exists a job with lower priority that executes at time t. 
       In order to simplify things, we ignore the fact that according to this 
       definition a job can incur priority inversion even before its release 
       (or after completion). All such (potentially bad) cases do not cause
       problems, as each job is analyzed only within the corresponding busy
       interval where the priority inversion behaves in the expected way. *)
    Let is_priority_inversion (j: Job) (t: time) :=
      is_priority_inversion sched higher_eq_priority j t.

    (* Next, we say that job j is incurring interference from another job with higher or equal 
       priority at time t, if there exists job jhp (different from j) with a higher or equal priority 
       that executes at time t. *)
    Definition is_interference_from_another_job_with_higher_eq_priority (j: Job) (t: time) :=
      if sched t is Some jhp then
        another_job_with_higher_eq_priority jhp j
      else false.
    
    (* Similarly, we say that job j is incurring interference from a job with higher or 
       equal priority of another task at time t, if there exists a job jhp (of a different task) 
       with higher or equal priority that executes at time t. *)
    Definition is_interference_from_another_task_with_higher_eq_priority (j: Job) (t: time) :=
      if sched t is Some jhp then
        job_from_another_task_with_higher_eq_priority jhp j
      else false.

    (* Now, we define the notion of cumulative interference, called 
       interfering_workload_of_jobs_with_hep_priority, that says 
       how many units of workload are generated by jobs with higher
       or equal priority released at time t. *)
    Definition interfering_workload_of_jobs_with_hep_priority (j: Job) (t: time) :=
      \sum_(jhp <- jobs_arriving_at arr_seq t |
            another_job_with_higher_eq_priority jhp j) job_cost jhp.

    (* To use the theorem uniprocessor_response_time_bound_seq from the Abstract RTA module, 
       we need to specify functions of interference and interfering workload.  *)

    (* Instantiation of Interference *)
    (* We say that job j incurs interference at time t iff it cannot execute due to 
       a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. *)
    Let interference j t :=
      is_priority_inversion j t || is_interference_from_another_job_with_higher_eq_priority j t.

    (* Instantiation of Interfering Workload *)
    (* The interfering workload, in turn, is defined as the sum of the priority inversion 
       function and interfering workload of jobs with higher or equal priority. *)
    Let interfering_workload j t :=
      is_priority_inversion j t + interfering_workload_of_jobs_with_hep_priority j t.

    (* Finally, we define the interference bound function as the sum of the priority 
       interference bound and the higher-or-equal-priority workload. *)
    Let IBF A R := priority_inversion_bound + W A R.
    
    (* For each of the concepts defined above, we introduce a corresponding cumulative function: *)
    (* (a) cumulative priority inversion... *)
    Let cumulative_priority_inversion j t1 t2 :=
      \sum_(t1 <= t < t2) is_priority_inversion j t.

    (* ... (b) cumulative interference from other jobs with higher or equal priority... *)
    Let cumulative_interference_from_other_jobs j t1 t2 :=
      \sum_(t1 <= t < t2) is_interference_from_another_job_with_higher_eq_priority j t.

    (* ... (c) and cumulative interference from jobs with higher or equal priority from other tasks... *)
    Let cumulative_interference_from_other_tasks j t1 t2 :=
      \sum_(t1 <= t < t2) is_interference_from_another_task_with_higher_eq_priority j t.

    (* ... (d) cumulative interference... *)
    Let cumulative_interference j t1 t2 := \sum_(t1 <= t < t2) interference j t.

    (* ... (e) cumulative workload from jobs with higher or equal priority... *)
    Let cumulative_interfering_workload_of_jobs_with_hep_priority j t1 t2 :=
      \sum_(t1 <= t < t2) interfering_workload_of_jobs_with_hep_priority j t.

    (* ... (f) and cumulative interfering workload. *)
    Let cumulative_interfering_workload j t1 t2 := \sum_(t1 <= t < t2) interfering_workload j t.

    (* Instantiated functions usually do not have any useful lemmas about them. In order to
       reuse existing lemmas, we need to prove equivalence of the instantiated functions to 
       some conventional notions. Instantiations given in this file are equivalent to 
       service and workload. Further, we prove these equivalences formally. *)
    
    (* Before we present the formal proofs of the equivalences, we recall
       the notion of workload of higher or equal priority jobs. *)
    Let workload_of_other_jobs_with_hep_priority j t1 t2 :=
      workload_of_jobs job_cost (arrivals_between t1 t2)
                       (fun jhp => another_job_with_higher_eq_priority jhp j).

    (* Similarly, we recall notions of service of higher or equal priority jobs from other tasks... *)
    Let service_of_jobs_from_other_tasks_with_hep_priority j t1 t2 :=
      service_of_jobs sched (arrivals_between t1 t2)
                      (fun jhp => job_from_another_task_with_higher_eq_priority jhp j) t1 t2.

    (* ... and service of all other jobs with higher or equal priority. *)
    Let service_of_other_jobs_with_hep_priority j t1 t2 :=
      service_of_jobs sched (arrivals_between t1 t2)
                      (fun jhp => another_job_with_higher_eq_priority jhp j) t1 t2.
    
    (** ** Equivalences *)
    (** In this section we prove a few equivalences between definitions obtained by 
        instantiation of definitions from the Abstract RTA module (interference and
        interfering workload) and definitions corresponding to the conventional concepts.
        
        As it was mentioned previously, instantiated functions of interference and 
        interfering workload usually do not have any useful lemmas about them. Hovewer,
        it is possible to prove their equivalence to the more conventional notions like 
        service or workload. Next we prove the equivalence between the instantiations 
        and conventional notions. *)
    Section Equivalences.
      
      (* We prove that we can split cumulative interference into two parts: (1) cumulative priority 
         inversion and (2) cumulative interference from jobs with higher or equal priority. *)
      Lemma cumulative_interference_split:
        forall j t1 t2,
          cumulative_interference j t1 t2
          = cumulative_priority_inversion j t1 t2 + cumulative_interference_from_other_jobs j t1 t2.
        rewrite /cumulative_interference /cumulative_priority_inversion
                /cumulative_interference_from_other_jobs /interference.
        intros; rewrite -big_split //=.
        apply/eqP; rewrite eqn_leq; apply/andP; split; rewrite leq_sum; try done.
        { intros t _; unfold is_priority_inversion,
                      BusyIntervalJLFP.is_priority_inversion,
                      is_interference_from_another_job_with_higher_eq_priority.
          case SCHED: (sched t) => [s | ]; last by done.
            by case HP: (higher_eq_priority s j); simpl; rewrite ?addn0 ?add0n.
        }              
        { intros t _; unfold is_priority_inversion,
                      BusyIntervalJLFP.is_priority_inversion,
                      is_interference_from_another_job_with_higher_eq_priority.
          case SCHED: (sched t) => [s | ]; last by done.
          unfold another_job_with_higher_eq_priority.
            by case HP: (higher_eq_priority s j); simpl; rewrite ?addn0 ?add0n.
        }
      Qed.          

      (* Let j be any job of task tsk, and let upp_t be any time instant after job j's arrival.
         Then for any time interval lying before upp_t, the cumulative interference received by tsk 
         is equal to the sum of the cumulative priority inversion of job j and the cumulative interference
         incurred by task tsk due to other tasks. *)
      Lemma cumulative_task_interference_split: 
        forall j t1 t2 upp_t,
          job_task j = tsk ->
          t2 <= upp_t ->
          j \in jobs_arrived_before arr_seq upp_t ->
          ~~ job_completed_by j t2 ->
          cumulative_task_interference interference tsk upp_t t1 t2 = 
          cumulative_priority_inversion j t1 t2 +
          cumulative_interference_from_other_tasks j t1 t2.
      Proof.
        rewrite /cumulative_task_interference /AbstractSeqRTA.cumul_task_interference
                /ScheduleOfTask.task_scheduled_at
                /cumulative_priority_inversion
                /cumulative_interference_from_other_tasks.
        clear H_R_is_maximum R.
        intros j t1 R upp TSK GE ARR NCOMPL. 
        rewrite -big_split //=.
        rewrite big_nat_cond [X in _ = X]big_nat_cond. 
        apply/eqP; rewrite eqn_leq; apply/andP; split. 
        { apply leq_sum; intros t _.
          rewrite /interference /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion
                  /is_interference_from_another_task_with_higher_eq_priority
                  /is_interference_from_another_job_with_higher_eq_priority
                  /AbstractSeqRTA.task_interference_received_before
                  /another_job_with_higher_eq_priority /job_from_another_task_with_higher_eq_priority
                  /ScheduleOfTask.task_scheduled_at.
          case SCHED: (sched t) => [s | ]; last by rewrite has_pred0 addn0 leqn0 eqb0.
          case HP: (higher_eq_priority s j); simpl; last by rewrite addn0 leq_b1. 
          rewrite add0n TSK.
          case: ((job_task s != tsk)); last by done.
            by rewrite Bool.andb_true_l leq_b1.
        }                   
        { apply leq_sum; move => t /andP [/andP [_ LT'] _].
          rewrite /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion
                  /is_interference_from_another_task_with_higher_eq_priority
                  /is_interference_from_another_job_with_higher_eq_priority /another_job_with_higher_eq_priority
                  /job_from_another_task_with_higher_eq_priority /AbstractSeqRTA.task_interference_received_before
                  /ScheduleOfTask.task_scheduled_at .
          case SCHED: (sched t) => [s | ]; last by done.
          rewrite -TSK; case TSKEQ: (job_task s == job_task j); simpl. 
          { rewrite Bool.andb_false_r leqn0 addn0 eqb0.
            unfold higher_eq_priority.
            rewrite -ltnNge; apply/negP; intros NEQ.
            move: NCOMPL => /negP NCOMPL; apply: NCOMPL.
            apply completion_monotonic with t; [ by done | by apply ltnW | ].
            move: SCHED => /eqP SCHED.
            eapply H_sequential_jobs with (j2 := s); try done.
            { rewrite eq_sym TSKEQ; by done. } 
            { by move: TSKEQ => /eqP TSKEQ; rewrite /job_deadline TSKEQ ltn_add2r in NEQ. }
          }
          have NEQ: s != j.
          { apply/negP; intros EQ; move: EQ => /eqP EQ.
            move: TSKEQ => /eqP TSKEQ; apply: TSKEQ.
              by rewrite EQ.
          }
          have Fact: forall b, ~~ b + b = true; first by intros b; destruct b.
          rewrite Bool.andb_true_r Fact; simpl; rewrite lt0b; clear Fact.
          apply/hasP; exists j.
          { rewrite /arrivals_of_task_before /arrivals_of_task_between.
            rewrite /arrivals_of_task_between mem_filter; apply/andP; split; first by rewrite /is_job_of_task. 
              by unfold jobs_arrived_before in ARR; apply jobs_arrived_between_sub with (t2 := 0) (t3 := upp). 
          }
          { case HP: (higher_eq_priority s j).
            { apply/orP; right.
              rewrite /is_interference_from_another_job_with_higher_eq_priority SCHED.
                by rewrite /another_job_with_higher_eq_priority NEQ Bool.andb_true_r. }
            { apply/orP; left.
                by rewrite /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion SCHED HP. }
          } 
        }
      Qed.

      (* In this section we prove that the (abstract) cumulative interfering workload is equivalent to 
         conventional workload, i.e., the one defined with concrete schedule parameters. *)
      Section InstantiatedWorkloadEquivalence.

        (* Let [t1,t2) be any time interval. *)
        Variables t1 t2: time.
        
        (* Consider any job j of tsk. *)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_tsk: job_task j = tsk.

        (* Then for any job j, the cumulative interfering workload is equal to the conventional workload. *)
        Lemma instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs:
          cumulative_interfering_workload_of_jobs_with_hep_priority j t1 t2
          = workload_of_other_jobs_with_hep_priority j t1 t2.
        Proof.
          intros.
          unfold cumulative_interfering_workload_of_jobs_with_hep_priority, workload_of_other_jobs_with_hep_priority.
          case NEQ: (t1 < t2); last first.
          { move: NEQ => /negP /negP; rewrite -leqNgt; move => NEQ.
            rewrite big_geq; last by done.
            rewrite /arrivals_between /jobs_arrived_between big_geq; last by done.
              by rewrite /workload_of_jobs big_nil.
          }
          { unfold interfering_workload_of_jobs_with_hep_priority, workload_of_jobs.
            have EX: exists k, t2 = t1 + k.
            { exists (t2 - t1). rewrite subnKC. by done.  by rewrite ltnW.  } 
            move: EX => [k EQ]. subst t2. clear NEQ.
            induction k.
            - rewrite !addn0.
              rewrite big_geq; last by done.
              rewrite /arrivals_between /jobs_arrived_between big_geq; last by done.
                by rewrite /workload_of_jobs big_nil.
            - rewrite addnS big_nat_recr //=; last by rewrite leq_addr.
              rewrite IHk.
              rewrite /arrivals_between /jobs_arrived_between big_nat_recr //=; last by rewrite leq_addr.
                by rewrite big_cat //=.
          }
        Qed.
        
      End InstantiatedWorkloadEquivalence.

      (* In this section we prove that the (abstract) cumulative interference of jobs with higher or 
         equal priority is equal to total service of jobs with higher or equal priority. *)
      Section InstantiatedServiceEquivalences.

        (* Consider any job j of tsk. *)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_tsk: job_task j = tsk.

        (* We consider an arbitrary time interval [t1, t) that starts with a quiet time. *)
        Variable t1 t: time.
        Hypothesis H_quiet_time: quiet_time j t1.

        (* Then for any job j, the (abstract) instantiated function of interference is 
           equal to the total service of jobs with higher or equal priority. *)
        Lemma instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs:
          cumulative_interference_from_other_jobs j t1 t = service_of_other_jobs_with_hep_priority j t1 t.
        Proof.
          { rewrite /cumulative_interference_from_other_jobs /is_interference_from_another_job_with_higher_eq_priority
                    /service_of_other_jobs_with_hep_priority.
            case NEQ: (t1 <= t); last first.
            { apply negbT in NEQ; rewrite -ltnNge in NEQ.
              rewrite big_geq; last by apply ltnW.
              rewrite /service_of_jobs /arrivals_between /jobs_arrived_between big_geq; last by apply ltnW.
                by rewrite big_nil.
            }
            have EX: exists k, t = t1 + k.
            { by exists (t - t1); rewrite subnKC. } move: EX => [k EQ]. subst t. clear NEQ.
            induction k.
            - rewrite addn0 big_geq; last by done.
                by rewrite /arrivals_between /jobs_arrived_between big_geq // /service_of_jobs big_nil.
            - unfold service_of_jobs, service_during.
              unfold is_interference_from_another_job_with_higher_eq_priority.
              rewrite addnS. 
              rewrite big_nat_recr //=.
              unfold arrivals_between, jobs_arrived_between.
              rewrite big_nat_recr //=.
              rewrite big_cat //=.
              rewrite IHk.
              have EQ:
                \sum_(i0 <- jobs_arriving_at arr_seq (t1 + k) | higher_eq_priority i0 j && (i0 != j))
                 \sum_(t1 <= t0 < (t1 + k).+1) service_at sched i0 t0
                =
                \sum_(i0 <- jobs_arriving_at arr_seq (t1 + k) | higher_eq_priority i0 j && (i0 != j))
                 \sum_(t1 + k <= t0 < (t1 + k).+1) service_at sched i0 t0.
              {
                rewrite big_seq_cond [X in _ = X]big_seq_cond.
                apply/eqP; rewrite eqn_leq; apply/andP; split.
                {
                  rewrite leq_sum //.
                  move => jo /andP [ARR /andP [HP NTSK]].
                  rewrite (@big_cat_nat _ _ _ (t1 + k)) //=.
                  rewrite -[X in _ <= X]add0n leq_add //.
                  rewrite leqn0.
                  rewrite big_nat_cond.
                  rewrite big1 //.
                  move => x /andP [/andP [_ LT] _].
                  apply/eqP; rewrite eqb0; apply/negP; intros NSCHED.
                  unfold jobs_must_arrive_to_execute, arrival_times_are_consistent in *.
                  apply H_jobs_must_arrive_to_execute in NSCHED.
                  unfold has_arrived in NSCHED.
                  apply H_arrival_times_are_consistent in ARR.                  
                  rewrite -ARR in LT.
                    by move: LT; rewrite ltnNge; move => /negP LT.
                      by rewrite leq_addr.
                }
                {
                  rewrite leq_sum //.
                  move => jo /andP [ARR /andP [HP NTSK]].
                  rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + k )) //=. rewrite leq_addl //.
                    by rewrite leq_addr.
                }
              }              
              rewrite EQ.              
              apply/eqP. 
              rewrite exchange_big //=.
              rewrite (@big_cat_nat _ _ _ (t1 + k)) //=.
              rewrite exchange_big //=.              
              rewrite  big_nat1.
              rewrite -addnA.
              rewrite eqn_add2l.
              rewrite exchange_big //=.
              rewrite big_nat1.
              rewrite -big_cat //=. rewrite -big_nat_recr //=.              
              clear EQ IHk.
              case SCHED: (sched (t1 + k)) => [jo | ].
              case PRIO: (another_job_with_higher_eq_priority jo j).
              { simpl.
                rewrite eqn_leq; apply/andP; split; last by apply service_of_jobs_le_1 with job_arrival.
                rewrite (big_rem jo) //=.
                rewrite PRIO  /service_at /scheduled_at SCHED eq_refl add1n; by done.
                apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival); try done.
                unfold jobs_come_from_arrival_sequence in *.
                apply H_jobs_come_from_arrival_sequence with (t1 + k). by rewrite /scheduled_at SCHED.
                { move: PRIO => /andP [PRIO1 PRIO2].
                  rewrite /arrived_between ltnS; apply/andP; split.
                  { rewrite leqNgt; apply/negP; intros AB.
                    move: (SCHED) => /eqP /negP SCHED2; apply: SCHED2.
                    apply/negP.
                    apply completed_implies_not_scheduled with job_cost; try done.
                    apply completion_monotonic with t1; try done.
                    rewrite leq_addr; by done.
                    apply H_quiet_time; try done.
                    move: SCHED => /eqP SCHED.
                      by apply H_jobs_come_from_arrival_sequence  in SCHED.
                  }
                  {
                    move: SCHED => /eqP SCHED.
                      by apply H_jobs_must_arrive_to_execute in SCHED.
                  }
                }
              }
              { 
                simpl.
                rewrite eq_sym big1 //.
                intros joo PRIO2.
                apply/eqP; rewrite eqb0; apply/negP; intros SCHED2.
                move: SCHED2 => /eqP SCHED2.
                rewrite SCHED2 in SCHED.
                inversion SCHED; subst joo.
                  by rewrite PRIO in PRIO2.
              }
              { simpl.
                rewrite eq_sym big1 //.
                intros.
                  by rewrite /service_at /scheduled_at SCHED. 
              }
                by rewrite leq_addr.
                by rewrite leq_addr .
                  by rewrite leq_addr.
                    by rewrite leq_addr.
          }
        Qed.

        (* The same applies to the alternative definition of interference. *)
        Lemma instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks:
          cumulative_interference_from_other_tasks j t1 t = service_of_jobs_from_other_tasks_with_hep_priority j t1 t.
        Proof.
          rewrite /cumulative_interference_from_other_tasks /service_of_jobs_from_other_tasks_with_hep_priority 
                  /job_from_another_task_with_higher_eq_priority.
          case NEQ: (t1 <= t); last first.
          { apply negbT in NEQ; rewrite -ltnNge in NEQ.
            rewrite big_geq; last by apply ltnW.
            rewrite /service_of_jobs /arrivals_between /jobs_arrived_between big_geq; last by apply ltnW.
              by rewrite big_nil.
          }
          { have EX: exists k, t = t1 + k; first by exists (t - t1); rewrite subnKC. 
            move: EX => [k EQ]; subst t; clear NEQ.
            induction k. 
            - rewrite addn0 big_geq; last by done.
                by rewrite /arrivals_between /jobs_arrived_between big_geq // /service_of_jobs big_nil.
            - unfold service_of_jobs, service_during.
              unfold is_interference_from_another_job_with_higher_eq_priority.
              rewrite addnS. 
              rewrite big_nat_recr //=.              
              unfold arrivals_between, jobs_arrived_between.
              rewrite big_nat_recr //=.
              rewrite big_cat //=.
              rewrite IHk.
              have EQ:
                \sum_(i0 <- jobs_arriving_at arr_seq (t1 + k) | higher_eq_priority i0 j &&
                                                                                  (job_task i0 != job_task j))
                 \sum_(t1 <= t0 < (t1 + k).+1) service_at sched i0 t0
                =
                \sum_(i0 <- jobs_arriving_at arr_seq (t1 + k) | higher_eq_priority i0 j &&
                                                                                  (job_task i0 != job_task j))
                 \sum_(t1 + k <= t0 < (t1 + k).+1) service_at sched i0 t0.
              {
                rewrite big_seq_cond [X in _ = X]big_seq_cond.
                apply/eqP; rewrite eqn_leq; apply/andP; split.
                {
                  rewrite leq_sum //.
                  move => jo /andP [ARR /andP [HP NTSK]].
                  rewrite (@big_cat_nat _ _ _ (t1 + k)) //=.
                  rewrite -[X in _ <= X]add0n leq_add //.
                  rewrite leqn0.
                  rewrite big_nat_cond.
                  rewrite big1 //.
                  move => x /andP [/andP [_ LT] _].
                  apply/eqP; rewrite eqb0; apply/negP; intros NSCHED.
                  unfold jobs_must_arrive_to_execute, arrival_times_are_consistent in *.
                  apply H_jobs_must_arrive_to_execute in NSCHED.
                  unfold has_arrived in NSCHED.
                  apply H_arrival_times_are_consistent in ARR.
                  rewrite -ARR in LT.
                    by move: LT; rewrite ltnNge; move => /negP LT.
                      by rewrite leq_addr.
                }
                {
                  rewrite leq_sum //.
                  move => jo /andP [ARR /andP [HP NTSK]].
                  rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + k )) //=. rewrite leq_addl //.
                    by rewrite leq_addr.
                }
              }
              rewrite EQ.
              apply/eqP. 
              rewrite exchange_big //=.
              rewrite (@big_cat_nat _ _ _ (t1 + k)) //=.
              rewrite exchange_big //=.
              rewrite  big_nat1.
              rewrite -addnA.
              rewrite eqn_add2l.
              rewrite exchange_big //=.
              rewrite big_nat1.
              rewrite -big_cat //=. rewrite -big_nat_recr //=.
              clear EQ IHk.
              case SCHED: (sched (t1 + k)) => [jo | ].
              unfold is_interference_from_another_task_with_higher_eq_priority.
              case PRIO: (job_from_another_task_with_higher_eq_priority jo j).
              { simpl.
                rewrite eqn_leq; apply/andP; split.
                { rewrite (big_rem jo) //=.
                  unfold job_from_another_task_with_higher_eq_priority in PRIO.
                  rewrite PRIO /job_from_another_task_with_higher_eq_priority
                          /is_interference_from_another_task_with_higher_eq_priority /service_at
                          /scheduled_at SCHED eq_refl add1n PRIO; by done.
                  apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival); try done.
                  unfold jobs_come_from_arrival_sequence in *.
                  apply H_jobs_come_from_arrival_sequence with (t1 + k). by rewrite /scheduled_at SCHED.
                  { move: PRIO => /andP [PRIO1 PRIO2].
                    rewrite /arrived_between ltnS; apply/andP; split.
                    { rewrite leqNgt; apply/negP; intros AB.
                      move: (SCHED) => /eqP /negP SCHED2; apply: SCHED2.
                      apply/negP.
                      apply completed_implies_not_scheduled with job_cost; try done.
                      apply completion_monotonic with t1; try done.
                      rewrite leq_addr; by done.
                      apply H_quiet_time; try done.
                      move: SCHED => /eqP SCHED.
                        by apply H_jobs_come_from_arrival_sequence  in SCHED.
                    }
                    {
                      move: SCHED => /eqP SCHED.
                        by apply H_jobs_must_arrive_to_execute in SCHED.
                    }
                  }
                }
                {
                  rewrite SCHED PRIO.
                    by apply service_of_jobs_le_1 with job_arrival.
                }
              }
              {
                simpl. rewrite SCHED.
                rewrite eq_sym big1. rewrite PRIO //.
                intros joo PRIO2.
                apply/eqP; rewrite eqb0; apply/negP; intros SCHED2.
                move: SCHED2 => /eqP SCHED2.
                rewrite SCHED2 in SCHED.
                inversion SCHED; subst joo.
                unfold job_from_another_task_with_higher_eq_priority in PRIO.
                  by rewrite PRIO in PRIO2.
              }
              { simpl.
                rewrite /is_interference_from_another_task_with_higher_eq_priority eq_sym big1 //.
                rewrite SCHED; by done.
                intros.
                  by rewrite /service_at /scheduled_at SCHED. 
              }
                by rewrite leq_addr.
                by rewrite leq_addr .
                  by rewrite leq_addr.
                    by rewrite leq_addr.
          }
        Qed.
        
      End InstantiatedServiceEquivalences.

      (* In this section we prove that the abstract definition of busy interval is equivalent to 
         the conventional, concrete definition of busy interval for EDF scheduling. *)
      Section BusyIntervalEquivalence.

        (* Consider any job j of tsk. *)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_tsk: job_task j = tsk.
        Hypothesis H_job_cost_positive: job_cost_positive job_cost j.

        (* We prove that the concept of quiet time obtained by instantiating the abstract 
           definition of quiet time coincides with the conventional definition of quiet time
           (which is defined in module limited.busy_interval). *)
        Lemma instantiated_quiet_time_equivalent_edf_quiet_time:
          forall t,
            quiet_time j t <->
            AbstractRTADefinitions.quiet_time job_arrival job_cost sched interference interfering_workload j t.
        Proof.
          have zero_is_quiet_time: forall j, quiet_time j 0.
          { by intros jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0. }
          have CIS := cumulative_interference_split.
          have IC1 := instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs.
          have IC2 := instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks.
          rewrite /cumulative_interference
                   /cumulative_interference_from_other_jobs
                   /interference /interfering_workload /cumulative_interference_from_other_tasks
                   /service_of_jobs_from_other_tasks_with_hep_priority  
                   /service_of_other_jobs_with_hep_priority /job_from_another_task_with_higher_eq_priority
             in CIS, IC1, IC2.
          intros t; split; intros.
          { unfold AbstractRTADefinitions.quiet_time; split.
            { rewrite /cumulative_interference /AbstractRTADefinitions.cumul_interference
                      /AbstractRTADefinitions.cumul_interfering_workload
                      /cumulative_interference_from_other_jobs
                      /interference /interfering_workload.
              rewrite CIS !big_split //=.
              apply/eqP; rewrite eqn_add2l.
              have L11 := all_jobs_have_completed_equiv_workload_eq_service.
              rewrite IC1; last by apply zero_is_quiet_time.
              have L2 := instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs;
                  rewrite /cumulative_interfering_workload_of_jobs_with_hep_priority in L2.
              rewrite L2.
              rewrite eq_sym; apply/eqP. 
              apply L11 with job_arrival; try done.
              intros.
              apply H; try done.
              apply in_arrivals_implies_arrived in H0; by done.
              move: H1 => /andP [H3 H4].
              unfold FP_to_JLFP.  by done.
              apply in_arrivals_implies_arrived_between with (job_arrival0 := job_arrival) in H0; try done.
            }
            {
              unfold pending_earlier_and_at. 
              rewrite negb_and Bool.negb_involutive; apply/orP.
              case ARR: (arrived_before job_arrival j t); [right | by left]. 
              apply H; try done.
                by unfold higher_eq_priority, EDF.
            }
          }
          {
            intros jhp ARR HP ARB.
            eapply all_jobs_have_completed_equiv_workload_eq_service with
            (P :=  (fun jhp => higher_eq_priority jhp j)) (t1 := 0)(t2 := t); eauto 2; last first.
            eapply arrived_between_implies_in_arrivals; eauto 2.
            move: H => [H0 H1].
            move: H0.
            rewrite /AbstractRTADefinitions.cumul_interference /AbstractRTADefinitions.cumul_interfering_workload
                    /interference /interfering_workload.
            rewrite CIS !big_split //=; move => /eqP; rewrite eqn_add2l.
            rewrite IC1; last by apply zero_is_quiet_time.
            have L2 := instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs;
                         rewrite /cumulative_interfering_workload_of_jobs_with_hep_priority in L2.
            rewrite L2. move => H2.
            have H2EQ: 
              service_of_jobs sched (arrivals_between 0 t)
                              (fun jhp : Job =>
                                 higher_eq_priority jhp j) 0 t ==
              workload_of_jobs job_cost (arrivals_between 0 t)
                               (fun jhp : Job =>
                                  higher_eq_priority jhp j).
            { move: H1; rewrite negb_and Bool.negb_involutive -leqNgt; move => /orP [H1 | H1].
              { intros.
                have NOTIN: j \notin arrivals_between 0 t.
                { apply/memPn.
                  intros jo IN; apply/negP; intros EQ; move: EQ => /eqP EQ.
                  subst jo.
                  unfold arrivals_between in *.
                  apply in_arrivals_implies_arrived_between with (job_arrival0:= job_arrival) in IN; try done.
                    by move: IN => /andP [_ IN]; move: H1; rewrite leqNgt; move => /negP LT; apply: LT.
                }
                have UL1 := sum_notin_rem_eqn.
                rewrite /workload_of_other_jobs_with_hep_priority
                  /another_job_with_higher_eq_priority in H2.
                  by rewrite /service_of_jobs /workload_of_jobs !sum_notin_rem_eqn in H2.
              }
              {
                have JIN: j \in arrivals_between 0 t.
                { eapply completed_implies_scheduled_before in H1; eauto 2.
                  apply arrived_between_implies_in_arrivals with (job_arrival0:= job_arrival); try done.
                  move: H1 => [t' [H3 _]].
                  apply/andP; split; first by done.
                  move: H3 => /andP [H3e H3t].
                    by apply leq_ltn_trans with t'.
                }
                have UNIC: uniq (arrivals_between 0 t).
                { by eapply arrivals_uniq; eauto 2. }
                unfold service_of_jobs, workload_of_jobs in H2.
                unfold service_of_jobs, workload_of_jobs.
                rewrite big_mkcond //=.
                rewrite (bigD1_seq j) //=.
                rewrite -big_mkcondl //=.
                move: H2 => /eqP H2. rewrite H2.
                rewrite [X in _ == X]big_mkcond //=.
                rewrite [X in _ == X](bigD1_seq j) //=.
                rewrite -big_mkcondl //=.
                rewrite eqn_add2r.
                move: H1 => /eqP H1.
                  by rewrite -H1.
              }
            }
              by move: H2EQ => /eqP H2EQ.
          }
        Qed.

        (* Based on that, we prove that the concept of busy interval obtained by instantiating the abstract 
           definition of busy interval coincides with the conventional definition of busy interval. *)
        Lemma instantiated_busy_interval_equivalent_edf_busy_interval:
          forall t1 t2,
            busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 <-> 
            AbstractRTADefinitions.busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2.
        Proof.
          split.
          {
            move => [[NEQ [QTt1 [NQT REL]] QTt2]].
            - split; last by eapply instantiated_quiet_time_equivalent_edf_quiet_time in QTt2; eauto 2.
            - split; first by done. 
            - split; first by apply instantiated_quiet_time_equivalent_edf_quiet_time in QTt1; eauto 2.
                by intros t NEQ' QT; eapply NQT; eauto 2; apply instantiated_quiet_time_equivalent_edf_quiet_time.
          }
          { move => [[/andP [NEQ1 NEQ2] [QTt1 NQT] QTt2]].
            - split; last by eapply instantiated_quiet_time_equivalent_edf_quiet_time; eauto 2.
            - split; first by apply leq_ltn_trans with (job_arrival j). 
            - split; first by eapply instantiated_quiet_time_equivalent_edf_quiet_time; eauto 2.
            - split; first by intros t NEQ QT; eapply NQT; eauto 2; eapply instantiated_quiet_time_equivalent_edf_quiet_time in QT; eauto 2.
            - by apply/andP; split.
          }
        Qed.
        
      End BusyIntervalEquivalence.
      
    End Equivalences.

    (** ** Filling Out Hypothesis Of Abstract RTA Theorem *)
    (** In this section we prove that all hypotheses necessary to use the abstract theorem are satisfied. *)
    Section FillingOutHypothesesOfAbstractRTATheorem.

      (* First, we prove that in the instantiation of interference and interfering workload, 
         we really take into account everything that can interfere with tsk's jobs, and thus, 
         the scheduler satisfies the abstract notion of work conserving schedule. *)
      Lemma instantiated_i_and_w_are_coherent_with_schedule:
        AbstractRTADefinitions.work_conserving
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload.
      Proof.
        intros j t1 t2 t ARR TSK POS BUSY NEQ; split; intros HYP.
        { move: HYP => /negP.
          rewrite negb_or /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion
                  /is_interference_from_another_job_with_higher_eq_priority.
          move => /andP [HYP1 HYP2].
          case SCHED: (sched t) => [s | ].
          { rewrite SCHED in HYP1, HYP2. 
            move: HYP1 HYP2.
            rewrite Bool.negb_involutive negb_and.
            move => HYP1 /orP [/negP HYP2| /eqP HYP2].
            - by exfalso.
            - rewrite Bool.negb_involutive in HYP2.
              move: HYP2 => /eqP /eqP HYP2.
                by subst s; rewrite /scheduled_at SCHED.
          }
          { exfalso; clear HYP1 HYP2.
            apply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; try done.
            have EQ:= not_quiet_implies_not_idle
                        job_arrival job_cost arr_seq
                        _ sched higher_eq_priority j _ _ _ _ _ _ t1 t2 _ t.
            feed_n 9 EQ; try done.
            { by rewrite /higher_eq_priority /EDF. }
            { by move: BUSY => [PREF _]. }            
              by eapply EQ; apply/eqP.
          }
        }
        { move: HYP => /eqP HYP.
          apply/negP; rewrite /interference /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion
                              /is_interference_from_another_job_with_higher_eq_priority HYP negb_or; apply/andP; split.
          - by rewrite Bool.negb_involutive /higher_eq_priority /EDF.
          - by rewrite negb_and Bool.negb_involutive; apply/orP; right.
        }
      Qed.

      (* Next, we prove that the interference and interfering workload 
         functions are consistent with the task service. *)
      Lemma instantiated_interference_and_workload_consistent_with_sequential_jobs:
        AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload.          
      Proof. 
        intros j t1 t2 ARR TSK POS BUSY. 
        apply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; try done.
        eapply all_jobs_have_completed_equiv_workload_eq_service; eauto 2.
        intros s INs TSKs.
        rewrite /arrivals_between in INs.
        move: (INs) => NEQ.
        eapply in_arrivals_implies_arrived_between in NEQ; eauto 2.
        move: NEQ => /andP [_ JAs].
        move: (BUSY) => [[ _ [QT [_ /andP [JAj _]]] _]].
        apply QT; try done.
        - eapply in_arrivals_implies_arrived; eauto 2.
        - unfold higher_eq_priority, EDF.
          move: TSKs => /eqP TSKs.
          rewrite /job_deadline TSK TSKs leq_add2r.
            by apply leq_trans with t1; [apply ltnW | ].
      Qed.

      (* Recall that L is assumed to be a fixed point of the busy interval recurrence. Thanks to
         this fact, we can prove that every busy interval (according to the concrete definition) 
         is bounded. In addition, we know that the conventional concept of busy interval and the 
         one obtained from the abstract definition (with the interference and interfering 
         workload) coincide. Thus, it follows that any busy interval (in the abstract sense) 
         is bounded. *)
      Lemma instantiated_busy_intervals_are_bounded:
        AbstractRTADefinitions.busy_intervals_are_bounded_by
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L.
      Proof.
        intros j ARR TSK POS.   
        have EX := exists_busy_interval
                     job_arrival job_cost arr_seq _ sched _
                     higher_eq_priority j _ _ _ _ _ _ priority_inversion_bound _ L.
        feed_n 12 EX; try eauto 2.
        { by unfold JLFP_is_reflexive, reflexive, higher_eq_priority, EDF. }
        { intros. 
          rewrite {2}H_fixed_point leq_add //.
          apply leq_trans with (workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + L)) predT).
          - rewrite /workload_of_higher_or_equal_priority_jobs /workload_of_jobs
                    big_mkcond [X in _ <= X]big_mkcond leq_sum //=.
            intros s _.
              by case (higher_eq_priority s j).
          - apply total_workload_le_total_rbf'' with job_task; try done.
            intros tsk0 IN0.
              by move: (H_family_of_proper_arrival_curves tsk0 IN0) => [ARRB _].              
        } 
        move: EX => [t1 [t2 [H1 [H2 GGG]]]].
        exists t1, t2; split; first by done.
        split; first by done.
          by eapply instantiated_busy_interval_equivalent_edf_busy_interval; eauto 2.
      Qed.

      (* Next, we prove that IBF is indeed an interference bound.

         Recall that in module abstract_seq_RTA hypothesis task_interference_is_bounded_by expects 
         to receive a function that maps some task t, the relative arrival time of a job j of task t, 
         and the length of the interval to the maximum amount of interference (for more details see 
         files limited.abstract_RTA.definitions and limited.abstract_RTA.abstract_seq_rta).

         However, in this module we analyze only one task -- tsk, therefore it is “hardcoded” 
         inside the interference bound function IBF. Therefore, in order for the IBF signature to
         match the required signature in module abstract_seq_RTA, we wrap the IBF function in a 
         function that accepts, but simply ignores the task. *)
      Lemma instantiated_task_interference_is_bounded:
        AbstractSeqRTA.task_interference_is_bounded_by
          job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload
          (fun tsk A R => IBF A R).
      Proof. 
        clear H_R_is_maximum R. 
        intros j R t1 t2 ARR TSK N NCOMPL BUSY. 
        move: (posnP (job_cost j)) => [ZERO|POS].
        { exfalso.
          move: NCOMPL => /negP COMPL; apply: COMPL.
          rewrite /is_response_time_bound_of_job /completed_by eqn_leq; apply/andP; split.
          - by apply H_completed_jobs_dont_execute.
          - by rewrite ZERO.
        }    
        move: (BUSY) => [[/andP [JINBI JINBI2] [QT _]] _]. 
        set (A := job_arrival j - t1) in *.
        have L2 := cumulative_task_interference_split; rewrite /cumulative_task_interference in L2.
        rewrite (L2 j); try done; first last.
        { by eapply arrived_between_implies_in_arrivals; eauto. }
        { by apply ltnW. }
        { rewrite /I leq_add //.  
          { unfold priority_inversion_is_bounded_by in *.
            apply leq_trans with (cumulative_priority_inversion j t1 t2).
            { rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1  + R)) //=.
              - by rewrite leq_addr.
              - by rewrite /is_priority_inversion leq_addr.
              - by rewrite ltnW.
            }
            { apply H_priority_inversion_is_bounded; try done.
              apply instantiated_busy_interval_equivalent_edf_busy_interval in BUSY; try done.
                by move: BUSY => [PREF _].
            }
          }
          { rewrite instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks
            ; last by rewrite instantiated_quiet_time_equivalent_edf_quiet_time //.
            apply leq_trans with
                (workload_of_jobs job_cost (arrivals_between t1 (t1 + R))
                                  (fun jhp : Job => higher_eq_priority jhp j && (job_task jhp != job_task j))).
            { apply service_of_jobs_le_workload; try done. }
            { rewrite /W /rbf /total_ohep_request_bound_function_FP /task_request_bound_function
                      /workload_of_jobs /arrivals_between.
              set l := jobs_arrived_between arr_seq t1 (t1 + R). 
              set hep := higher_eq_priority.            
              apply leq_trans with
                  (\sum_(tsk_o <- ts | tsk_o != tsk)
                    (\sum_(j0 <- l | hep j0 j && (job_task j0 == tsk_o)) job_cost j0)).
              { intros.
                have EXCHANGE := exchange_big_dep (fun j0 => hep j0 j && (job_task j0 != job_task j)).
                rewrite EXCHANGE /=; last first.
                { move => tsko jo /negP NEQ /andP [EQ1 /eqP EQ2].
                  rewrite EQ1 Bool.andb_true_l; apply/negP; intros CONTR.
                  apply: NEQ; clear EQ1.
                    by rewrite -TSK -EQ2.
                }
                rewrite /workload_of_jobs /l big_seq_cond [X in _ <= X]big_seq_cond.
                apply leq_sum; move => jo /andP [ARRo /andP [HEQ TSKo]].
                rewrite (big_rem (job_task jo)) //=.
                rewrite HEQ eq_refl -TSK TSKo andTb andTb leq_addr //.
                eapply H_all_jobs_from_taskset, in_arrivals_implies_arrived; eauto 2.
              }                        
              apply leq_sum_seq; intros tsko INtsko NEQT.
              case NEQ: (R <= job_arrival j - t1 + ε + task_deadline tsk - task_deadline tsko). 
              { move: (NEQ) => /minn_idPl => MIN.
                rewrite minnC in MIN; rewrite MIN; clear MIN. 
                apply leq_trans with (task_cost tsko * num_arrivals_of_task job_task arr_seq tsko t1 (t1 + R)).
                { apply leq_trans with (\sum_(j0 <- l | job_task j0 == tsko) job_cost j0).
                  { rewrite big_mkcond [X in _ <= X]big_mkcond //= leq_sum //.
                      by intros s _; case (job_task s == tsko); case (hep s j). }
                  { rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
                    rewrite -/l /workload_of_jobs.
                    rewrite /is_job_of_task  muln1.
                    apply leq_sum_seq; move => j0 IN0 /eqP EQ.
                    rewrite -EQ.
                    apply H_job_cost_le_task_cost.
                      by apply in_arrivals_implies_arrived in IN0.
                  }
                }
                { rewrite leq_mul2l; apply/orP; right.
                  rewrite -{2}[R](addKn t1).
                  move: (H_family_of_proper_arrival_curves tsko INtsko) => [ARRB _].
                    by apply ARRB; rewrite leq_addr.
                }
              }
              { apply negbT in NEQ; rewrite -ltnNge in NEQ; apply ltnW in NEQ.
                move: (NEQ) => /minn_idPr => MIN.
                rewrite minnC in MIN; rewrite MIN; clear MIN.
                set (V := job_arrival j - t1 + ε + task_deadline tsk - task_deadline tsko) in *.              
                apply leq_trans with (task_cost tsko * num_arrivals_of_task job_task arr_seq tsko t1 (t1 + V)).
                { unfold l.                
                  apply leq_trans with
                      (\sum_(jo <- jobs_arrived_between arr_seq t1 (t1 + V) | hep jo j && (job_task jo == tsko))
                        job_cost jo).
                  { rewrite (job_arrived_between_cat _ _ (t1 + V)); [ |rewrite leq_addr //|rewrite leq_add2l //].
                    rewrite big_cat //=. 
                    rewrite -[X in _ <= X]addn0 leq_add2l leqn0.
                    rewrite big_seq_cond.
                    apply/eqP; apply big_pred0.
                    intros jo; apply/negP; intros CONTR.
                    move: CONTR => /andP [ARRIN /andP [HEP /eqP TSKo]].
                    unfold hep, higher_eq_priority, EDF in HEP.
                    eapply in_arrivals_implies_arrived_between in ARRIN; eauto 2.
                    move: ARRIN => /andP [ARRIN _]; unfold V in ARRIN.
                    have EQ1: job_deadline jo = task_deadline tsko; first by rewrite /job_deadline TSKo.
                    rewrite EQ1 in HEP; clear EQ1.
                    have EQ2: job_deadline j = task_deadline tsk; first by rewrite /job_deadline TSK.
                    rewrite EQ2 in HEP; clear EQ2. 
                    case NEQ2: (task_deadline tsko <= job_arrival j - t1 + ε + task_deadline tsk).
                    { move: ARRIN; rewrite leqNgt; move => /negP ARRIN; apply: ARRIN.
                      rewrite -(ltn_add2r (task_deadline tsko)).
                      apply leq_ltn_trans with (job_arrival j + task_deadline tsk); first by done.
                      rewrite addnBA; last by done.
                      rewrite addnA addnA. 
                      rewrite subnKC; last by done.
                      rewrite subnK.
                      - by rewrite ltn_add2r addn1.
                      - apply leq_trans with (job_arrival j - t1 + ε + task_deadline tsk); first by done.
                          by rewrite !leq_add2r leq_subr. 
                    } 
                    { apply negbT in NEQ2; rewrite -ltnNge in NEQ2.
                      move: HEP; rewrite leqNgt; move => /negP HEP; apply: HEP.
                      
                      apply leq_ltn_trans with (job_arrival jo + (job_arrival j - t1 + task_deadline tsk)).
                      { rewrite subh1; last by done.
                        rewrite addnBA; last apply leq_trans with (job_arrival j); [ | by done | by rewrite leq_addr].
                        rewrite [in X in _ <= X]addnC.
                        rewrite -addnBA; first by rewrite leq_addr.
                          by apply leq_trans with (t1 + (job_arrival j - t1 + ε + task_deadline tsk - task_deadline tsko)); first rewrite leq_addr.
                      } 
                      { rewrite ltn_add2l.
                        apply leq_ltn_trans with (job_arrival j - t1 + ε + task_deadline tsk); last by done.
                          by rewrite leq_add2r leq_addr.
                      }
                    }
                  }
                  {
                    intros. 
                    apply leq_trans with
                        (\sum_(jo <- jobs_arrived_between arr_seq t1 (t1 + V) | job_task jo == tsko) job_cost jo).
                    { rewrite big_mkcond [X in _ <= X]big_mkcond //=.
                      rewrite leq_sum //; intros s _.
                        by case (hep s j).
                    }
                    { rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
                      rewrite /is_job_of_task  muln1.
                      apply leq_sum_seq; move => j0 IN0 /eqP EQ.
                      rewrite -EQ.
                      apply H_job_cost_le_task_cost.
                        by apply in_arrivals_implies_arrived in IN0.
                    }                  
                  }                
                }
                { rewrite leq_mul2l; apply/orP; right.
                  rewrite -{2}[V](addKn t1).
                  move: (H_family_of_proper_arrival_curves tsko INtsko) => [ARRB _].
                    by apply ARRB; rewrite leq_addr.
                }                    
              }
            }
          }
        }
      Qed.
      
      (* Finally, we show that there exists a solution for the response-time recurrence. *)
      Section SolutionOfResponseTimeReccurenceExists.

        (* Consider any job j of tsk. *)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_tsk: job_task j = tsk.
        Hypothesis H_job_cost_positive: job_cost_positive job_cost j.

        (* Given any job j of task tsk that arrives exactly A units after the beginning of 
           the busy interval, the bound of the total interference incurred by j within an 
           interval of length Δ is equal to [task_rbf (A + ε) - task_cost tsk + IBF(A, Δ)]. *)
        Let total_interference_bound tsk A Δ :=
          task_rbf (A + ε) - task_cost tsk + IBF A Δ.
        
        (* Next, consider any A from the search space (in abstract sence). *)
        Variable A: time.
        Hypothesis H_A_is_in_abstract_search_space:
          AbstractRTAReduction.is_in_search_space tsk L total_interference_bound A.

        (* We prove that A is also in the concrete search space. *)
        Lemma A_is_in_concrete_search_space:
          is_in_search_space A.
        Proof.
          unfold total_interference_bound in *.
          unfold AbstractRTAReduction.is_in_search_space in H_A_is_in_abstract_search_space.
          unfold is_in_search_space in H_R_is_maximum. 
          move: H_A_is_in_abstract_search_space => [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
          { subst A.
            apply/andP; split; first by done.
            apply/orP; left.
            rewrite neq_ltn; apply/orP; left.
            rewrite /task_rbf /rbf. erewrite rbf.RBF.task_rbf_0_zero; eauto 2.
            rewrite add0n /task_rbf.
            apply leq_trans with (task_cost tsk).
            + apply leq_trans with (job_cost j); try eauto 2. 
                by rewrite -H_job_of_tsk; apply H_job_cost_le_task_cost. 
            + by eapply rbf.RBF.task_rbf_1_ge_task_cost; eauto 2.                    
          }
          { apply/andP; split; first by done.
            apply/negPn/negP; intros EQ; move: EQ => /eqP EQ.
            apply INSP2.
            move: EQ; rewrite negb_or eqb_id Bool.negb_involutive; move => /andP [/eqP EQ1 /hasPn EQ2].
            unfold task_rbf, rbf in EQ1.                  
            rewrite subn1 addn1 prednK; last by done.
            rewrite /task_rbf /rbf -EQ1.
            apply/eqP; rewrite eqn_add2l eqn_add2l.
            unfold W.
            have Abs:
              forall (T: eqType) (xs: seq T) f1 f2 (P: _ -> bool),
                (forall x, x \in xs -> P x -> f1 x == f2 x) ->
                \sum_(x <- xs | P x) f1 x == \sum_(x <- xs | P x) f2 x.
            { clear.
              intros.
              rewrite big_seq_cond [X in _ == X]big_seq_cond.
              rewrite big_mkcond [X in _ == X]big_mkcond //=.
              rewrite eqn_leq; apply/andP; split; rewrite leq_sum //; intros i _.
              - case IN: (i \in xs); last by done.
                case Pi: (P i); simpl; last by done.
                apply H in IN; last by done.
                  by move: IN => /eqP IN; rewrite IN.
              - case IN: (i \in xs); last by done.
                case Pi: (P i); simpl; last by done.
                apply H in IN; last by done.
                  by move: IN => /eqP IN; rewrite IN.              
            }
            apply: Abs; intros tsk_o IN NEQ.
            rewrite addn1 prednK; last by done.
            move: (EQ2 tsk_o IN); clear EQ2.
            rewrite eq_sym NEQ Bool.andb_true_l Bool.negb_involutive; move => /eqP EQ2.
            case CASE: (A + ε + task_deadline tsk - task_deadline tsk_o <= x).
            { have F1: minn (A + task_deadline tsk - task_deadline tsk_o) x =
                       A + task_deadline tsk - task_deadline tsk_o.
              { rewrite minnE.
                have CASE2: A + task_deadline tsk - task_deadline tsk_o <= x.
                {  apply leq_trans with (A + ε + task_deadline tsk - task_deadline tsk_o).
                   - by apply leq_sub2r; rewrite leq_add2r leq_addr.
                   - by done.
                } 
                move: CASE2; rewrite -subn_eq0; move => /eqP CASE2; rewrite CASE2.
                  by rewrite subn0.
              } 
              have F2: minn (A + ε + task_deadline tsk - task_deadline tsk_o) x =
                       A + ε + task_deadline tsk - task_deadline tsk_o.
              { rewrite minnE.
                move: CASE; rewrite -subn_eq0; move => /eqP CASE; rewrite CASE.
                  by rewrite subn0.                
              }
                by apply/eqP; rewrite F1 F2.
            }
            { move: CASE => /negP /negP; rewrite -ltnNge; move => CASE.
              have F1: minn (A + task_deadline tsk - task_deadline tsk_o) x = x.
              { rewrite minnE; rewrite subKn //.
                rewrite -(leq_add2r 1) !addn1.
                rewrite -subSn.
                { rewrite -[in X in _ <= X]addn1.
                    by rewrite -addnA [_ + 1]addnC addnA.
                }
                { intros.
                  have POS := @leq_ltn_trans _ 0 _ _ CASE.
                  feed POS; first by done.
                    by rewrite subn_gt0 -addnA [1 + _]addnC addnA addn1 ltnS in POS.
                } 
              }
              have F2: minn (A + ε + task_deadline tsk - task_deadline tsk_o) x = x.
              { by rewrite minnE; rewrite subKn // ltnW. }
                by apply/eqP; rewrite F1 F2.
            }
          }
        Qed.

        (* Then, there exists solution for response time recurrence. *)
        Corollary correct_search_space:
          exists F,
            A + F = task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk) + IBF A (A + F) /\
            F + (task_cost tsk - task_lock_in_service tsk) <= R.
        Proof.
          unfold total_interference_bound in *.
          unfold AbstractRTAReduction.is_in_search_space in H_A_is_in_abstract_search_space.
          unfold is_in_search_space in H_R_is_maximum.
          move: (H_R_is_maximum A) => FIX.
          feed FIX; first by apply A_is_in_concrete_search_space.
          move: FIX => [F [FIX NEQ]].
          exists F; split; last by done.
          apply/eqP; rewrite {1}FIX.
            by rewrite addnA [_ + priority_inversion_bound]addnC -!addnA.
        Qed.
         
      End SolutionOfResponseTimeReccurenceExists.       
 
    End FillingOutHypothesesOfAbstractRTATheorem.

    (** ** Final Theorem *)
    (* Based on the properties established above, we apply the abstract analysis 
       framework to infer that R is a response-time bound for tsk. *)
    Theorem uniprocessor_response_time_bound_edf:
      response_time_bounded_by tsk R.
    Proof.
      intros js ARRs TSKs.
      move: (posnP (job_cost js)) => [ZERO|POS].
      { rewrite /is_response_time_bound_of_job /completed_by eqn_leq; apply/andP; split.
        - by apply H_completed_jobs_dont_execute.
        - by rewrite ZERO.
      }    
      eapply AbstractSeqRTA.uniprocessor_response_time_bound_seq with
          (interference0 := interference) (interfering_workload0 := interfering_workload)
          (task_interference_bound_function := fun tsk A R => IBF A R) (L0 := L); eauto 3.
      - by apply instantiated_i_and_w_are_coherent_with_schedule.
      - by apply instantiated_interference_and_workload_consistent_with_sequential_jobs.
      - by apply instantiated_busy_intervals_are_bounded.
      - by apply instantiated_task_interference_is_bounded.
      - by eapply correct_search_space; eauto 2.
    Qed.
     
  End AbstractResponseTimeAnalysisForEDF. 
   
End AbstractRTAforEDFwithArrivalCurves. 