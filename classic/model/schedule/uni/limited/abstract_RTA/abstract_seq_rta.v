Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.response_time
               prosa.classic.model.schedule.uni.schedule_of_task.
Require Import prosa.classic.model.schedule.uni.limited.rbf
               prosa.classic.model.schedule.uni.limited.schedule.
Require Import prosa.classic.model.arrival.curves.bounds.
Require Import prosa.classic.analysis.uni.arrival_curves.workload_bound. 
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions
               prosa.classic.model.schedule.uni.limited.abstract_RTA.sufficient_condition_for_lock_in_service
               prosa.classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space
               prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_rta.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Abstract Response-Time Analysis with sequential jobs *)
(** In this module we propose the general framework for response-time analysis (RTA) 
    of uniprocessor scheduling of real-time tasks with arbitrary arrival models
    and sequential jobs. *)
Module AbstractSeqRTA. 

  Import Job ArrivalCurves TaskArrival ScheduleOfTask UniprocessorSchedule Workload
         Service ResponseTime MaxArrivalsWorkloadBound 
         AbstractRTADefinitions AbstractRTALockInService AbstractRTAReduction AbstractRTA. 

  (* In this section we prove that the maximum among the solutions of 
     the response-time bound recurrence for some set of parameters 
     is a response-time bound for tsk. Note that in this section we _do_
     rely on the hypothesis about job sequentiality. This allows us to 
     provide a more precise response-time bound function, since jobs of 
     the same task will be executed strictly in the order they arrive. *) 
  Section Sequential_Abstract_RTA.
    
    Context {Task: eqType}.
    Variable task_cost: Task -> time.    
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any arrival sequence with consistent, non-duplicate arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.
    
    (* Next, consider any uniprocessor schedule of this arrival sequence... *)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
    
    (* Assume that the job costs are no larger than the task costs. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq.

    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_completed_by := completed_by job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    Let task_scheduled_at :=  task_scheduled_at job_task sched.
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.

    (* Consider an arbitrary task set. *)
    Variable ts: list Task.
    
    (* In addition, assume that all jobs come from the task set. *)
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
    
    (* Assume we are provided with abstract functions for interference and interfering workload. *)
    Variable interference: Job -> time -> bool.
    Variable interfering_workload: Job -> time -> time.
            
    (* Let's define some local names for clarity. *)
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.
    Let work_conserving := work_conserving job_arrival job_cost job_task arr_seq sched tsk.
    Let busy_intervals_are_bounded_by := busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk.
    Let job_interference_is_bounded_by := job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk.
    Let busy_interval := busy_interval job_arrival job_cost sched interference interfering_workload.
    Let task_workload_between := task_workload_between job_cost job_task arr_seq tsk.
    Let arrivals_of_task_before := arrivals_of_task_before job_task arr_seq.
    Let task_service_between := task_service_between job_task arr_seq sched tsk.

    (* In this section, we introduce a few new definitions to make it easier to
       express the new bound of the worst-case execution time. *)
    Section Definitions.

      (* When assuming sequential jobs, we can introduce an additional hypothesis that 
         ensures that the values of interference and workload remain consistent. It states 
         that any of tsk's job, that arrived before the busy interval, should be
         completed by the beginning of the busy interval. *)
      Definition interference_and_workload_consistent_with_sequential_jobs :=
        forall j t1 t2,
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_cost j > 0 ->
          busy_interval j t1 t2 ->
          task_workload_between 0 t1 = task_service_between 0 t1.

      (* Next we introduce the notion of task interference. Intuitively, task tsk incurs interference
         when some of the jobs of task tsk incur interference. As a result, tsk cannot make any progress.
         
         More formally, task tsk experiences interference at a time instant time t, if at time t 
         task tsk is not scheduled and there exists a job of tsk that (1) experiences interference and 
         (2) has arrived before some time instant [upper_bound]. 

         It is important to note two subtle points: according to our semantics of the interference function,
         jobs from the same task can cause interference to each other. In the definition of interference of
         a task we want to avoid such situations. That is why we use the term [~~ task_scheduled_at tsk t].

         Moreover, in order to make the definition constructive, we introduce an upper
         bound on the arrival time of jobs from task tsk. As a result, we need to consider only a finite 
         number of jobs. For the function to produce the correct values it is enough to specify 
         a sufficiently large upper_bound. Usually as upper_bound one can use the end 
         of the corresponding busy interval. *)
      Definition task_interference_received_before (tsk: Task) (upper_bound: time) (t: time) :=
        (~~ task_scheduled_at tsk t)
          && has (fun j => interference j t) (arrivals_of_task_before tsk upper_bound).

      (* Next we define the cumulative task interference. *)
      Definition cumul_task_interference tsk upper_bound t1 t2 :=
        \sum_(t1 <= t < t2) task_interference_received_before tsk upper_bound t. 

      (* We say that task interference is bounded by task_interference_bound_function (tIBF) 
         iff for any job j of task tsk cumulative _task_ interference within the interval 
         [t1, t1 + R) is bounded by function tIBF(tsk, A, R). 
         Note that this definition is almost the same as the definition of job_interference_is_bounded_by 
         from the non-nesessary-sequential case. However, in this case we ignore the 
         interference that comes from jobs from the same task. *)        
      Definition task_interference_is_bounded_by (task_interference_bound_function: Task -> time -> time -> time) :=
        forall j R t1 t2,
          arrives_in arr_seq j ->
          job_task j = tsk -> 
          t1 + R < t2 ->  
          ~~ job_completed_by j (t1 + R) ->
          busy_interval j t1 t2 ->
          let offset := job_arrival j - t1 in 
          cumul_task_interference tsk t2 t1 (t1 + R) <= task_interference_bound_function tsk offset R.
             
    End Definitions.

    (* In this section, we prove that the maximum among the solutions of the 
       response-time bound recurrence is a response-time bound for tsk. *)
    Section ResponseTimeBound.

      (* For simplicity, let's define some local names. *)
      Let cumul_interference := cumul_interference interference.
      Let cumul_workload := cumul_interfering_workload interfering_workload.
      Let cumul_task_interference := cumul_task_interference tsk.
      
      (* We assume that the schedule is work-conserving. *)
      Hypothesis H_work_conserving: work_conserving interference interfering_workload. 
      
      (* Unlike the previous theorem [uniprocessor_response_time_bound], we assume 
         that (1) jobs are sequential, moreover (2) functions interference and 
         interfering_workload are consistent with the hypothesis of sequential jobs. *)
      Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.
      Hypothesis H_interference_and_workload_consistent_with_sequential_jobs:
        interference_and_workload_consistent_with_sequential_jobs.

      (* Assume we have a constant L which bounds the busy interval of any of tsk's jobs. *)
      Variable L: time.
      Hypothesis H_busy_interval_exists: busy_intervals_are_bounded_by interference interfering_workload L.

      (* Next, we assume that task_interference_bound_function is a bound on interference incurred by the task. *) 
      Variable task_interference_bound_function: Task -> time -> time -> time.
      Hypothesis H_task_interference_is_bounded: task_interference_is_bounded_by task_interference_bound_function.   

      (* Given any job j of task tsk that arrives exactly A units after the beginning of the busy 
         interval, the bound on the total interference incurred by j within an interval of length Δ 
         is no greater than [task_rbf (A + ε) - task_cost tsk + task's IBF Δ]. Note that in case of 
         sequential jobs the bound consists of two parts: (1) the part that bounds the interference 
         received from other jobs of task tsk -- [task_rbf (A + ε) - task_cost tsk] and (2) any other
         interferece that is bounded by task_IBF(tsk, A, Δ). *)
      Let total_interference_bound tsk A Δ :=
        task_rbf (A + ε) - task_cost tsk + task_interference_bound_function tsk A Δ.

      (* Note that since we consider the modified interference bound function, the search space has
         also changed. One can see that the new search space is guaranteed to include any A for which 
         [task_rbf (A) ≠ task_rbf (A + ε)], since this implies the fact that 
         [total_interference_bound (tsk, A, Δ) ≠ total_interference_bound (tsk, A + ε, Δ)]. *)
      Let is_in_search_space_seq := is_in_search_space tsk L total_interference_bound. 

      (* Consider any value R, and assume that for any relative arrival time A from the search 
         space there is a solution F of the response-time recurrence that is bounded by R. In
         contrast to the formula in "non-sequential" Abstract RTA, assuming that jobs are 
         sequential leads to a more precise response-time bound. Now we can explicitly express 
         the interference caused by other jobs of the task under consideration. 
         
         To understand the right part of the fixpoint in the equation it is helpful to note 
         that the bound on the total interference (bound_of_total_interference) is equal to 
         [task_rbf (A + ε) - task_cost tsk + tIBF tsk A Δ]. Besides, a job must receive 
         enough service to become non-preemptive [task_lock_in_service tsk]. The sum of 
         these two quantities is exactly the right-hand side of the equation. *)
      Variable R: nat. 
      Hypothesis H_R_is_maximum_seq: 
        forall A,
          is_in_search_space_seq A -> 
          exists F,
            A + F = (task_rbf (A + ε) - (task_cost tsk - task_lock_in_service tsk))
                    + task_interference_bound_function tsk A (A + F) /\
            F + (task_cost tsk - task_lock_in_service tsk) <= R.

      (* In this section we prove a few simple lemmas about the completion of jobs from the task 
         considering the busy interval of the job under consideration. *)
      Section CompletionOfJobsFromSameTask.

        (* Consider any two jobs j1 j2 of tsk. *)
        Variable j1 j2: Job. 
        Hypothesis H_j1_arrives: arrives_in arr_seq j1.
        Hypothesis H_j2_arrives: arrives_in arr_seq j2. 
        Hypothesis H_j1_from_tsk: job_task j1 = tsk.
        Hypothesis H_j2_from_tsk: job_task j2 = tsk.
        Hypothesis H_j1_cost_positive: job_cost_positive job_cost j1.
        
        (* Consider the busy interval [t1, t2) of job j1. *)
        Variable t1 t2: time.
        Hypothesis H_busy_interval: busy_interval j1 t1 t2.

        (* We prove that if a job from task tsk arrived before the beginning of the busy 
           interval, then it must be completed before the beginning of the busy interval *)
        Lemma completed_before_beginning_of_busy_interval:
          job_arrival j2 < t1 ->
          completed_by job_cost sched j2 t1. 
        Proof. 
          move => JA; move: (H_j2_from_tsk) => /eqP TSK2eq.
          move: (posnP (job_cost j2)) => [ZERO|POS].
          { by rewrite /is_response_time_bound_of_job /completed_by ZERO. }    
          move: (H_interference_and_workload_consistent_with_sequential_jobs
                   j1 t1 t2 H_j1_arrives H_j1_from_tsk H_j1_cost_positive H_busy_interval) => SWEQ.
          eapply all_jobs_have_completed_equiv_workload_eq_service
            with (j := j2) in SWEQ; eauto 2; try done.
            by apply arrived_between_implies_in_arrivals with job_arrival.
        Qed. 

        (* Next we prove that if a job is pending after the beginning 
           of the busy interval [t1, t2) then it arrives after t1 . *) 
        Lemma arrives_after_beginning_of_busy_interval:
          forall t,
            t1 <= t ->
            job_pending_at j2 t ->
            arrived_between job_arrival j2 t1 t.+1.
        Proof.
          intros t GE PEND.
          rewrite /arrived_between; apply/andP; split; last first.
          { by move: PEND => /andP [ARR _]; rewrite ltnS. }
          rewrite leqNgt; apply/negP; intros LT.
          move: (H_busy_interval) => [[/andP [AFR1 AFR2] [QT _]] _].
          have L12 := completed_before_beginning_of_busy_interval.
          feed L12; try done.
          apply completion_monotonic with (t' := t) in L12; try done.
            by move: PEND => /andP [_ /negP H2].
        Qed.

      End CompletionOfJobsFromSameTask.

      (* Since we are going to use the [uniprocessor_response_time_bound] theorem to prove 
         the theorem of this section, we have to show that all the hypotheses are satisfied. 
         Namely, we need to show that hypotheses [H_sequential_jobs, H_i_w_are_task_consistent 
         and H_task_interference_is_bounded_by] imply [H_job_interference_is_bounded], and the 
         fact that [H_R_is_maximum_seq] implies [H_R_is_maximum]. *)
      
      (* In this section we show that there exists a bound for cumulative interference for any
         job of task tsk, i.e., the hypothesis H_job_interference_is_bounded holds. *)
      Section BoundOfCumulativeJobInterference.

        (* Consider any job j of tsk. *)
        Variable j: Job. 
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_tsk: job_task j = tsk.
        Hypothesis H_job_cost_positive: job_cost_positive job_cost j.

        (* Consider the busy interval [t1, t2) of job j. *)
        Variable t1 t2: time.
        Hypothesis H_busy_interval: busy_interval j t1 t2.

        (* Let's define A as a relative arrival time of job j (with respect to time t1). *)
        Let A := job_arrival j - t1.

        (* Consider an arbitrary time x... *) 
        Variable x: time.
        (* ...such that (t1 + x) is inside the busy interval... *)
        Hypothesis H_inside_busy_interval: t1 + x < t2.
        (* ... and job j is not completed by time (t1 + x). *)
        Hypothesis H_job_j_is_not_completed: ~~ job_completed_by j (t1 + x).

        (* We start by proving that the cumulative interference incurred by job j is bounded by the sum of 
           the task workload on the interval [t1, t1 + A] and the cumulative interference of j's task. *)
        Lemma bound_for_cumulative_job_interference_actual:
          cumul_interference j t1 (t1 + x) <=
          (task_workload_between t1 (t1 + A + ε) - job_cost j) + cumul_task_interference t2 t1 (t1 + x).
        Proof. 
          set (y := t1 + x) in *.
          have IN: j \in arrivals_between t1 (t1 + A + ε).
          { eapply arrived_between_implies_in_arrivals; eauto 2.
            move: (H_busy_interval) => [[/andP [GE _] [_ _]] _].
              by apply/andP; split; last rewrite /A subnKC // addn1.
          }
          have Fact1:
            task_service_of_jobs_received_in job_task arr_seq sched tsk t1 (t1 + A + ε) t1 y
            - service_during sched j t1 y <=
            task_workload_between t1 (t1 + A + ε) - job_cost j.
          { rewrite /task_workload /task_service_of_jobs_received_in /service_of_jobs /workload_of_jobs.
            rewrite (big_rem j) ?[X in _ <= X - _](big_rem j) //=.
            rewrite H_job_of_tsk eq_refl.
            rewrite addnC -addnBA; last by done.
            rewrite [X in _ <= X - _]addnC -addnBA; last by done.
            rewrite !subnn !addn0.
              by apply service_of_jobs_le_workload.
          }
          apply leq_trans with (
                              task_service_of_jobs_received_in job_task arr_seq sched tsk t1 (t1+A+ε) t1 y
                              - service_during sched j t1 y
                              + cumul_task_interference t2 t1 y); [clear Fact1 | by rewrite leq_add2r].
          rewrite /cumul_interference /cumul_interference 
                  /task_service_of_jobs_received_in /service_of_jobs /service_during exchange_big //=
                  /cumul_task_interference /Sequential_Abstract_RTA.cumul_task_interference.
          rewrite -(leq_add2r (\sum_(t1 <= t < y) service_at sched j t)).
          rewrite [X in _ <= X]addnC addnA subnKC; last first.
          { by rewrite exchange_big //= (big_rem j) //= H_job_of_tsk eq_refl leq_addr. }
          rewrite -big_split -big_split //=.
          rewrite big_nat_cond [X in _ <= X]big_nat_cond leq_sum //; move => t /andP [NEQ _].
          have Fact1:
            service_at sched j t <= \sum_(i0 <- arrivals_between t1 (t1 + A + ε) | job_task i0 == tsk) service_at sched i0 t.
          { by rewrite (big_rem j) // H_job_of_tsk eq_refl leq_addr. } 
          unfold task_scheduled_at, ScheduleOfTask.task_scheduled_at.
          case SCHEDt: (sched t) => [s | ]; last first.
          { rewrite {1}/service_at {1}/scheduled_at SCHEDt; simpl; rewrite addn0.
            case INT: (interference j t); last by done.
            apply leq_trans with (task_interference_received_before tsk t2 t); last by rewrite leq_addl.
            rewrite lt0b. 
            rewrite /task_interference_received_before /task_scheduled_at /ScheduleOfTask.task_scheduled_at SCHEDt; simpl.
            apply/hasP; exists j; last by done.
            rewrite /arrivals_of_task_before mem_filter; apply/andP; split.
            - by rewrite /is_job_of_task H_job_of_tsk.
            - move: (H_busy_interval) => [[/andP [_ LT] [_ _]] _].
                by eapply arrived_between_implies_in_arrivals; eauto.
          } 
          have ARRs: arrives_in arr_seq s.
          { by apply H_jobs_come_from_arrival_sequence with t; apply/eqP. }
          case TSK: (job_task s == tsk); last first.
          { have ZERO: service_at sched j t = 0.
            { rewrite /service_at /scheduled_at SCHEDt.
              apply/eqP; rewrite eqb0; apply/negP.
              intros FALSE; move: FALSE => /eqP FALSE; inversion FALSE; subst s.
                by move: TSK => /eqP TSK; apply TSK.
            } 
            rewrite ZERO; clear ZERO.
            have ZERO: \sum_(i <- arrivals_between t1 (t1 + A + ε) | job_task i == tsk) service_at sched i t = 0.
            { rewrite /service_at /scheduled_at SCHEDt.
              apply big1; move => k /eqP TSK2.
              apply/eqP; rewrite eqb0; apply/negP.
              intros FALSE; move: FALSE => /eqP FALSE; inversion FALSE; subst s.
                by move: TSK => /eqP TSK; apply TSK.
            }
            rewrite ZERO; clear ZERO.
            rewrite addn0 add0n.
            rewrite /task_interference_received_before /task_scheduled_at /ScheduleOfTask.task_scheduled_at.
            rewrite SCHEDt TSK; simpl.
            case INT: (interference j t); last by done.
            rewrite lt0b. 
            apply/hasP; exists j; last by done.
            rewrite /arrivals_of_task_before mem_filter; apply/andP; split.
            - by rewrite /is_job_of_task H_job_of_tsk.
            - move: (H_busy_interval) => [[/andP [_ LT] [_ _]] _].
                by eapply arrived_between_implies_in_arrivals; eauto.
          }
          { rewrite /task_interference_received_before /task_scheduled_at /ScheduleOfTask.task_scheduled_at SCHEDt TSK.
            simpl; rewrite addn0.
            case EQ: (j == s).
            { move: EQ => /eqP EQ; subst s.
              move: (H_work_conserving j t1 t2 t H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval) => WORK.
              feed WORK.
              { by move: NEQ => /andP [NEQ1 NEQ2]; apply/andP; split; last apply ltn_trans with y. }
              move: WORK => [_ ZIJT].
              feed ZIJT; first by rewrite  /scheduled_at SCHEDt.
              move: ZIJT => /negP /eqP; rewrite eqb_negLR; simpl; move => /eqP ZIJT.
              rewrite ZIJT; simpl; rewrite add0n.
                by done.
            }  
            { have NSCHED: scheduled_at sched j t = false.
              { apply/negP; intros SCHED.
                move: SCHEDt => /eqP SCHEDt.
                move: (only_one_job_scheduled sched j s t SCHED SCHEDt) => EQjs.
                  by rewrite EQjs eq_refl in EQ.
              }
              rewrite /service_at NSCHED.
              have IJT: interference j t = true.
              { have NEQT: t1 <= t < t2.
                { move: NEQ => /andP [NEQ1 NEQ2].
                  apply/andP; split; first by done.
                    by apply ltn_trans with y.
                } 
                move: (H_work_conserving j t1 t2 t H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval NEQT) => [Hn _].
                apply/negPn/negP; intros CONTR; move: CONTR => /negP CONTR.
                  by apply Hn in CONTR; rewrite NSCHED in CONTR.
              }
              rewrite IJT; clear IJT.
              simpl. rewrite addn0.
              rewrite big_mkcond; apply/sum_seq_gt0P.
              exists s; split.
              { intros. have ARR:= arrives_after_beginning_of_busy_interval j s _ _ _ _ _ t1 t2 _ t.
                feed_n 8 ARR; try done.
                { by move: TSK => /eqP TSK; rewrite TSK. } 
                { by move: NEQ => /andP [T1 T2]. }
                { by move: SCHEDt => /eqP SCHEDt; apply scheduled_implies_pending. }
                case ARRNEQ: (job_arrival s <= job_arrival j).
                { move: ARR => /andP [РР _].
                  unfold arrivals_between in *.
                  eapply arrived_between_implies_in_arrivals; eauto 2.
                  apply/andP; split; first by done.
                  rewrite /A subnKC.
                  rewrite addn1 ltnS. by done.
                    by move: (H_busy_interval) => [[/andP [BUS _] _] _].
                }
                { exfalso.
                  apply negbT in ARRNEQ; rewrite -ltnNge in ARRNEQ.
                  move: (H_sequential_jobs j s t) => CONTR.
                  feed_n 3 CONTR; try done.
                  { by rewrite -H_job_of_tsk in TSK; rewrite eq_sym. }
                  { by move: SCHEDt => /eqP SCHEDt. }
                  move: H_job_j_is_not_completed => /negP H; apply: H.
                  apply completion_monotonic with t; try done.
                  apply ltnW.
                    by move: NEQ => /andP [_ NEQ]. 
                }
              }
              { move: TSK => /eqP TSK.
                  by rewrite TSK eq_refl /service_at /scheduled_at SCHEDt eq_refl.
              }
            }
          } 
        Qed.
        
        (* However, in order to obtain a more convenient bound of the cumulative interference, 
           we need to abandon the actual workload in favor of a bound which depends on task parameters only.
           So, we show that actual workload of the task excluding workload of any job j is no greater than
           bound of workload excluding the cost of job j's task. *)
        Lemma task_rbf_excl_tsk_bounds_task_workload_excl_j:
          task_workload_between t1 (t1 + A + ε) - job_cost j <= task_rbf (A + ε) - task_cost tsk.
        Proof.
          unfold cost_of_jobs_from_arrival_sequence_le_task_cost, job_cost_le_task_cost in *. 
          move: H_j_arrives H_job_of_tsk => ARR TSK.
          move: (H_busy_interval) => [[/andP [JAGET1 JALTT2] _] _].
          apply leq_trans with (
                              task_cost tsk *
                              num_arrivals_of_task job_task arr_seq tsk t1 (t1 + A + ε) - task_cost tsk); last first.
          { rewrite leq_sub2r //.
            rewrite leq_mul2l; apply/orP; right.
            rewrite -addnA -{2}[(A+1)](addKn t1).
            move: (H_family_of_proper_arrival_curves tsk H_tsk_in_ts) => [ARRB T].
              by apply ARRB; last rewrite leq_addr.
          }    
          { have Fact6: j \in arrivals_between (t1 + A) (t1 + A + ε).
            { apply (arrived_between_implies_in_arrivals job_arrival); try(done).
              apply/andP; split; rewrite /A subnKC //.
                by rewrite addn1 ltnSn //.
            } 
            have Fact1: num_arrivals_of_task job_task arr_seq tsk (t1 + A) (t1 + A + ε) >= 1.
            { rewrite /num_arrivals_of_task /arrivals_of_task_between.
              rewrite -count_filter_fun -has_count; apply/hasP.
                by exists j; last rewrite /is_job_of_task TSK.
            }
            have Fact2: job_cost j <= task_workload_between (t1 + A) (t1 + A + ε).
            { rewrite /task_workload_between /Workload.task_workload_between /task_workload
                      /workload_of_jobs /arrivals_between (big_rem j) //=.
                by rewrite TSK eq_refl leq_addr.
            }
            have Fact3: 0 < task_cost tsk. 
            { apply leq_trans with (job_cost j); [ |rewrite -H_job_of_tsk]; auto. }
            have Fact4: j \in jobs_arriving_at arr_seq (t1 + A).
            { move: ARR => [t ARR]; rewrite subnKC //.
                by feed (H_arrival_times_are_consistent j t); try (subst t).
            }
            rewrite (@num_arrivals_of_task_cat _ _ _ _ _ (t1 + A)); last by apply/andP; split; rewrite leq_addr //.
            rewrite mulnDr.
            have Step1:
              task_workload_between t1 (t1 + A + ε) = task_workload_between t1 (t1 + A) + task_workload_between (t1 + A) (t1 + A + ε).
            { by apply workload_of_jobs_cat; apply/andP; split; rewrite leq_addr. }
            rewrite Step1; clear Step1.
            rewrite -!addnBA; first last.
            { by apply leq_trans with (job_cost j). }
            { apply leq_trans with (task_cost tsk); first by done.
                by rewrite -{1}[task_cost tsk]muln1 leq_mul2l; apply/orP; right. }
            rewrite leq_add; first by done.
            { rewrite // /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
              rewrite /task_workload_between /Workload.task_workload_between /task_workload /workload_of_jobs.
              rewrite /is_job_of_task -TSK muln1.
              apply leq_sum_seq; move => j0 IN0 /eqP EQ.
                by rewrite -EQ; apply in_arrivals_implies_arrived in IN0; auto.
            }
            { unfold task_workload_between, Workload.task_workload_between,
                 task_workload, workload_of_jobs, arrivals_between, jobs_arrived_between. 
              rewrite {1}addn1 big_nat1.
              rewrite /num_arrivals_of_task /arrivals_of_task_between /jobs_arrived_between addn1 big_nat1.
              rewrite (big_rem j) //=  TSK !eq_refl; simpl.
              rewrite addnC -addnBA; last by done.
              rewrite subnn addn0.
              rewrite (filter_size_rem _ j); [ | by done | by rewrite /is_job_of_task TSK].
              rewrite mulnDr mulnC muln1 -addnBA; last by done.
              rewrite subnn addn0.
              rewrite mulnC.
              apply sum_majorant_constant.
              move => j' ARR' /eqP TSK2.
              unfold job_cost_le_task_cost in *.
              have ARR2: arrives_in arr_seq j'.
              { by exists (t1 + A); apply rem_in in ARR'. }
                by rewrite -TSK2; auto.
            } 
          }
        Qed.
        
        (* Now we can use two lemmas above to get the following bound: *)
        Lemma bound_for_cumulative_job_interference:
          cumul_interference j t1 (t1 + x) 
            <= (task_rbf (A + ε) - task_cost tsk) + cumul_task_interference t2 t1 (t1 + x).
        Proof.
          set (y := t1 + x) in *.
          have IN: j \in arrivals_between t1 (t1 + A + ε).
          { eapply arrived_between_implies_in_arrivals; eauto 2.
            move: (H_busy_interval) => [[/andP [GE _] _] _].
              by apply/andP; split; last rewrite /A subnKC // addn1.
          }
          apply leq_trans with (task_workload_between t1 (t1+A+ε) - job_cost j + cumul_task_interference t2 t1 y).
          - by apply bound_for_cumulative_job_interference_actual.
          - rewrite leq_add2r.
            eapply task_rbf_excl_tsk_bounds_task_workload_excl_j; eauto 2.
        Qed.
        
      End BoundOfCumulativeJobInterference. 

      (* In this section, we prove that [H_R_is_maximum_seq] implies [H_R_is_maximum]. *)
      Section MaxInSeqHypothesisImpMaxInNonseqHypothesis.

        (* Consider any job j of tsk. *)
        Variable j: Job.
        Hypothesis H_j_arrives: arrives_in arr_seq j.
        Hypothesis H_job_of_tsk: job_task j = tsk.

        (* For simplicity, let's define a local name for the search space. *)
        Let is_in_search_space A :=
          is_in_search_space tsk L total_interference_bound A.
        
        (* We prove that [H_R_is_maximum] holds. *)
        Lemma max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis:
          forall A,
            is_in_search_space A ->
            exists F,
              A + F = task_lock_in_service tsk +
                      (task_rbf (A + ε) - task_cost tsk + task_interference_bound_function tsk A (A + F)) /\
              F + (task_cost tsk - task_lock_in_service tsk) <= R.
        Proof.
          move: H_proper_job_lock_in_service => [PRJ1 [PRJ2 PRJ3]].
          move: H_proper_task_lock_in_service => [PRT1 PRT2].
          intros A INSP.
          clear H_sequential_jobs H_interference_and_workload_consistent_with_sequential_jobs.  
          move: (H_R_is_maximum_seq _ INSP) => [F [FIX LE]].
          exists F; split; last by done. 
          rewrite {1}FIX.
          apply/eqP.
          rewrite addnA eqn_add2r.
          rewrite addnBA; last first.
          { apply leq_trans with (task_rbf 1).
            eapply rbf.RBF.task_rbf_1_ge_task_cost; eauto 2. 
              eapply rbf.RBF.task_rbf_monotone; eauto 2.
                by rewrite addn1. }                   
            by rewrite subnBA; auto; rewrite addnC.
        Qed.
        
      End MaxInSeqHypothesisImpMaxInNonseqHypothesis. 

      (* Finally, we apply the [uniprocessor_response_time_bound] theorem, and using the 
         lemmas above, we prove that all the requirements are satisfied. So, R is a response
         time bound. *) 
      Theorem uniprocessor_response_time_bound_seq:
        response_time_bounded_by tsk R. 
      Proof.
        intros j ARR TSK.
        eapply uniprocessor_response_time_bound with
            (interference_bound_function := fun tsk A R => task_rbf (A + ε) - task_cost tsk + task_interference_bound_function tsk A R)
            (interfering_workload0 := interfering_workload); eauto 2.
        { clear ARR TSK H_R_is_maximum_seq R j.
          intros t1 t2 R j BUSY NEQ ARR TSK COMPL.
          move: (posnP (job_cost j)) => [ZERO|POS].
          { exfalso.
            move: COMPL => /negP COMPL; apply: COMPL.
            by rewrite /is_response_time_bound_of_job /completed_by ZERO.
          }            
          set (A := job_arrival j - t1) in *.
          apply leq_trans with
              (task_rbf (A + ε) - task_cost tsk + cumul_task_interference t2 t1 (t1 + R)).
          - by eapply bound_for_cumulative_job_interference; eauto 2.
          - by rewrite leq_add2l; apply H_task_interference_is_bounded.
        }
        { by eapply max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis; eauto. }
      Qed. 

    End ResponseTimeBound. 
    
  End Sequential_Abstract_RTA. 
  
End AbstractSeqRTA.
 