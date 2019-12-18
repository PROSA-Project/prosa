Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedule_of_task.
Require Import prosa.classic.model.schedule.uni.limited.busy_interval
               prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions
               prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * JLFP instantiation of Interference and Interfering Workload *)
(** In this module we instantiate functions Interference and Interfering Workload 
    for an arbitrary JLFP-policy that satisfies the sequential jobs hypothesis. 
    We also prove equivalence of Interference and Interfering Workload to the 
    more conventional notions of service or workload. *)
Module JLFPInstantiation.
  
  Import Job TaskArrival ScheduleOfTask Priority Workload Service BusyIntervalJLFP.
  
  Section Instantiation.

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

    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Assume we have sequential jobs, i.e., jobs from the 
       same task execute in the order of their arrival. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.

    (* Consider a JLFP-policy that indicates a higher-or-equal priority relation,
       and assume that this relation is reflexive and transitive. *)             
    Variable higher_eq_priority: JLFP_policy Job.
    Hypothesis H_priority_is_reflexive: JLFP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: JLFP_is_transitive higher_eq_priority.
    
    (* We also assume that the policy respects sequential jobs, meaning 
       that later-arrived jobs of a task don't have higher priority than
       earlier-arrived jobs of the same task. *)
    Hypothesis H_JLFP_respects_sequential_jobs:
      JLFP_respects_sequential_jobs
        job_task job_arrival higher_eq_priority.

    (* Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: Task.

    (* For simplicity, let's define some local names. *)
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    Let quiet_time := quiet_time job_arrival job_cost arr_seq sched higher_eq_priority.
    Let cumulative_task_interference :=
      AbstractSeqRTA.cumul_task_interference job_task arr_seq sched.

    (** ** Interference and Interfering Workload *)
    (** In this section, we introduce definitions of interference, 
        interfering workload and a function that bounds cumulative interference. *)
    
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

    (* In order to introduce the interference, first we need to recall the definition 
       of priority inversion introduced in module limited.fixed_priority.busy_interval: 
         [ Definition is_priority_inversion t := ]
         [   if sched t is Some jlp then         ]
         [     ~~ higher_eq_priority jlp j       ]
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

    (* Instantiation of Interference *)
    (* We say that job j incurs interference at time t iff it cannot execute due to 
       a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. *)
    Definition interference j t :=
      is_priority_inversion j t || is_interference_from_another_job_with_higher_eq_priority j t.

    (* Instantiation of Interfering Workload *)
    (* The interfering workload, in turn, is defined as the sum of the priority inversion 
       function and interfering workload of jobs with higher or equal priority. *)
    Definition interfering_workload j t :=
      is_priority_inversion j t + interfering_workload_of_jobs_with_hep_priority j t.

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
       some conventional notions. The instantiations given in this file are equivalent to 
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
    (** In this section we prove a few equivalences between the definitions obtained by 
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
        intros j t1 R upp TSK ARR NCOMPL.
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
            apply/negP; intros NEQ.
            move: SCHED => /eqP SCHED.
            move: NCOMPL => /negP NCOMPL; apply: NCOMPL.
            apply completion_monotonic with t; [ by apply ltnW | ].
            apply/negP; intros NCOMPL; move: NCOMPL => /negP NCOMPL.
            have ARRle := (scheduler_executes_job_with_earliest_arrival
                             job_arrival _ _ _ _  s j t TSKEQ NCOMPL SCHED).
            feed ARRle; try done.
            move: NEQ => /negP NEQ; apply: NEQ.
              by apply H_JLFP_respects_sequential_jobs.
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
                by rewrite /is_priority_inversion /BusyIntervalJLFP.is_priority_inversion SCHED HP.
            }
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
         the conventional, concrete definition of busy interval for JLFP scheduling. *)
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
                by apply H.
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
                rewrite eqn_add2r H_priority_is_reflexive.
                  by rewrite eqn_leq; apply/andP; split; try eauto 2.
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

  End Instantiation. 
  
End JLFPInstantiation. 