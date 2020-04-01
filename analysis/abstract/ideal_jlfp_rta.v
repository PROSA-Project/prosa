Require Export prosa.analysis.definitions.priority_inversion.
Require Export prosa.analysis.abstract.abstract_seq_rta.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** In this file we consider an ideal uni-processor ... *)
Require Import prosa.model.processor.ideal.

(** ... and classic model of readiness without jitter and no
    self-suspensions, where pending jobs are always ready. *)
Require Import prosa.model.readiness.basic.

(** * JLFP instantiation of Interference and Interfering Workload for ideal uni-processor. *)
(** In this module we instantiate functions Interference and Interfering Workload 
    for an arbitrary JLFP-policy that satisfies the sequential tasks hypothesis. 
    We also prove equivalence of Interference and Interfering Workload to the 
    more conventional notions of service or workload. *)
Section JLFPInstantiation.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set: arrival_sequence_uniq arr_seq. 
  
  (** Next, consider any ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume we have sequential tasks, i.e., jobs of the 
     same task execute in the order of their arrival. *)
  Hypothesis H_sequential_tasks : sequential_tasks sched.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority relation,
     and assume that this relation is reflexive and transitive. *)             
  Context `{JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities.
  Hypothesis H_priority_is_transitive : transitive_priorities.
  
  (** We also assume that the policy respects sequential tasks, meaning 
     that later-arrived jobs of a task don't have higher priority than
     earlier-arrived jobs of the same task. *)
  Hypothesis H_JLFP_respects_sequential_tasks : policy_respects_sequential_tasks.

  (** Let [tsk] be any task in ts that is to be analyzed. *)
  Variable tsk : Task.

  (** For simplicity, let's define some local names. *)
  Let job_scheduled_at := scheduled_at sched.
  Let job_completed_by := completed_by sched.
  Let arrivals_between := arrivals_between arr_seq.
  Let cumulative_task_interference := cumul_task_interference arr_seq sched.

  (** ** Interference and Interfering Workload *)
  (** In this section, we introduce definitions of interference, 
      interfering workload and a function that bounds cumulative interference. *)

  (** For proper calculation of interference and interfering workload
     of a job, we need to distinguish interference received from other
     jobs of the same task and jobs of other tasks. In that regard, we
     introduce two additional relations. The first relation defines
     whether job [j1] has a higher-than-or-equal-priority than job [j2]
     and [j1] is not equal to [j2]... *)
  Let another_hep_job: JLFP_policy Job :=
    fun j1 j2 => hep_job j1 j2 && (j1 != j2).

  (** ...and the second relation defines whether a job [j1] has a higher-or-equal-priority than 
     job [j2] and the task of [j1] is not equal to task of [j2]. *)
  Let hep_job_from_another_task: JLFP_policy Job :=
    fun j1 j2 => hep_job j1 j2 && (job_task j1 != job_task j2).

  (** In order to introduce the interference, first we need to recall the definition 
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
  Let is_priority_inversion (j : Job) (t : instant) :=
    is_priority_inversion sched j t.
  
  (** Next, we say that job j is incurring interference from another job with higher or equal 
     priority at time t, if there exists job [jhp] (different from j) with a higher or equal priority 
     that executes at time t. *)
  Definition is_interference_from_another_hep_job (j : Job) (t : instant) :=
    if sched t is Some jhp then
      another_hep_job jhp j
    else false.
  
  (** Similarly, we say that job j is incurring interference from a job with higher or 
     equal priority of another task at time t, if there exists a job [jhp] (of a different task) 
     with higher or equal priority that executes at time t. *)
  Definition is_interference_from_hep_job_from_another_task (j : Job) (t : instant) :=
    if sched t is Some jhp then
      hep_job_from_another_task jhp j
    else false.
  
  (** Now, we define the notion of cumulative interference, called
     interfering_workload_of_jobs_with_hep_priority, that says how
     many units of workload are generated by jobs with higher or equal
     priority released at time t. *)
  Definition interfering_workload_of_hep_jobs (j : Job) (t : instant) :=
    \sum_(jhp <- arrivals_at arr_seq t | another_hep_job jhp j) job_cost jhp.

  (** Instantiation of Interference *)
  (** We say that job j incurs interference at time t iff it cannot execute due to 
     a higher-or-equal-priority job being scheduled, or if it incurs a priority inversion. *)
  Definition interference (j : Job) (t : instant)  :=
    is_priority_inversion j t || is_interference_from_another_hep_job j t.
  
  (** Instantiation of Interfering Workload *)
  (** The interfering workload, in turn, is defined as the sum of the priority inversion 
     function and interfering workload of jobs with higher or equal priority. *)
  Definition interfering_workload (j : Job) (t : instant) :=
    is_priority_inversion j t + interfering_workload_of_hep_jobs j t.

  (** For each of the concepts defined above, we introduce a corresponding cumulative function: *)
  (** (a) cumulative priority inversion... *)
  Definition cumulative_priority_inversion (j : Job) (t1 t2 : instant)  :=
    \sum_(t1 <= t < t2) is_priority_inversion j t.

  (** ... (b) cumulative interference from other jobs with higher or equal priority... *)
  Let cumulative_interference_from_other_hep_jobs (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) is_interference_from_another_hep_job j t.

  (** ... (c) and cumulative interference from jobs with higher or equal priority from other tasks... *)
  Definition cumulative_interference_from_hep_jobs_from_other_tasks (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) is_interference_from_hep_job_from_another_task j t.
  
  (** ... (d) cumulative interference... *)
  Let cumulative_interference (j : Job) (t1 t2 : instant) := \sum_(t1 <= t < t2) interference j t.

  (** ... (e) cumulative workload from jobs with higher or equal priority... *)
  Let cumulative_interfering_workload_of_hep_jobs (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) interfering_workload_of_hep_jobs j t.

  (** ... (f) and cumulative interfering workload. *)
  Let cumulative_interfering_workload (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) interfering_workload j t.

  (** Instantiated functions usually do not have any useful lemmas about them. In order to
     reuse existing lemmas, we need to prove equivalence of the instantiated functions to 
     some conventional notions. The instantiations given in this file are equivalent to 
     service and workload. Further, we prove these equivalences formally. *)
  
  (** Before we present the formal proofs of the equivalences, we recall
     the notion of workload of higher or equal priority jobs. *)
  Let workload_of_other_hep_jobs (j : Job) (t1 t2 : instant) :=
    workload_of_jobs (fun jhp => another_hep_job jhp j) (arrivals_between t1 t2).

  (** Similarly, we recall notions of service of higher or equal priority jobs from other tasks... *)
  Let service_of_hep_jobs_from_other_tasks (j : Job) (t1 t2 : instant) :=
    service_of_jobs sched (fun jhp => hep_job_from_another_task jhp j)
                    (arrivals_between t1 t2) t1 t2.
  
  (** ... and service of all other jobs with higher or equal priority. *)
  Let service_of_other_hep_jobs (j : Job) (t1 t2 : instant) :=
    service_of_jobs sched (fun jhp => another_hep_job jhp j) (arrivals_between t1 t2) t1 t2.
    
  (** ** Equivalences *)
  (** In this section we prove a few equivalences between the definitions obtained by 
      instantiation of definitions from the Abstract RTA module (interference and
      interfering workload) and definitions corresponding to the conventional concepts.
      
      As it was mentioned previously, instantiated functions of interference and 
      interfering workload usually do not have any useful lemmas about them. However,
      it is possible to prove their equivalence to the more conventional notions like 
      service or workload. Next we prove the equivalence between the instantiations 
      and conventional notions. *)
  Section Equivalences.
    
    (** We prove that we can split cumulative interference into two parts: (1) cumulative priority 
       inversion and (2) cumulative interference from jobs with higher or equal priority. *)
    Lemma cumulative_interference_split:
      forall j t1 t2,
        cumulative_interference j t1 t2
        = cumulative_priority_inversion j t1 t2
          + cumulative_interference_from_other_hep_jobs j t1 t2.
    Proof.
      rewrite /cumulative_interference /interference.
      intros; rewrite -big_split //=.
      apply/eqP; rewrite eqn_leq; apply/andP; split; rewrite leq_sum; try done.
      { intros t _; unfold is_priority_inversion, priority_inversion.is_priority_inversion.
        ideal_proc_model_sched_case_analysis_eq sched t s; first by done.
        destruct (hep_job s j) eqn:MM; simpl; rewrite ?addn0 ?add0n.
        all: by move: Sched_s; rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ MM.
      }              
      { intros t _; unfold is_priority_inversion, priority_inversion.is_priority_inversion,
                    is_interference_from_another_hep_job.
        ideal_proc_model_sched_case_analysis_eq sched t s; first by done.
        unfold another_hep_job.
        destruct (hep_job s j) eqn:HP; simpl; rewrite ?addn0 ?add0n.
        all: by move: Sched_s; rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ HP.
      }
    Qed.          
    
    (** Let [j] be any job of task [tsk], and let [upp_t] be any time instant after job [j]'s arrival.
       Then for any time interval lying before [upp_t], the cumulative interference received by [tsk] 
       is equal to the sum of the cumulative priority inversion of job [j] and the cumulative interference
       incurred by task [tsk] due to other tasks. *)
    Lemma cumulative_task_interference_split: 
      forall j t1 t2 upp_t, 
        job_task j = tsk ->
        j \in arrivals_before arr_seq upp_t ->
        ~~ job_completed_by j t2 ->
        cumulative_task_interference interference tsk upp_t t1 t2 = 
        cumulative_priority_inversion j t1 t2 +
        cumulative_interference_from_hep_jobs_from_other_tasks j t1 t2.
    Proof.
      rewrite /cumulative_task_interference /cumul_task_interference.
      intros j t1 R upp TSK ARR NCOMPL.
      rewrite -big_split //= big_nat_cond [X in _ = X]big_nat_cond. 
      apply/eqP; rewrite eqn_leq; apply/andP; split.
      all: rewrite /interference /is_priority_inversion /priority_inversion.is_priority_inversion.
      - apply leq_sum; intros t _.
        rewrite /task_interference_received_before /task_schedule.task_scheduled_at
                /is_interference_from_hep_job_from_another_task
                /is_interference_from_another_hep_job /hep_job_from_another_task.
        ideal_proc_model_sched_case_analysis_eq sched t s; first by rewrite has_pred0 addn0 leqn0 eqb0. 
        destruct (hep_job s j) eqn:HP; simpl.
        1-2: move: Sched_s; rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ HP.
        + rewrite add0n TSK.
          by case: (job_task s != tsk); first rewrite Bool.andb_true_l leq_b1.
        + by rewrite addn0 leq_b1. 
      - apply leq_sum; move => t /andP [/andP [_ LT'] _].
        rewrite /is_interference_from_hep_job_from_another_task
                /hep_job_from_another_task /task_interference_received_before
                /task_schedule.task_scheduled_at.
        ideal_proc_model_sched_case_analysis_eq sched t s; first by done.
        move: (Sched_s); rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ.
        rewrite -TSK; case TSKEQ: (job_task s == job_task j); simpl. 
        + rewrite Bool.andb_false_r leqn0 addn0 eqb0.
          apply/negP; intros NEQ; move: NCOMPL => /negP NCOMPL; apply: NCOMPL.
          apply completion_monotonic with t; [ by apply ltnW | ].
          apply/negP; intros NCOMPL; move: NCOMPL => /negP NCOMPL.
          move: NEQ => /negP NEQ; apply: NEQ; apply H_JLFP_respects_sequential_tasks; eauto 2. 
            by eapply scheduler_executes_job_with_earliest_arrival; eauto 2.
        + have NEQ: s != j.
          { apply/negP; intros EQ2; move: EQ2 => /eqP EQ2.
              by move: TSKEQ => /eqP TSKEQ; apply: TSKEQ; rewrite EQ2. } 
          have Fact: forall b, ~~ b + b = true; first by intros b; destruct b.
          rewrite Bool.andb_true_r Fact; simpl; rewrite lt0b; clear Fact.
          apply/hasP; exists j.
          * rewrite mem_filter; apply/andP; split; first by done.
              by eapply arrivals_between_sub with (t2 := 0) (t3 := upp); eauto 2.
          * destruct (hep_job s j) eqn:HP; apply/orP; [right|left]; last by done.
              by rewrite /is_interference_from_another_hep_job EQ
                         /another_hep_job NEQ Bool.andb_true_r. 
    Qed.
    
    (** In this section we prove that the (abstract) cumulative interfering workload is equivalent to 
       conventional workload, i.e., the one defined with concrete schedule parameters. *)
    Section InstantiatedWorkloadEquivalence.

      (** Let <<[t1,t2)>> be any time interval. *)
      Variables t1 t2 : instant.
      
      (** Consider any job j of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.

      (** Then for any job j, the cumulative interfering workload is equal to the conventional workload. *)
      Lemma instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs:
        cumulative_interfering_workload_of_hep_jobs j t1 t2
        = workload_of_other_hep_jobs j t1 t2.
      Proof.
        intros.
        rewrite /cumulative_interfering_workload_of_hep_jobs
                /workload_of_other_hep_jobs.
        case NEQ: (t1 < t2); last first.
        { move: NEQ => /negP /negP; rewrite -leqNgt; move => NEQ.
          rewrite big_geq; last by done.
          rewrite /arrivals_between /arrival_sequence.arrivals_between big_geq; last by done.
            by rewrite /workload_of_jobs big_nil.
        }
        { unfold interfering_workload_of_hep_jobs, workload_of_jobs.
          convert_two_instants_into_instant_and_duration t1 t2 k.
          induction k.
          - rewrite !addn0.
            rewrite big_geq; last by done.
            rewrite /arrivals_between /arrival_sequence.arrivals_between big_geq; last by done.
              by rewrite /workload_of_jobs big_nil.
          - rewrite addnS big_nat_recr //=; last by rewrite leq_addr.
            rewrite IHk.
            rewrite /arrivals_between /arrival_sequence.arrivals_between big_nat_recr //=; 
                    last by rewrite leq_addr.
              by rewrite big_cat //=.
        }
      Qed.
      
    End InstantiatedWorkloadEquivalence.

    (** In order to avoid confusion, we denote the notion of a quiet
        time in the _classical_ sense as [quiet_time_cl], and the
        notion of quiet time in the _abstract_ sense as
        [quiet_time_ab]. *)
    Let quiet_time_cl := busy_interval.quiet_time arr_seq sched.
    Let quiet_time_ab := definitions.quiet_time sched interference interfering_workload.

    (** Same for the two notions of a busy interval. *)
    Let busy_interval_cl := busy_interval.busy_interval arr_seq sched.
    Let busy_interval_ab := definitions.busy_interval sched interference interfering_workload.
    
    (** In this section we prove that the (abstract) cumulative interference of jobs with higher or 
       equal priority is equal to total service of jobs with higher or equal priority. *)
    Section InstantiatedServiceEquivalences.
   
      (** Consider any job [j] of [tsk]. *)
      Variable j : Job.
      Hypothesis H_j_arrives : arrives_in arr_seq j.
      Hypothesis H_job_of_tsk : job_of_task tsk j.
      
      (** We consider an arbitrary time interval <<[t1, t)>> that starts with a quiet time. *)
      Variable t1 t : instant.
      Hypothesis H_quiet_time : quiet_time_cl j t1.

      (** Then for any job j, the (abstract) instantiated function of interference is 
         equal to the total service of jobs with higher or equal priority. *)
      Lemma instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs:
        cumulative_interference_from_other_hep_jobs j t1 t
        = service_of_other_hep_jobs j t1 t.
      Proof.
        rewrite /service_of_other_hep_jobs /service_of_jobs.
        rewrite /cumulative_interference_from_other_hep_jobs
                /is_interference_from_another_hep_job.
        rewrite exchange_big //= big_nat_cond [in X in _ = X]big_nat_cond.
        all: apply/eqP; rewrite eqn_leq; apply/andP; split.
        all: rewrite leq_sum //; move => x /andP [/andP [Ge Le] _].
        { ideal_proc_model_sched_case_analysis_eq sched x jo; first by done.
          move: (Sched_jo); rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ.
          destruct (another_hep_job jo j) eqn:PRIO; last by done.
          rewrite (big_rem jo) //=; first by rewrite PRIO eq_refl.
          apply arrived_between_implies_in_arrivals; try done.
          - by apply H_jobs_come_from_arrival_sequence with x.
          - rewrite /arrived_between; apply/andP; split.
            + move: PRIO => /andP [PRIO1 PRIO2].
              rewrite leqNgt; apply/negP; intros AB.
              move: (Sched_jo). rewrite -[scheduled_at _ _ _]Bool.negb_involutive;
                                  move => /negP SCHED2; apply: SCHED2.
              apply completed_implies_not_scheduled; eauto. 
              apply completion_monotonic with t1; try done.
              apply H_quiet_time; try done.
              eapply H_jobs_come_from_arrival_sequence; eauto.
            + by apply leq_ltn_trans with x; [apply H_jobs_must_arrive_to_execute | done].
        }
        { ideal_proc_model_sched_case_analysis_eq sched x jo; first by rewrite big1_eq.
          move: (Sched_jo); rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ.
          destruct (another_hep_job jo j) eqn:PRIO.
          - rewrite -EQ. have SCH := service_of_jobs_le_1 sched _ (arrivals_between t1 t) _ x.
            eapply leq_trans; last by apply SCH; eauto using arrivals_uniq.
            erewrite leq_sum; eauto 2.
          - rewrite leqn0 big1 //; intros joo PRIO2.
            apply/eqP; rewrite eqb0; apply/eqP; intros C.
            inversion C; subst joo; clear C.
              by rewrite PRIO2 in PRIO.
        }
      Qed.

      (** The same applies to the alternative definition of interference. *) 
      Lemma instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks:
        cumulative_interference_from_hep_jobs_from_other_tasks j t1 t
        = service_of_hep_jobs_from_other_tasks j t1 t.
      Proof.
        rewrite /service_of_hep_jobs_from_other_tasks /service_of_jobs.
        rewrite /cumulative_interference_from_hep_jobs_from_other_tasks
                /is_interference_from_hep_job_from_another_task.
        rewrite exchange_big //= big_nat_cond [in X in _ = X]big_nat_cond.
        all: apply/eqP; rewrite eqn_leq; apply/andP; split.
        all: rewrite leq_sum //; move => x /andP [/andP [Ge Le] _].
        { ideal_proc_model_sched_case_analysis_eq sched x jo; first by done.
          move: (Sched_jo); rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ.
          destruct (hep_job_from_another_task jo j) eqn:PRIO; last by done.
          rewrite (big_rem jo) //=; first by rewrite PRIO eq_refl.
          apply arrived_between_implies_in_arrivals; try done.
          - by apply H_jobs_come_from_arrival_sequence with x.
          - rewrite /arrived_between; apply/andP; split.
            + move: PRIO => /andP [PRIO1 PRIO2].
              rewrite leqNgt; apply/negP; intros AB.
              move: (Sched_jo). rewrite -[scheduled_at _ _ _]Bool.negb_involutive;
                                  move => /negP SCHED2; apply: SCHED2.
              apply completed_implies_not_scheduled; eauto. 
              apply completion_monotonic with t1; try done.
              apply H_quiet_time; try done.
              eapply H_jobs_come_from_arrival_sequence; simpl; eauto.
            + by apply leq_ltn_trans with x; [apply H_jobs_must_arrive_to_execute | done].
        }
        { ideal_proc_model_sched_case_analysis_eq sched x jo; first by rewrite big1_eq.
          move: (Sched_jo); rewrite scheduled_at_def; move => /eqP EQ; rewrite EQ.
          destruct (hep_job_from_another_task jo j) eqn:PRIO.
          - rewrite -EQ. have SCH := service_of_jobs_le_1 sched _ (arrivals_between t1 t) _ x.
            eapply leq_trans; last by apply SCH; eauto using arrivals_uniq.
            erewrite leq_sum; eauto 2.
          - rewrite leqn0 big1 //; intros joo PRIO2.
            apply/eqP; rewrite eqb0; apply/eqP; intros C.
            inversion C; subst joo; clear C.
              by rewrite PRIO2 in PRIO.
        }
      Qed.
              
      End InstantiatedServiceEquivalences.

      (** In this section we prove that the abstract definition of busy interval is equivalent to 
         the conventional, concrete definition of busy interval for JLFP scheduling. *)
      Section BusyIntervalEquivalence.

        (** Consider any job j of [tsk]. *)
        Variable j : Job.
        Hypothesis H_j_arrives : arrives_in arr_seq j.
        Hypothesis H_job_of_tsk : job_task j = tsk.
        Hypothesis H_job_cost_positive : job_cost_positive j.

        (** To show the equivalence of the notions of busy intervals
            we first show that the notions of quiet time are also
            equivalent. *)
        
        Lemma quiet_time_cl_implies_quiet_time_ab:
          forall t, quiet_time_cl j t -> quiet_time_ab j t.
        Proof.
          have zero_is_quiet_time: forall j, quiet_time_cl j 0.
          { by intros jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0. }
          intros t QT; split.
          { intros.
            have CIS := cumulative_interference_split.
            rewrite /cumulative_interference in CIS.
            rewrite /cumul_interference /cumul_interfering_workload.
            rewrite CIS !big_split //=.
            apply/eqP; rewrite eqn_add2l.
            rewrite instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs;
              last by apply zero_is_quiet_time.
            have L2 := instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs.
            rewrite /cumulative_interfering_workload_of_hep_jobs in L2; rewrite L2; clear L2.
            rewrite eq_sym; apply/eqP. 
            apply all_jobs_have_completed_equiv_workload_eq_service; try done.
            intros; apply QT.
            - by apply in_arrivals_implies_arrived in H4.
            - by move: H5 => /andP [H6 H7]. 
            - by apply in_arrivals_implies_arrived_between in H4.
          }
          { rewrite negb_and Bool.negb_involutive; apply/orP.
            case ARR: (arrived_before j t); [right | by left]. 
            apply QT; try eauto 2.
          }
        Qed.

        Lemma quiet_time_ab_implies_quiet_time_cl:
          forall t, quiet_time_ab j t -> quiet_time_cl j t.
        Proof.
          have zero_is_quiet_time: forall j, quiet_time_cl j 0.
          { by intros jhp ARR HP AB; move: AB; rewrite /arrived_before ltn0. }
          have CIS := cumulative_interference_split.
          have IC1 := instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs.
          rewrite /cumulative_interference /service_of_other_hep_jobs in CIS, IC1.
          intros t [T0 T1]; intros jhp ARR HP ARB.
          eapply all_jobs_have_completed_equiv_workload_eq_service with
              (P := fun jhp => hep_job jhp j) (t1 := 0) (t2 := t);
            eauto 2; last eapply arrived_between_implies_in_arrivals; try done.
          move: T0; rewrite /cumul_interference /cumul_interfering_workload.
          rewrite CIS !big_split //=; move => /eqP; rewrite eqn_add2l.
          rewrite IC1; last by apply zero_is_quiet_time.
          have L2 := instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs;
                       rewrite /cumulative_interfering_workload_of_hep_jobs in L2.
          rewrite L2. move => T2. apply/eqP; rewrite eq_sym.
          move: T1; rewrite negb_and Bool.negb_involutive -leqNgt; move => /orP [T1 | T1].
          - have NOTIN: j \notin arrivals_between 0 t.
            { apply/memPn; intros jo IN; apply/negP; intros EQ; move: EQ => /eqP EQ.
              subst jo.
              apply in_arrivals_implies_arrived_between in IN; try done.
                by move: IN => /andP [_ IN]; move: T1; rewrite leqNgt; move => /negP LT; apply: LT. }
            rewrite /workload_of_other_hep_jobs in T2.
              by rewrite /service_of_jobs /workload_of_jobs !sum_notin_rem_eqn in T2.
          - have JIN: j \in arrivals_between 0 t.
            { eapply completed_implies_scheduled_before in T1; eauto 2.
              apply arrived_between_implies_in_arrivals; try done.
              move: T1 => [t' [T3 _]].
              apply/andP; split; first by done.
              move: T3 => /andP [H3e H3t].
                by apply leq_ltn_trans with t'. }
            have UNIC: uniq (arrivals_between 0 t) by eapply arrivals_uniq; eauto 2. 
            unfold service_of_jobs, workload_of_jobs.
            rewrite big_mkcond //= (bigD1_seq j) //= -big_mkcondl //=.
            move: T2; rewrite /service_of_jobs; move => /eqP T2; rewrite T2.
            rewrite [X in _ == X]big_mkcond //= [X in _ == X](bigD1_seq j) //= -big_mkcondl //=.
            rewrite eqn_add2r; unfold hep_job.
            erewrite H_priority_is_reflexive; eauto 2.
            rewrite eqn_leq; apply/andP; split; try eauto 2.
              by apply service_at_most_cost; eauto with basic_facts.
        Qed.
 
        (** The equivalence trivially follows from the lemmas above. *)
        Corollary instantiated_quiet_time_equivalent_quiet_time:
          forall t,
            quiet_time_cl j t <-> quiet_time_ab j t.
        Proof.
          intros ?; split.
          - apply quiet_time_cl_implies_quiet_time_ab.
          - apply quiet_time_ab_implies_quiet_time_cl.
        Qed.
     
        (** Based on that, we prove that the concept of busy interval obtained by instantiating the abstract 
           definition of busy interval coincides with the conventional definition of busy interval. *)
        Lemma instantiated_busy_interval_equivalent_edf_busy_interval:
          forall t1 t2,
            busy_interval_cl j t1 t2 <-> busy_interval_ab j t1 t2.
        Proof.
          split.
          { move => [[NEQ [QTt1 [NQT REL]] QTt2]].
            split; [split; [ |split] | ].
            - by done.
            - by apply instantiated_quiet_time_equivalent_quiet_time in QTt1.
            - by intros t NE QT; eapply NQT; eauto 2; apply instantiated_quiet_time_equivalent_quiet_time.
            - by eapply instantiated_quiet_time_equivalent_quiet_time in QTt2.
          }
          { move => [[/andP [NEQ1 NEQ2] [QTt1 NQT] QTt2]].
            split; [split; [ | split; [ |split] ] | ].
            - by apply leq_ltn_trans with (job_arrival j).
            - by eapply instantiated_quiet_time_equivalent_quiet_time; eauto 2.
            - by intros t NEQ QT; eapply NQT; eauto 2; eapply instantiated_quiet_time_equivalent_quiet_time in QT; eauto 2.
            - by apply/andP; split.
            - by eapply instantiated_quiet_time_equivalent_quiet_time; eauto 2.
          }
        Qed.
        
      End BusyIntervalEquivalence.

  End Equivalences.

End JLFPInstantiation. 
