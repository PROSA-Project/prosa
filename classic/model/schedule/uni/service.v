Require Import prosa.classic.util.all.
Require Import prosa.classic.model.time prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.schedule prosa.classic.model.schedule.uni.workload.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Service.

  Import UniprocessorSchedule Priority Workload.

  (* In this section, we define the more general notion of service received by sets of jobs. *)
  Section ServiceOverSets.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* Let jobs denote any (finite) set of jobs. *)
    Variable jobs: seq Job. 

    Section Definitions.

      (* First, we define the service received by a generic set of jobs. *)
      Section ServiceOfJobs.

        (* Then, given any predicate over jobs, ...*)
        Variable P: Job -> bool.

        (* ...we define the cumulative service received during [t1, t2)
           by the jobs that satisfy this predicate. *)
        Definition service_of_jobs (t1 t2: time) :=
          \sum_(j <- jobs | P j) service_during sched j t1 t2.

      End ServiceOfJobs.

      (* Next, we define the service received by tasks with higher-or-equal
         priority under a given FP policy. *)
      Section PerTaskPriority.

        Context {Task: eqType}.
        Variable job_task: Job -> Task.

        (* Consider any FP policy. *)
        Variable higher_eq_priority: FP_policy Task.

        (* Let tsk be the task to be analyzed. *)
        Variable tsk: Task.

        (* Based on the definition of jobs of higher or equal priority (with respect to tsk), ... *)
        Let of_higher_or_equal_priority j := higher_eq_priority (job_task j) tsk.
        
        (* ...we define the service received during [t1, t2) by jobs of higher or equal priority. *)
        Definition service_of_higher_or_equal_priority_tasks (t1 t2: time) :=
          service_of_jobs of_higher_or_equal_priority t1 t2.

      End PerTaskPriority.
      
      (* Next, we define the service received by jobs with higher or equal priority
         under JLFP policies. *)
      Section PerJobPriority.

        (* Consider any JLDP policy. *)
        Variable higher_eq_priority: JLFP_policy Job.

        (* Let j be the job to be analyzed. *)
        Variable j: Job.

        (* Based on the definition of jobs of higher or equal priority, ... *)
        Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
       
        (* ...we define the service received during [t1, t2) by jobs of higher or equal priority. *)
        Definition service_of_higher_or_equal_priority_jobs (t1 t2: time) :=
          service_of_jobs of_higher_or_equal_priority t1 t2.

      End PerJobPriority.

    End Definitions.

    Section Lemmas.

      (* Let P be any predicate over jobs. *)
      Variable P: Job -> bool.

      (* In this section, we prove that the service received by any set of jobs
         is upper-bounded by the corresponding workload. *)
      Section ServiceBoundedByWorkload.

        (* Recall the definition of workload. *)
        Let workload_of := workload_of_jobs job_cost.

        (* Assume that jobs do not execute after completion.*)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
        
        (* Then, we prove that the service received by those jobs is no larger than their workload. *)
        Lemma service_of_jobs_le_workload:
          forall t1 t2,
            service_of_jobs P t1 t2 <= workload_of jobs P.
        Proof.
          intros t1 t2.
          apply leq_sum; intros j _.
          by apply cumulative_service_le_job_cost.
        Qed.

      End ServiceBoundedByWorkload.

      (* In this section, we prove that the service received by any set of jobs
         is upper-bounded by the corresponding interval length. *)
      Section ServiceBoundedByIntervalLength.

        (* Assume that jobs do not execute after completion.*)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.

        (* Assume that the sequence of jobs is a set. *)
        Hypothesis H_no_duplicate_jobs: uniq jobs.
        
        (* Then, we prove that the service received by those jobs is no larger than their workload. *)
        Lemma service_of_jobs_le_delta:
          forall t1 t2,
            service_of_jobs P t1 t2 <= t2 - t1.
        Proof.
          unfold service_of_jobs; intros t1 t2.
          rewrite exchange_big /=.
          apply leq_trans with (n := \sum_(t1 <= t < t2) 1); last by simpl_sum_const.
          apply leq_sum; intros t _; rewrite /service_at.
          case (boolP (has (fun j => P j && scheduled_at sched j t) jobs)) => [HAS | ALL].
          {
            move: HAS => /hasP [j0 IN0 /andP [PRED0 SCHED0]].
            rewrite big_mkcond (bigD1_seq j0) //= PRED0 SCHED0 big1 //.
            intros j1 NEQ; case: ifP => PRED1; last by done.
            apply/eqP; rewrite eqb0; apply/negP; intro SCHED1.
            apply only_one_job_scheduled with (j2 := j1) in SCHED0; last by done.
            by rewrite SCHED0 eq_refl in NEQ.
          }
          {
            rewrite -all_predC in ALL; move: ALL => /allP ALL.
            rewrite big_seq_cond big1 //.
            move => j0 /andP [IN0 PRED0]; apply/eqP; rewrite eqb0.
            by specialize (ALL j0 IN0); rewrite /= PRED0 /= in ALL.
          }
        Qed.

      End ServiceBoundedByIntervalLength.

    End Lemmas.
      
  End ServiceOverSets.

  (* In this section, we introduce some auxiliary definitions about the service. *)
  Section ExtraDefinitions.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: Task.
    
    (* Recall the notion of a job of task tsk. *)
    Let of_task_tsk j := job_task j == tsk.
    
    (* We define the cumulative task service received by the jobs from the task
       that arrives in interval [ta1, ta2) within time interval [t1, t2). *)
    Definition task_service_of_jobs_received_in ta1 ta2 t1 t2 :=
      service_of_jobs sched (jobs_arrived_between arr_seq ta1 ta2) of_task_tsk t1 t2.

    (* For simplicity, let's define a shorter version of task service 
       for jobs that arrive and execute in the same interval [t1, t2). *)
    Definition task_service_between t1 t2 := task_service_of_jobs_received_in t1 t2 t1 t2.
      
  End ExtraDefinitions.
    
  (* In this section, we prove some auxiliary lemmas about the service. *)
  Section ExtraLemmas.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Consider any arrival sequence with consistent, non-duplicate arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.

    (* ... where jobs do not execute before their arrival or after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* For simplicity, let's define some local names. *)
    Let job_completed_by := completed_by job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    
    (* First, we prove that service is monotonic. *)
    Lemma service_monotonic:
      forall j t1 t2,
        t1 <= t2 ->
        service sched j t1 <= service sched j t2.
    Proof.
      intros.
      rewrite /service /service_during [X in _ <= X](@big_cat_nat _ _ _ t1) //.
        by rewrite leq_addr.
    Qed.
    
    (* Next, we prove that service during can be splited into two parts. *)
    Lemma service_during_cat:
      forall j t t1 t2,
        t1 <= t <= t2 -> 
        service_during sched j t1 t2 =
        service_during sched j t1 t + service_during sched j t t2.
    Proof.
      move => j' t t1 t2 /andP [GE LE].
        by rewrite /service_during (@ big_cat_nat _ _ _ t).
    Qed.
    
    (* We prove that if in some time interval [t1,t2) a job j receives k units of service, then
       there exists time instant t in [t1,t2) such that job is scheduled at time t and 
       service of job j within interval [t1,t) is equal to k. *)
    Lemma incremental_service_during:
      forall j t1 t2 k,
        service_during sched j t1 t2 > k ->
        exists t, t1 <= t < t2 /\ scheduled_at sched j t /\ service_during sched j t1 t = k.
    Proof.
      intros j t1 t2 k SERV.
      have LE: t1 <= t2.
      { rewrite leqNgt; apply/negP; intros CONTR.
        apply ltnW in CONTR.
          by move: SERV; rewrite /service_during big_geq.
      }
      induction k.
      { case SCHED: (scheduled_at sched j t1).
        { exists t1; repeat split; try done.
          - apply/andP; split; first by done.
            rewrite ltnNge; apply/negP; intros CONTR.
              by move: SERV; rewrite/service_during big_geq.
          - by rewrite /service_during big_geq.                
        }  
        { apply negbT in SCHED.
          move: SERV; rewrite /service /service_during; move => /sum_seq_gt0P [t [IN SCHEDt]].
          rewrite lt0b in SCHEDt.
          rewrite mem_iota subnKC in IN; last by done.
          move: IN => /andP [IN1 IN2].
          move: (exists_first_intermediate_point
                   ((fun t => scheduled_at sched j t)) t1 t IN1 SCHED SCHEDt)
          => [x [/andP [H1 H4] [H2 H3]]].
          exists x; repeat split; try done.
          - apply/andP; split; first by apply ltnW.
              by apply leq_ltn_trans with t. 
          - apply/eqP; rewrite big_nat_cond big1 //.
            move => y /andP [H5 _].
              by apply/eqP; rewrite eqb0; apply H2.
        }
      }  
      { feed IHk; first by apply ltn_trans with k.+1.
        move: IHk => [t [/andP [NEQ1 NEQ2] [SCHEDt SERVk]]].
        have SERVk1: service_during sched j t1 t.+1 = k.+1.
        { rewrite (service_during_cat _ t).
          rewrite  SERVk -[X in _ = X]addn1. apply/eqP; rewrite eqn_add2l. 
          rewrite /service_during big_nat1. 
          rewrite /service_at SCHEDt. by simpl.
            by apply/andP; split.
        } 
        move: SERV; rewrite (service_during_cat _ t.+1); last first.
        { by apply/andP; split; first apply leq_trans with t. }
        rewrite SERVk1 -addn1 leq_add2l; move => SERV.
        case SCHED: (scheduled_at sched j t.+1).
        { exists t.+1; repeat split; try done.
          apply/andP; split.
          - apply leq_trans with t; by done. 
          - rewrite ltnNge; apply/negP; intros CONTR.
              by move: SERV; rewrite /service_during big_geq. 
        } 
        { apply negbT in SCHED.
          move: SERV; rewrite /service /service_during; move => /sum_seq_gt0P [x [INx SCHEDx]].
          rewrite lt0b in SCHEDx.
          rewrite mem_iota subnKC in INx; last by done.
          move: INx => /andP [INx1 INx2].
          move: (exists_first_intermediate_point
                   ((fun t => scheduled_at sched j t)) t.+1 x INx1 SCHED SCHEDx) => [y [/andP [H1 H4] [H2 H3]]].
          exists y; repeat split; try done.
          - apply/andP; split.
            apply leq_trans with t; first by done. 
            apply ltnW, ltn_trans with t.+1; by done.
              by apply leq_ltn_trans with x. 
          - rewrite (@big_cat_nat _ _ _ t.+1) //=; [ | by apply leq_trans with t | by apply ltn_trans with t.+1].
            unfold service_during in SERVk1; rewrite SERVk1.
            apply/eqP.
            rewrite -{2}[k.+1]addn0 eqn_add2l.
            rewrite big_nat_cond big1 //.
            move => z /andP [H5 _].
              by apply/eqP; rewrite eqb0; apply H2.
        }
      } 
    Qed.
    
    (* We prove that the overall service of jobs at each time instant is at most 1. *)
    Lemma service_of_jobs_le_1:
      forall (t1 t2 t: time) (P: Job -> bool),
        \sum_(j <- arrivals_between t1 t2 | P j) service_at sched j t <= 1.
    Proof.
      intros t1 t2 t P.
      case SCHED: (sched t) => [j | ]; simpl.
      { case ARR: (j \in arrivals_between t1 t2).
        { rewrite (big_rem j) //=; simpl.
          rewrite /service_at /scheduled_at SCHED; simpl.
          rewrite -[1]addn0 leq_add //.
          - by rewrite eq_refl; case (P j).
          - rewrite leqn0 big1_seq; first by done.
            move => j' /andP [_ ARRj'].
            apply/eqP; rewrite eqb0.
            apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
            inversion CONTR; subst j'; clear CONTR.
            rewrite rem_filter in ARRj'; last first.
            eapply arrivals_uniq; eauto 2.
            move: ARRj'; rewrite mem_filter; move => /andP [/negP CONTR _].
              by apply: CONTR.
        }
        { apply leq_trans with 0; last by done.
          rewrite leqn0 big1_seq; first by done.
          move => j' /andP [_ ARRj'].
          apply/eqP; rewrite eqb0.
          rewrite /scheduled_at SCHED.
          apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
          inversion CONTR; clear CONTR.
            by subst j'; rewrite ARR in ARRj'.
        }
      }                    
      { apply leq_trans with 0; last by done.
        rewrite leqn0 big1_seq; first by done.
        move => j' /andP [_ ARRj'].
          by rewrite /service_at /scheduled_at SCHED.
      }
    Qed.

    (* We prove that the overall service of jobs within 
       some time interval [t, t + Δ) is at most Δ. *)
    Lemma total_service_of_jobs_le_delta:  
      forall (t Δ: time) (P: Job -> bool),
        \sum_(j <- arrivals_between t (t + Δ) | P j)
         service_during sched j t (t + Δ) <= Δ.
    Proof.
      intros.
      have EQ: \sum_(t <= x < t + Δ) 1 = Δ.
      { by rewrite big_const_nat iter_addn mul1n addn0 -{2}[t]addn0 subnDl subn0. } 
      rewrite -{3}EQ; clear EQ.
      rewrite exchange_big //=.
      rewrite leq_sum //.
      move => t' _.
        by apply service_of_jobs_le_1.
    Qed.

    (* Next we prove that total service that is lower than the 
       range implies the existence of an idle time instant. *)
    Lemma low_service_implies_existence_of_idle_time :
      forall t1 t2,
        t1 <= t2 ->
        service_of_jobs sched (arrivals_between 0 t2) predT t1 t2 < t2 - t1 ->
        exists t, t1 <= t < t2 /\ is_idle sched t.
    Proof.
      intros ? ? LE SERV.
      have EX: exists δ, t2 = t1 + δ.
      { by exists (t2 - t1); rewrite subnKC // ltnW. }
      move: EX => [δ EQ]; subst t2; clear LE.
      rewrite {3}[t1 + δ]addnC -addnBA // subnn addn0 in SERV.
      rewrite /service_of_jobs exchange_big //= in SERV.
      apply sum_le_summation_range in SERV.
      move: SERV => [x [/andP [GEx LEx] L]].
      exists x; split; first by apply/andP; split.
      apply/negPn; apply/negP; intros NIDLE.
      unfold is_idle in NIDLE.
      destruct(sched x) eqn:SCHED; last by done.
      move: SCHED => /eqP SCHED; clear NIDLE.
      move: L => /eqP; rewrite -sum_nat_eq0_nat; move => /allP L.
      specialize (L s); feed L. 
      { unfold arrivals_between.
        eapply arrived_between_implies_in_arrivals; eauto 2.
        apply/andP; split; first by done.
        apply H_jobs_must_arrive_to_execute in SCHED.
          by apply leq_ltn_trans with x.
      } 
        by move: L; simpl; rewrite /service_at /scheduled_at SCHED eqb0; move => /eqP EQ.
    Qed.

    (* In this section we prove a few facts about splitting 
       the total service of a set of jobs. *)
    Section ServiceCat.
      
      (* We show that the total service of jobs released in a time interval [t1,t2) during [t1,t2)
         is equal to the sum of:
         (1) the total service of jobs released in time interval [t1, t) during time [t1, t)
         (2) the total service of jobs released in time interval [t1, t) during time [t, t2)
         and (3) the total service of jobs released in time interval [t, t2) during time [t, t2). *)
      Lemma service_of_jobs_cat_scheduling_interval :
        forall P t1 t2 t,
          t1 <= t <= t2 -> 
          service_of_jobs sched (arrivals_between t1 t2) P t1 t2
          = service_of_jobs sched (arrivals_between t1 t) P t1 t
            + service_of_jobs sched (arrivals_between t1 t) P t t2
            + service_of_jobs sched (arrivals_between t t2) P t t2. 
      Proof.
        move => P t1 t2 t /andP [GEt LEt].
        rewrite /arrivals_between (job_arrived_between_cat _ _ t) //.
        rewrite {1}/service_of_jobs big_cat //=.
        rewrite exchange_big //= (@big_cat_nat _ _ _ t) //=;
                rewrite [in X in X + _ + _]exchange_big //= [in X in _ + X + _]exchange_big //=.
        apply/eqP; rewrite -!addnA eqn_add2l eqn_add2l.
        rewrite exchange_big //= (@big_cat_nat _ _ _ t) //= [in X in _ + X]exchange_big //=.
        rewrite -[service_of_jobs _ _ _ _ _]add0n /service_of_jobs eqn_add2r.
        rewrite big_nat_cond big1 //.
        move => x /andP [/andP [GEi LTi] _].
        rewrite big_seq_cond big1 //.
        move => s /andP [ARR Ps].
        rewrite /service_at /scheduled_at.
        apply/eqP; rewrite eqb0; apply/negP; intros SCHED.
        apply H_jobs_must_arrive_to_execute in SCHED.
        eapply in_arrivals_implies_arrived_between in ARR; eauto 2.
        move: SCHED; rewrite /has_arrived leqNgt; move => /negP CONTR; apply: CONTR.
        move: ARR => /andP [ARR1 ARR2].
          by apply leq_trans with t.
      Qed.

      (* We show that the total service of jobs released in a time interval [t1,t2) during [t,t2)
         is equal to the sum of: 
         (1) the total service of jobs released in a time interval [t1,t) during [t,t2)
         and (2) the total service of jobs released in a time interval [t,t2) during [t,t2). *)
      Lemma service_of_jobs_cat_arrival_interval :
        forall P t1 t2 t,
          t1 <= t <= t2 ->
          service_of_jobs sched (arrivals_between t1 t2) P t t2 = 
          service_of_jobs sched (arrivals_between t1 t) P t t2 +
          service_of_jobs sched (arrivals_between t t2) P t t2.
      Proof.
        move => P t1 t2 t /andP [GEt LEt].
        apply/eqP;rewrite eq_sym; apply/eqP.
        rewrite /arrivals_between [in X in _ = X](job_arrived_between_cat _ _ t) //.
          by rewrite {3}/service_of_jobs -big_cat //=.
      Qed.
          
    End ServiceCat.
    
    (* In this section, we introduce a connection between the cumulative 
       service, cumulative workload, and completion of jobs. *)
    Section WorkloadServiceAndCompletion. 

      (* Let P be an arbitrary predicate on jobs. *)
      Variable P: Job -> bool.
      
      (* Consider an arbitrary time interval [t1, t2). *)
      Variables t1 t2: time.
      
      (* Let jobs be a set of all jobs arrived during [t1, t2). *) 
      Let jobs := arrivals_between t1 t2.
      
      (* Next, we consider some time instant [t_compl]. *)
      Variable t_compl: time.

      (* First, we prove that the fact that the workload of [jobs] is equal to the service 
         of [jobs] implies that any job in [jobs] is completed by time t_compl. *)
      Lemma workload_eq_service_impl_all_jobs_have_completed:
        workload_of_jobs job_cost jobs P =
        service_of_jobs sched jobs P t1 t_compl -> 
        (forall j, j \in jobs -> P j -> job_completed_by j t_compl).
      Proof.
        unfold jobs.
        intros. 
        move: (H0) => ARR.
        apply (in_arrivals_implies_arrived_between job_arrival) in H0; last by done.
        move: H0 => /andP [T1 T2].
        have F1: forall a b, (a < b) || (a >= b).
        { intros.
          destruct (a < b) eqn:EQ; apply/orP.
          - by left.
          - by right; apply negbT in EQ; rewrite leqNgt.
        }
        move: (F1 t_compl t1) => /orP [LT | GT].
        { rewrite /service_of_jobs /service_during in H.
          rewrite exchange_big big_geq //= in H; last by rewrite ltnW.
          rewrite /workload_of_jobs in H.
          rewrite (big_rem j) ?H1 //= in H.
          move: H => /eqP; rewrite addn_eq0; move => /andP [CZ _].
          unfold job_completed_by, completed_by.
            by move: CZ => /eqP CZ; rewrite CZ. 
        }
        { unfold workload_of_jobs, service_of_jobs in H.
          unfold job_completed_by, completed_by.
          rewrite /service /service_during (@big_cat_nat _ _ _ t1) //=.
          rewrite (cumulative_service_before_job_arrival_zero
                     job_arrival sched _ j 0 t1) // add0n.
          rewrite <- sum_majorant_eqn with (F1 := fun j => service_during sched j t1 t_compl)
                                      (xs := arrivals_between t1 t2) (P := P); try done.
            by intros; apply cumulative_service_le_job_cost.
        } 
      Qed.

      (* And vice versa, the fact that any job in [jobs] is completed by time t_compl 
         implies that the workload of [jobs] is equal to the service of [jobs]. *)
      Lemma all_jobs_have_completed_impl_workload_eq_service:
        (forall j, j \in jobs -> P j -> job_completed_by j t_compl) ->
        workload_of_jobs job_cost jobs P =
        service_of_jobs sched jobs P t1 t_compl.
      Proof.
        unfold jobs.
        intros.      
        have F:
          forall j t,
            t <= t1 ->
            (j \in arrivals_between t1 t2) ->
            service_during sched j 0 t = 0.
        { intros j t LE ARR.
          eapply in_arrivals_implies_arrived_between in ARR; eauto 2.
          move: ARR => /andP [GE LT].
          unfold service_during.
          apply/eqP.
          rewrite big1_seq //.
          move => x /andP [_ ARR].
          eapply service_before_job_arrival_zero; eauto 2.
          move: ARR; rewrite mem_iota subn0 add0n; move => /andP [_ LTt].
          apply leq_trans with t; first by done.
            by apply leq_trans with t1.
        } 
        destruct (t_compl <= t1) eqn:EQ.
        { unfold service_of_jobs. unfold service_during.
          rewrite exchange_big //=. 
          rewrite big_geq; last by done.
          rewrite /workload_of_jobs big1_seq //. 
          move => j /andP [Pj ARR].
          move: H (H _ ARR Pj) => _ H.
          rewrite <- F with (j := j) (t := t_compl); try done.
          apply/eqP; rewrite eqn_leq; apply/andP; split.
          - by apply H.
          - by eauto 2.
        }
        apply/eqP; rewrite eqn_leq; apply/andP; split; first last.
        { by apply service_of_jobs_le_workload. }
        { unfold workload_of_jobs, service_of_jobs.
          rewrite big_seq_cond [X in _ <= X]big_seq_cond.
          rewrite leq_sum //.
          move => j /andP [ARR Pj].
          move: H (H _ ARR Pj) => _ H.
          rewrite -[service_during _ _ _ _ ]add0n.
          rewrite -(F j t1); try done.
          rewrite -(big_cat_nat) //=; last first.
          move: EQ =>/negP /negP; rewrite -ltnNge; move => EQ.
            by apply ltnW.
        }
      Qed.

      (* Using the lemmas above, we prove equivalence. *)
      Lemma all_jobs_have_completed_equiv_workload_eq_service:
        (forall j, j \in jobs -> P j -> job_completed_by j t_compl) <->
        workload_of_jobs job_cost jobs P =
        service_of_jobs sched jobs P t1 t_compl.
      Proof.
        split.
        - by apply all_jobs_have_completed_impl_workload_eq_service.
        - by apply workload_eq_service_impl_all_jobs_have_completed. 
      Qed.
      
    End WorkloadServiceAndCompletion.
    
  End ExtraLemmas.

End Service.