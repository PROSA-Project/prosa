Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.limited.schedule
               prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions
               prosa.classic.model.schedule.uni.limited.abstract_RTA.sufficient_condition_for_lock_in_service
               prosa.classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space.
 
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Abstract Response-Time Analysis *)
(** In this module, we propose the general framework for response-time analysis (RTA) 
    of uniprocessor scheduling of real-time tasks with arbitrary arrival models. *)
Module AbstractRTA. 

  Import Job UniprocessorSchedule Service ResponseTime  AbstractRTADefinitions
         AbstractRTALockInService AbstractRTAReduction. 

  (* In this section we prove that the maximum among the solutions of the response-time bound 
     recurrence is a response time bound for tsk. Note that in this section we do not rely on 
     any hypotheses about job sequentiality. *)
  Section Abstract_RTA.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.    
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any arrival sequence with consistent, non-duplicate arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.
    
    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.
     
    (* ... where jobs do not execute before their arrival nor after completion. *) 
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Assume that the job costs are no larger than the task costs. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq.
    
    (* Consider a task set ts... *)
    Variable ts: list Task.

    (* ... and a task tsk of ts that is to be analyzed. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Consider proper job lock-in service and task lock-in service functions, i.e... *)
    Variable job_lock_in_service: Job -> time.
    Variable task_lock_in_service: Task -> time.

    (* ...we assume that for all jobs in the arrival sequence the lock-in service is 
       (1) positive, (2) no bigger than the costs of the corresponding jobs, and 
       (3) a job becomes nonpreemptive after it reaches its lock-in service... *)
    Hypothesis H_proper_job_lock_in_service:
      proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service.

    (* ...and that [task_lock_in_service tsk] is (1) no bigger than tsk's cost, (2) for any
       job of task tsk job_lock_in_service is bounded by task_lock_in_service. *)
    Hypothesis H_proper_task_lock_in_service:
      proper_task_lock_in_service
        task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk.  
    
     (* Let's define some local names for clarity. *)
    Let work_conserving := work_conserving job_arrival job_cost job_task arr_seq sched tsk.
    Let busy_intervals_are_bounded_by := busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk.
    Let job_interference_is_bounded_by := job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk.
      
    (* Assume we are provided with abstract functions for interference and interfering workload. *)
    Variable interference: Job -> time -> bool.
    Variable interfering_workload: Job -> time -> time.

    (* We assume that the scheduler is work-conserving. *)
    Hypothesis H_work_conserving: work_conserving interference interfering_workload.
    
    (* For simplicity, let's define some local names. *)
    Let cumul_interference := cumul_interference interference.
    Let cumul_interfering_workload := cumul_interfering_workload interfering_workload.
    Let busy_interval := busy_interval job_arrival job_cost sched interference interfering_workload.
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    
    (* Let L be a constant which bounds any busy interval of task tsk. *)
    Variable L: time.
    Hypothesis H_busy_interval_exists: busy_intervals_are_bounded_by interference interfering_workload L.

    (* Next, assume that interference_bound_function is a bound on 
       the interference incurred by jobs of task tsk. *)
    Variable interference_bound_function: Task -> time -> time -> time.
    Hypothesis H_job_interference_is_bounded:
      job_interference_is_bounded_by interference interfering_workload interference_bound_function.

    (* For simplicity, let's define a local name for the search space. *)
    Let is_in_search_space A := is_in_search_space tsk L interference_bound_function A.

    (* Consider any value R that upper-bounds the solution of each response-time recurrence, 
       i.e., for any relative arrival time A in the search space, there exists a corresponding 
       solution F such that F + (task_cost tsk - task_lock_in_service tsk) <= R. *)
    Variable R: nat.
    Hypothesis H_R_is_maximum:
      forall A,
        is_in_search_space A -> 
        exists F,
          A + F = task_lock_in_service tsk + interference_bound_function tsk A (A + F) /\
          F + (task_cost tsk - task_lock_in_service tsk) <= R.

    (* In this section we show a detailed proof of the main theorem 
       that establishes that R is a response-time bound of task tsk. *) 
    Section ProofOfTheorem.

      (* Consider any job j of tsk. *)
      Variable j: Job. 
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.
      Hypothesis H_job_cost_positive: job_cost_positive job_cost j.
        
      (* Assume we have a busy interval [t1, t2) of job j that is bounded by L. *)
      Variable t1 t2: time.
      Hypothesis H_busy_interval: busy_interval j t1 t2.
      
      (* Let's define A as a relative arrival time of job j (with respect to time t1). *)
      Let A := job_arrival j - t1.

      (* In order to prove that R is a response-time bound of job j, we use hypothesis H_R_is_maximum. 
         Note that the relative arrival time (A) is not necessarily from the search space. However, 
         earlier we have proven that for any A there exists another A_sp from the search space that
         shares the same IBF value. Moreover, we've also shown that there exists an F_sp such that
         F_sp is a solution of the response time recurrence for parameter A_sp. Thus, despite the 
         fact that the relative arrival time may not lie in the search space, we can still use
         the assumption H_R_is_maximum. *)
      
      (* More formally, consider any A_sp and F_sp such that:.. *)
      Variable A_sp F_sp: time.
      (* (a) A_sp is less than or equal to A... *)
      Hypothesis H_A_gt_Asp: A_sp <= A.
      (* (b) interference_bound_function(A, x) is equal to interference_bound_function(A_sp, x) for all x less than L... *)
      Hypothesis H_equivalent:
        are_equivalent_at_values_less_than (interference_bound_function tsk A) (interference_bound_function tsk A_sp) L.
      (* (c) A_sp is in the search space, ... *)
      Hypothesis H_Asp_is_in_search_space: is_in_search_space A_sp.
      (* (d) A_sp + F_sp is a solution of the response time reccurence... *)
      Hypothesis H_fixpoint:
        A_sp + F_sp = task_lock_in_service tsk + interference_bound_function tsk A_sp (A_sp + F_sp).
      (* (e) and finally, F_sp + (task_last - ε) is no greater than R. *)
      Hypothesis H_R_gt_Fsp: F_sp + (task_cost tsk - task_lock_in_service tsk) <= R.
      
      (* In this section, we consider the case where the solution is so large that the value of [t1 + A_sp + F_sp] goes 
         beyond the busy interval. Although this case may be impossible in some scenarios, it can be easily proven,
         since any job that completes by the end of the busy interval remains completed. *)
      Section FixpointOutsideBusyInterval.

        (* By assumption, suppose that t2 is less than or equal to [t1 + A_sp + F_sp]. *)
        Hypothesis H_big_fixpoint_solution: t2 <= t1 + (A_sp + F_sp).

        (* Then we prove that (job_arrival j + R) is no less than t2. *)
        Lemma t2_le_arrival_plus_R:
          t2 <= job_arrival j + R.
        Proof.
          move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
          apply leq_trans with (t1 + (A_sp + F_sp)); first by done.
          apply leq_trans with (t1 + A + F_sp).
          { by rewrite !addnA leq_add2r leq_add2l. }
          rewrite /A subnKC; last by done.
          rewrite leq_add2l.
           apply leq_trans with (F_sp + (task_cost tsk - task_lock_in_service tsk)); last by done.
            by rewrite leq_addr.
        Qed.

        (* But since we know that the job is completed by the end of its busy interval, 
           we can show that job j is completed by (job arrival j + R) *)
        Lemma job_completed_by_arrival_plus_R_1:
          completed_by job_cost sched j (job_arrival j + R).
        Proof.
          move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
          apply completion_monotonic with t2; try done.
          apply t2_le_arrival_plus_R.
          eapply job_completes_within_busy_interval; eauto 2.
        Qed.

      End FixpointOutsideBusyInterval.

      (* In this section, we consider the complementary case where [t1 + A_sp + F_sp] lies inside the busy interval. *)
      Section FixpointInsideBusyInterval.

        (* So, assume that [t1 + A_sp + F_sp] is less than t2. *) 
        Hypothesis H_small_fixpoint_solution: t1 + (A_sp + F_sp) < t2.

        (* Next, let's consider two other cases: *)
        (* CASE 1: the value of the fixpoint is no less than the relative arrival time of job j. *)
        Section FixpointIsNoLessThanArrival.
          
          (* Suppose that [A_sp + F_sp] is no less than relative arrival of job j. *)
          Hypothesis H_fixpoint_is_no_less_than_relative_arrival_of_j: A <= A_sp + F_sp. 

          (* Using lemma "solution_for_A_exists" we can find a solution for response time recurrence for A. *)
          Lemma solution_for_A_exists':
            exists F,
              A_sp + F_sp = A + F /\
              F <= F_sp /\
              A + F = task_lock_in_service tsk + interference_bound_function tsk A (A + F).
          Proof.
            move: (solution_for_A_exists
                     tsk L (fun tsk A R => task_lock_in_service tsk + interference_bound_function tsk A R) A_sp F_sp) => Lemma1.
            feed_n 2 Lemma1; try done.
            { move: (H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive) => [t1' [t2' [_ [BOUND BUSY]]]].
              have EQ:= busy_interval_is_unique _ _ _ _ _ _ _ _ _ _ H_busy_interval BUSY. destruct EQ as [EQ1 EQ2].
              subst t1' t2'; clear BUSY.
                by rewrite -(ltn_add2l t1); apply leq_trans with t2. }
            specialize (Lemma1 A).
            feed_n 2 Lemma1; try done.
            - by apply/andP; split. 
            - by intros x H; apply/eqP; rewrite eqn_add2l H_equivalent.
          Qed.  

          (* To prove this lemma, we introduce two temporal notions of the last nonpreemptive region of job j 
             and an execution optimism. We use these notions only inside this proof, so we don't define them
             explicitly. Let the last nonpreemptive region of job j (last) be the difference between the cost 
             of the job and the j's lock-in service (i.e. [job_cost j - job_lock_in_service j]). We know that
             after j has reached its lock-in service, it will additionally be executed [last] units of time. 
             And let execution optimism (optimism) be the difference between the tsk's lock-in service 
             and the j's lock-in service (i.e. [task_lock_in_service - job_lock_in_service]). And optimism is 
             how much earlier job j has received its lock-in service than it could at worst. From lemma 
             j_receives_at_least_lock_in_service we know that service of j by time [t1 + (A + F) - optimism] 
             is no less than [lock_in_service j]. Hence, job j is completed by time [t1 + (A + F) - optimism + last] 
             which is smaller than [job_arrival j + R]. *)
          Lemma job_completed_by_arrival_plus_R_2:
            completed_by job_cost sched j (job_arrival j + R).
          Proof.
            move: H_proper_job_lock_in_service => [PRJ1 [PRJ2 PRJ3]].
            move: H_proper_task_lock_in_service => [PRT1 PRT2].
            have AUTO1: forall m n, n <= n + m; first by intros; rewrite leq_addr.
            set (job_cost j - job_lock_in_service j) as job_last.
            set (task_lock_in_service tsk - job_lock_in_service j) as optimism.
            move: (H_busy_interval) => [[NEQ [QT1 NTQ]] QT2].
            move: (NEQ) => /andP [GT LT]. 
            move: solution_for_A_exists' => [F [EQSUM [F2LEF1 FIX2]]].
            apply/negP; intros CONTRc.
            have Fact1: A <= interference_bound_function tsk A (A + F).
            { apply leq_trans with
                  (AbstractRTADefinitions.cumul_interference interference j t1 (t1 + (A+F))).
              { unfold AbstractRTADefinitions.cumul_interference.
                apply leq_trans with
                    (\sum_(t1 <= t < t1 + A) interference j t); last first.
                { rewrite [in X in _ <= X](@big_cat_nat _ _ _ (t1 + A)) //=; last by rewrite addnA. }
                { rewrite -{1}[A](sum_of_ones t1).
                  rewrite [in X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond.
                  rewrite leq_sum //.
                  move => t /andP [/andP [NEQ1 NEQ2] _].
                  rewrite lt0b.
                  unfold work_conserving in H_work_conserving.
                  move: (H_work_conserving j t1 t2 t) => CONS. 
                  feed_n 5 CONS; try done.
                  { apply/andP; split; first by done.
                    apply leq_trans with (t1 + A); first by done.
                      by rewrite /A subnKC // ltnW.
                  }
                  move: CONS => [CONS1 _].
                  apply/negP; intros CONTR.
                  move: (CONS1 CONTR) => SCHED; clear CONS1 CONTR.
                  apply H_jobs_must_arrive_to_execute in SCHED.
                  move: NEQ2; rewrite ltnNge; move => /negP NEQ2; apply: NEQ2.
                    by rewrite subnKC. }
              }
              { apply H_job_interference_is_bounded with t2; try done.
                 - by rewrite -EQSUM.
                - apply/negP; intros CONTR; apply: CONTRc.
                  apply completion_monotonic with (t1 + (A + F)); try done.
                  rewrite !addnA subnKC // leq_add2l.
                  apply leq_trans with F_sp; first by done.
                    by apply leq_trans with (F_sp + (task_cost tsk - task_lock_in_service tsk)).
              }
            }
            have FleTLIN: task_lock_in_service tsk <= F.
            { have Fact: forall a b c d, a + b = c + d -> b <= d -> a >= c.
              { clear; intros ? ? ? ? EQ NEQ.
                have Fact: exists k, d = b + k.
                { by exists (d - b); rewrite subnKC. }
                move: Fact => [k EQk].
                subst d; clear NEQ.
                move: EQ; rewrite [b+k]addnC addnA; move => /eqP; rewrite eqn_add2r; move => /eqP EQ.
                  by subst a; rewrite leq_addr.
              }
                by rewrite {1}addnC in FIX2; apply Fact in FIX2.
            }
            have NotTooOptimistic: optimism <= F.
            { apply leq_trans with (task_lock_in_service tsk); last by done.
                by rewrite /optimism leq_subr.
            }
            have NEQf: optimism <= F_sp.
            { by apply leq_trans with F. }
            have NEQ1: task_lock_in_service tsk <= F_sp.
            { by apply leq_trans with F. }            
            have CNEQ: t1 + (A + F - optimism) + job_last <= job_arrival j + R. 
            { apply leq_trans with (job_arrival j + (F - optimism) + job_last).
              { rewrite leq_add2r addnBA; last by (apply leq_trans with F; [done | rewrite leq_addl]).
                  by rewrite /A !addnA subnKC // addnBA. }
              { rewrite -addnA leq_add2l.
                apply leq_trans with (F_sp - optimism + job_last ); first by rewrite leq_add2r leq_sub2r. 
                apply leq_trans with (F_sp + (task_cost tsk - task_lock_in_service tsk)); last by done. 
                rewrite /optimism subnBA; last by apply PRT2.
                rewrite -subh1 //.
                rewrite /job_last.
                rewrite addnBA; last by auto.
                rewrite -subh1; last by rewrite leq_addl.
                rewrite -addnBA // subnn addn0.
                rewrite addnBA; last by auto.
                rewrite subh1; last by done.
                rewrite leq_sub2r // leq_add2l.
                  by rewrite -H_job_of_tsk; apply H_job_cost_le_task_cost.
              } 
            } 
            apply CONTRc.
            apply completion_monotonic with
                (t1 + ((A + F) - optimism) + job_last); try done.
            apply negbNE; apply/negP; intros NCOMPL. 
            have ESERV :=
              j_receives_at_least_lock_in_service
                job_arrival job_cost
                job_task arr_seq sched tsk
                interference interfering_workload
                _ j _ _ _ t1 t2 _ (job_lock_in_service j) _ ((A + F) - optimism). 
            feed_n 7 ESERV; eauto 2. 
            { rewrite {2}FIX2.
              rewrite /AbstractRTADefinitions.cumul_interference.
              rewrite -[in X in _ <= X]subh1; last by rewrite leq_subr.
              rewrite {2}/optimism. 
              rewrite subKn; last by auto.
              rewrite leq_add2l.              
              apply leq_trans with (cumul_interference j t1 (t1 + (A + F))).
              { rewrite /cumul_interference /AbstractRTADefinitions.cumul_interference;
                  rewrite [in X in _ <= X](@big_cat_nat _ _ _ (t1 + (A + F - optimism))) //=.
                  by rewrite leq_add2l leq_subr. }
              { apply H_job_interference_is_bounded with t2; try done.
                - by rewrite -EQSUM.
                - apply/negP; intros CONTR; apply: CONTRc.
                  apply completion_monotonic with (t1 + (A + F)); try done.
                  rewrite addnA subnKC // leq_add2l.
                  apply leq_trans with F_sp; first by done.
                    by apply leq_trans with (F_sp + (task_cost tsk - task_lock_in_service tsk)).
              }
            }
            move: NCOMPL => /negP NCOMPL; apply: NCOMPL. 
              by eapply job_completes_after_reaching_lock_in_service; eauto.
          Qed.
          
        End FixpointIsNoLessThanArrival.

        (* CASE 2: the value of the fixpoint is less than the relative arrival time of 
           job j (which turns out to be impossible, i.e. the solution of the responce-time 
           recurrense is always equal to or greater than the relative arrival time). *)
        Section FixpointCannotBeSmallerThanArrival.

          (* Assume that [A_sp + F_sp] is less than A. *)
          Hypothesis H_fixpoint_is_less_that_relative_arrival_of_j: A_sp + F_sp < A.

          (* Note that the relative arrival time of job j is less than L. *)
          Lemma relative_arrival_is_bounded: A < L.
          Proof.
            rewrite /A.
            move: (H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive) => [t1' [t2' [_ [BOUND BUSY]]]].
            have EQ:= busy_interval_is_unique _ _ _ _ _ _ _ _ _ _ H_busy_interval BUSY. destruct EQ as [EQ1 EQ2].
            subst t1' t2'; clear BUSY.
            apply leq_trans with (t2 - t1); last by rewrite leq_subLR.
            move: (H_busy_interval)=> [[/andP [H1 H3] [_ _]] _].
              by apply ltn_sub2r; first apply leq_ltn_trans with (job_arrival j).
          Qed.                  

          (* We can use [j_receives_at_least_lock_in_service] to prove that the service 
             received by j by time [t1 + (A_sp + F_sp)] is no less than lock_in_service. *)
          Lemma service_of_job_ge_lock_in_service:
            service sched j (t1 + (A_sp + F_sp)) >= job_lock_in_service j.
          Proof.
            move: H_proper_job_lock_in_service => [PRJ1 [PRJ2 PRJ3]].
            move: H_proper_task_lock_in_service => [PRT1 PRT2].
            move: (H_busy_interval) => [[NEQ [QT1 NTQ]] QT2].
            move: (NEQ) => /andP [GT LT]. 
            move: (H_job_interference_is_bounded t1 t2 (A_sp + F_sp) j) => IB. 
            feed_n 5 IB; try done.
            { apply/negP; intros COMPL.
              apply completion_monotonic with (t' := t1 + A) in COMPL; try done; last first.
              { by rewrite leq_add2l; apply ltnW. }
              { rewrite /A subnKC in COMPL; last by done.
                move: COMPL; rewrite /completed_by leqNgt; move => /negP COMPL; apply: COMPL. 
                rewrite /service (service_during_cat _ _ (job_arrival j)); last by apply/andP; split.
                rewrite /service_during (cumulative_service_before_job_arrival_zero job_arrival) // add0n.
                  by rewrite big_geq //.
              } 
            }
            rewrite -/A in IB.
            have ALTT := relative_arrival_is_bounded.
            simpl in IB; rewrite H_equivalent in IB; last by apply ltn_trans with A.
            have ESERV := j_receives_at_least_lock_in_service
                            job_arrival job_cost
                            job_task arr_seq sched tsk
                            interference interfering_workload _ j _ _ _ t1 t2 _ (job_lock_in_service j) _ (A_sp + F_sp). 
            feed_n 7 ESERV; eauto 2.
              by rewrite {2}H_fixpoint leq_add //; eapply PRT2. 
          Qed.
          
          (* However, this is a contradiction. Since job j has not yet arrived, its 
             service it equal to 0. However, lock_in_service is always positive. *)
          Lemma relative_arrival_time_is_no_less_than_fixpoint:
            False.
          Proof.
            move: H_proper_job_lock_in_service => [PRJ1 [PRJ2 PRJ3]].
                  move: H_proper_task_lock_in_service => [PRT1 PRT2].
            move: (H_busy_interval) => [[NEQ [QT1 NTQ]] QT2].
            move: (NEQ) => /andP [GT LT].                    
            have ESERV := service_of_job_ge_lock_in_service.
            move: ESERV; rewrite leqNgt; move => /negP ESERV; apply: ESERV.
            rewrite /service /service_during (cumulative_service_before_job_arrival_zero job_arrival); auto.
            rewrite -[X in _ <= X](@subnKC t1); last by done.
              by rewrite -/A leq_add2l ltnW.
          Qed.
          
        End FixpointCannotBeSmallerThanArrival.

      End FixpointInsideBusyInterval.
                                             
    End ProofOfTheorem.

    (* Using the lemmas above, we prove that R is a response-time bound. *)  
    Theorem uniprocessor_response_time_bound:
      response_time_bounded_by tsk R. 
    Proof. 
      intros j ARR JOBtsk.
      move: (posnP (job_cost j)) => [ZERO|POS].
      { by rewrite /is_response_time_bound_of_job /completed_by ZERO. } 
      move: (H_busy_interval_exists j ARR JOBtsk POS) => [t1 [t2 [NEQ [H2 BUSY]]]].
      move: (NEQ) (BUSY)=> /andP [GE LT] [_ QTt2].
      have A2LTL := relative_arrival_is_bounded _ ARR JOBtsk POS _ _ BUSY.
      set (A2 := job_arrival j - t1) in *.
      move: (representative_exists tsk _ interference_bound_function _ A2LTL) => [A1 [ALEA2 [EQΦ INSP]]].
      move: (H_R_is_maximum _ INSP) => [F1 [FIX1 LE1]].
      destruct (t1 + (A1 + F1) >= t2) eqn:BIG.
      - eapply job_completed_by_arrival_plus_R_1; eauto 2.
      - apply negbT in BIG; rewrite -ltnNge in BIG.
        destruct (A2 <= A1 + F1) eqn:BOUND. 
        + eapply job_completed_by_arrival_plus_R_2; eauto 2.
        + apply negbT in BOUND; rewrite -ltnNge in BOUND.
          exfalso; eapply relative_arrival_time_is_no_less_than_fixpoint; eauto 2.
    Qed.            

  End Abstract_RTA.  
   
End AbstractRTA.
