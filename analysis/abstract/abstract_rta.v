Require Export prosa.analysis.definitions.schedulability.
Require Export prosa.analysis.abstract.search_space.
Require Export prosa.analysis.abstract.run_to_completion.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Abstract Response-Time Analysis *)
(** In this module, we propose the general framework for response-time analysis (RTA) 
    of uni-processor scheduling of real-time tasks with arbitrary arrival models. *)
(** We prove that the maximum (with respect to the set of offsets) among the solutions
   of the response-time bound recurrence is a response time bound for [tsk]. Note that
   in this section we do not rely on any hypotheses about job sequentiality. *)
Section Abstract_RTA.
 
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskRunToCompletionThreshold Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobPreemptable Job}.

  (** Consider any kind of uni-service ideal processor state model. *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.
  Hypothesis H_ideal_progress_proc_model : ideal_progress_proc_model PState.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.  
  
  (** Consider any arrival sequence with consistent, non-duplicate arrivals... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.
  
  (** Next, consider any schedule of this arrival sequence...*)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
  
  (** ... where jobs do not execute before their arrival nor after completion. *) 
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Assume that the job costs are no larger than the task costs. *)
  Hypothesis H_valid_job_cost:
    arrivals_have_valid_job_costs arr_seq.
  
  (** Consider a task set ts... *)
  Variable ts : list Task.

  (** ... and a task [tsk] of ts that is to be analyzed. *)
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
  Let work_conserving := work_conserving arr_seq sched tsk.
  Let busy_intervals_are_bounded_by := busy_intervals_are_bounded_by arr_seq sched tsk.
  Let job_interference_is_bounded_by := job_interference_is_bounded_by arr_seq sched tsk.
  
  (** Assume we are provided with abstract functions for interference and interfering workload. *)
  Variable interference : Job -> instant -> bool.
  Variable interfering_workload : Job -> instant -> duration.

  (** We assume that the scheduler is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving interference interfering_workload.
  
  (** For simplicity, let's define some local names. *)
  Let cumul_interference := cumul_interference interference.
  Let cumul_interfering_workload := cumul_interfering_workload interfering_workload.
  Let busy_interval := busy_interval sched interference interfering_workload.
  Let response_time_bounded_by := task_response_time_bound arr_seq sched.
  
  (** Let L be a constant which bounds any busy interval of task [tsk]. *)
  Variable L : duration.
  Hypothesis H_busy_interval_exists:
    busy_intervals_are_bounded_by interference interfering_workload L.

  (** Next, assume that interference_bound_function is a bound on 
     the interference incurred by jobs of task [tsk]. *)
  Variable interference_bound_function : Task -> duration -> duration -> duration.
  Hypothesis H_job_interference_is_bounded:
    job_interference_is_bounded_by
      interference interfering_workload interference_bound_function.

  (** For simplicity, let's define a local name for the search space. *)
  Let is_in_search_space A := is_in_search_space tsk L interference_bound_function A.

  (** Consider any value [R] that upper-bounds the solution of each response-time recurrence, 
     i.e., for any relative arrival time A in the search space, there exists a corresponding 
     solution [F] such that [F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R]. *)
  Variable R: nat.
  Hypothesis H_R_is_maximum:
    forall A,
      is_in_search_space A -> 
      exists F,
        A + F = task_run_to_completion_threshold tsk
                + interference_bound_function tsk A (A + F) /\
        F + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.

  (** In this section we show a detailed proof of the main theorem 
     that establishes that R is a response-time bound of task [tsk]. *) 
  Section ProofOfTheorem.

    (** Consider any job j of [tsk] with positive cost. *)
    Variable j: Job. 
    Hypothesis H_j_arrives: arrives_in arr_seq j.
    Hypothesis H_job_of_tsk: job_task j = tsk.
    Hypothesis H_job_cost_positive: job_cost_positive j.
    
    (** Assume we have a busy interval <<[t1, t2)>> of job j that is bounded by L. *)
    Variable t1 t2: instant.
    Hypothesis H_busy_interval: busy_interval j t1 t2.
    
    (** Let's define A as a relative arrival time of job j (with respect to time t1). *)
    Let A := job_arrival j - t1.

    (** In order to prove that R is a response-time bound of job j, we use hypothesis H_R_is_maximum. 
       Note that the relative arrival time (A) is not necessarily from the search space. However, 
       earlier we have proven that for any A there exists another [A_sp] from the search space that
       shares the same IBF value. Moreover, we've also shown that there exists an [F_sp] such that
       [F_sp] is a solution of the response time recurrence for parameter [A_sp]. Thus, despite the 
       fact that the relative arrival time may not lie in the search space, we can still use
       the assumption H_R_is_maximum. *)
    
    (** More formally, consider any [A_sp] and [F_sp] such that:.. *)
    Variable A_sp F_sp : duration.
    
    (** (a) [A_sp] is less than or equal to [A]... *)
    Hypothesis H_A_gt_Asp : A_sp <= A.
    
    (** (b) [interference_bound_function(A, x)] is equal to
       [interference_bound_function(A_sp, x)] for all [x] less than [L]... *)
    Hypothesis H_equivalent :
      are_equivalent_at_values_less_than
        (interference_bound_function tsk A)
        (interference_bound_function tsk A_sp) L.
    
    (** (c) [A_sp] is in the search space, ... *)
    Hypothesis H_Asp_is_in_search_space : is_in_search_space A_sp.
   
    (** (d) [A_sp + F_sp] is a solution of the response time recurrence... *)
    Hypothesis H_Asp_Fsp_fixpoint :
      A_sp + F_sp = task_run_to_completion_threshold tsk + interference_bound_function tsk A_sp (A_sp + F_sp).

    (** (e) and finally, [F_sp + (task_last - ε)] is no greater than R. *)
    Hypothesis H_R_gt_Fsp : F_sp + (task_cost tsk - task_run_to_completion_threshold tsk) <= R.

    (** In this section, we consider the case where the solution is so large 
       that the value of [t1 + A_sp + F_sp] goes beyond the busy interval. 
       Although this case may be impossible in some scenarios, it can be 
       easily proven, since any job that completes by the end of the busy
       interval remains completed. *)
    Section FixpointOutsideBusyInterval.

      (** By assumption, suppose that t2 is less than or equal to [t1 + A_sp + F_sp]. *)
      Hypothesis H_big_fixpoint_solution : t2 <= t1 + (A_sp + F_sp).

      (** Then we prove that [job_arrival j + R] is no less than [t2]. *)
      Lemma t2_le_arrival_plus_R:
        t2 <= job_arrival j + R.
      Proof.
        move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
        apply leq_trans with (t1 + (A_sp + F_sp)); first by done.
        apply leq_trans with (t1 + A + F_sp).
        { by rewrite !addnA leq_add2r leq_add2l. }
        rewrite /A subnKC; last by done.
        rewrite leq_add2l.
          by apply leq_trans with (F_sp + (task_cost tsk - task_run_to_completion_threshold tsk));
            first rewrite leq_addr.
      Qed.
      
      (** But since we know that the job is completed by the end of its busy interval, 
         we can show that job j is completed by [job arrival j + R]. *)
      Lemma job_completed_by_arrival_plus_R_1:
        completed_by sched j (job_arrival j + R).
      Proof.
        move: H_busy_interval => [[/andP [GT LT] [QT1 NTQ]] QT2].
        apply completion_monotonic with t2; try done.
        apply t2_le_arrival_plus_R.
        eapply job_completes_within_busy_interval; eauto 2.
      Qed.

    End FixpointOutsideBusyInterval.

    (** In this section, we consider the complementary case where
       [t1 + A_sp + F_sp] lies inside the busy interval. *)
    Section FixpointInsideBusyInterval.

      (** So, assume that [t1 + A_sp + F_sp] is less than t2. *) 
      Hypothesis H_small_fixpoint_solution : t1 + (A_sp + F_sp) < t2.

      (** Next, let's consider two other cases: *)
      (** CASE 1: the value of the fix-point is no less than the relative arrival time of job [j]. *)
      Section FixpointIsNoLessThanArrival.
        
        (** Suppose that [A_sp + F_sp] is no less than relative arrival of job [j]. *)
        Hypothesis H_fixpoint_is_no_less_than_relative_arrival_of_j : A <= A_sp + F_sp.
 
        (** In this section, we prove that the fact that job [j] is not completed by 
           time [job_arrival j + R] leads to a contradiction. Which in turn implies
           that the opposite is true -- job [j] completes by time [job_arrival j + R]. *)
        Section ProofByContradiction.
            
          (** Recall that by lemma "solution_for_A_exists" there is a solution [F] 
             of the response-time recurrence for the given relative arrival time [A] 
             (which is not necessarily from the search space). *)

          (** Thus, consider a constant [F] such that:.. *)
          Variable F : duration.
          (** (a) the sum of [A_sp] and [F_sp] is equal to the sum of [A] and [F]... *)
          Hypothesis H_Asp_Fsp_eq_A_F : A_sp + F_sp = A + F.
          (** (b) [F] is at mo1st [F_sp]... *)
          Hypothesis H_F_le_Fsp : F <= F_sp.
          (** (c) and [A + F] is a solution for the response-time recurrence for [A]. *)
          Hypothesis H_A_F_fixpoint:
            A + F = task_run_to_completion_threshold tsk + interference_bound_function tsk A (A + F).
 
          (** Next, we assume that job [j] is not completed by time [job_arrival j + R]. *)
          Hypothesis H_j_not_completed : ~~ completed_by sched j (job_arrival j + R).

          (** Some additional reasoning is required since the term [task_cost tsk - task_run_to_completion_threshold tsk]
             does not necessarily bound the term [job_cost j - job_run_to_completion_threshold j]. That is, a job can 
             have a small run-to-completion threshold, thereby becoming non-preemptive much earlier than guaranteed 
             according to task run-to-completion threshold, while simultaneously executing the last non-preemptive 
             segment that is longer than [task_cost tsk - task_run_to_completion_threshold tsk] (e.g., this is possible 
             in the case of floating non-preemptive sections). 

             In this case we cannot directly apply lemma "j_receives_at_least_run_to_completion_threshold". Therefore
             we introduce two temporal notions of the last non-preemptive region of job j and an execution 
             optimism. We use these notions inside this proof, so we define them only locally. *)

          (** Let the last non-preemptive region of job [j] (last) be the difference between the cost of the job 
             and the [j]'s run-to-completion threshold (i.e. [job_cost j - job_run_to_completion_threshold j]). 
             We know that after j has reached its run-to-completion threshold, it will additionally be executed
             [job_last j] units of time. *)          
          Let job_last := job_cost j - job_run_to_completion_threshold j.

          (** And let execution optimism (optimism) be the difference between the [tsk]'s 
             run-to-completion threshold and the [j]'s run-to-completion threshold (i.e. 
             [task_run_to_completion_threshold -  job_run_to_completion_threshold]).
             Intuitively, optimism is how much earlier job j has received its 
             run-to-completion threshold than it could at worst.  *)
          Let optimism := task_run_to_completion_threshold tsk - job_run_to_completion_threshold j.
          
          (** From lemma "j_receives_at_least_run_to_completion_threshold" with parameters [progress_of_job :=
             job_run_to_completion_threshold j] and [delta := (A + F) - optimism)] we know that service of [j]
             by time [t1 + (A + F) - optimism] is no less than [job_run_to_completion_threshold j]. Hence, job [j]
             is completed by time [t1 + (A + F) - optimism + last]. *)
          Lemma j_is_completed_by_t1_A_F_optimist_last :
            completed_by sched j (t1 + (A + F - optimism) + job_last).
          Proof.
            have HelpAuto: forall m n, n <= n + m; first by intros; rewrite leq_addr.
            move: H_busy_interval => [[/andP [GT LT] _] _].
            have ESERV :=
              @j_receives_at_least_run_to_completion_threshold
                _ _ H1 H2 H3 PState H5 _ _  arr_seq sched tsk interference interfering_workload
                _ j _ _ _ t1 t2 _ (job_run_to_completion_threshold j) _ ((A + F) - optimism). 
            feed_n 7 ESERV; eauto 2.
            specialize (ESERV H3 H4).
            feed_n 2 ESERV.
            { eapply job_run_to_completion_threshold_le_job_cost; eauto. }
            { rewrite {2}H_A_F_fixpoint.
              rewrite /definitions.cumul_interference.
              rewrite -[in X in _ <= X]subh1; last by rewrite leq_subr.
              rewrite {2}/optimism.
              rewrite subKn; last by apply H_valid_run_to_completion_threshold.
              rewrite leq_add2l.              
              apply leq_trans with (cumul_interference j t1 (t1 + (A + F))).
              { rewrite /cumul_interference /definitions.cumul_interference;
                  rewrite [in X in _ <= X](@big_cat_nat _ _ _ (t1 + (A + F - optimism))) //=.
                  by rewrite leq_add2l leq_subr. }
              { apply H_job_interference_is_bounded with t2; try done.
                - by rewrite -H_Asp_Fsp_eq_A_F.
                - apply/negP; intros CONTR.
                  move: H_j_not_completed => /negP C; apply: C.
                  apply completion_monotonic with (t1 + (A + F)); try done.
                  rewrite addnA subnKC // leq_add2l.
                  apply leq_trans with F_sp; first by done.
                    by apply leq_trans with (F_sp + (task_cost tsk - task_run_to_completion_threshold tsk)).
              }
            }
            eapply job_completes_after_reaching_run_to_completion_threshold with (arr_seq0 := arr_seq); eauto 2.
          Qed.

          (** However, [t1 + (A + F) - optimism + last ≤ job_arrival j + R]! 
             To prove this fact we need a few auxiliary inequalities that are 
             needed because we use the truncated subtraction in our development.
             So, for example [a + (b - c) = a + b - c] only if [b ≥ c]. *) 
          Section AuxiliaryInequalities.
            
            (** Recall that we consider a busy interval of a job [j], and [j] has arrived [A] time units 
               after the beginning the busy interval. From basic properties of a busy interval it 
               follows that job [j] incurs interference at any time instant t ∈ <<[t1, t1 + A)>>. 
               Therefore [interference_bound_function(tsk, A, A + F)] is at least [A]. *)
            Lemma relative_arrival_le_interference_bound:
              A <= interference_bound_function tsk A (A + F).
            Proof.
              have HelpAuto: forall m n, n <= n + m; first by intros; rewrite leq_addr.
              move: H_j_not_completed; clear H_j_not_completed; move => /negP CONTRc.
              move: (H_busy_interval) => [[/andP [GT LT] _] _].
              apply leq_trans with (cumul_interference j t1 (t1 + (A+F))).
              { unfold cumul_interference.
                apply leq_trans with
                    (\sum_(t1 <= t < t1 + A) interference j t); last first.
                { unfold definitions.cumul_interference.
                  rewrite [in X in _ <= X](@big_cat_nat _ _ _ (t1 + A)) //=; last by rewrite addnA. }
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
                    by rewrite subnKC.                   
                }
              }
              { apply H_job_interference_is_bounded with t2; try done.
                - by rewrite -H_Asp_Fsp_eq_A_F.
                - apply/negP; intros CONTR; apply: CONTRc. 
                  apply completion_monotonic with (t1 + (A + F)); last by done. 
                  rewrite !addnA subnKC // leq_add2l.
                  apply leq_trans with F_sp; first by done.
                    by apply leq_trans with (F_sp + (task_cost tsk - task_run_to_completion_threshold tsk)).
              }
            Qed.
            
            (** As two trivial corollaries, we show that 
               [tsk]'s run-to-completion threshold is at most [F_sp]... *)
            Corollary tsk_run_to_completion_threshold_le_Fsp :
              task_run_to_completion_threshold tsk <= F_sp.
            Proof.
              have HH : task_run_to_completion_threshold tsk <= F.
              { move: H_A_F_fixpoint => EQ.
                have L1 := relative_arrival_le_interference_bound.
                ssromega.
              }
              apply leq_trans with F; auto.
            Qed.
            
            (** ... and optimism is at most [F]. *)
            Corollary optimism_le_F :
              optimism <= F.
            Proof.
              have HH : task_run_to_completion_threshold tsk <= F.
              { move: H_A_F_fixpoint => EQ.
                have L1 := relative_arrival_le_interference_bound.
                ssromega.
              }
                by apply leq_trans with (task_run_to_completion_threshold tsk); first rewrite /optimism leq_subr.
            Qed.
            
          End AuxiliaryInequalities.

          (** Next we show that [t1 + (A + F) - optimism + last] is at most [job_arrival j + R], 
             which is easy to see from the following sequence of inequalities:

             [t1 + (A + F) - optimism + last]
             [≤ job_arrival j + (F - optimism) + job_last]
             [≤ job_arrival j + (F_sp - optimism) + job_last]
             [≤ job_arrival j + F_sp + (job_last - optimism)]
             [≤ job_arrival j + F_sp + job_cost j - task_run_to_completion_threshold tsk]
             [≤ job_arrival j + F_sp + task_cost tsk - task_run_to_completion_threshold tsk]
             [≤ job_arrival j + R]. *)
          Lemma t1_A_F_optimist_last_le_arrival_R :
            t1 + (A + F - optimism) + job_last <= job_arrival j + R.
          Proof.
            move: (H_busy_interval) => [[/andP [GT LT] _] _].
            have L1 := tsk_run_to_completion_threshold_le_Fsp.
            have L2 := optimism_le_F.
            apply leq_trans with (job_arrival j + (F - optimism) + job_last).
            { rewrite leq_add2r addnBA.
              - by rewrite /A !addnA subnKC // addnBA.
              - by apply leq_trans with F; last rewrite leq_addl.
            }
            { move: H_valid_run_to_completion_threshold => [PRT1 PRT2]. 
              rewrite -addnA leq_add2l.
              apply leq_trans with (F_sp - optimism + job_last ); first by rewrite leq_add2r leq_sub2r. 
              apply leq_trans with (F_sp + (task_cost tsk - task_run_to_completion_threshold tsk)); last by done. 
              rewrite /optimism subnBA; last by apply PRT2.
              rewrite -subh1 //.
              rewrite /job_last.
              rewrite addnBA; last by eapply job_run_to_completion_threshold_le_job_cost; eauto.
              rewrite -subh1; last by rewrite leq_addl.
              rewrite -addnBA // subnn addn0.
              rewrite addnBA; last by apply PRT1.
              rewrite subh1; last by done.
              rewrite leq_sub2r // leq_add2l.
                by rewrite -H_job_of_tsk; apply H_valid_job_cost.
            }
          Qed.
          
          (** ... which contradicts the initial assumption about [j] is not 
             completed by time [job_arrival j + R]. *)
          Lemma j_is_completed_earlier_contradiction : False.
          Proof.
            move: H_j_not_completed => /negP C; apply: C.
            apply completion_monotonic with (t1 + ((A + F) - optimism) + job_last);
              auto using j_is_completed_by_t1_A_F_optimist_last, t1_A_F_optimist_last_le_arrival_R. 
          Qed.
          
        End ProofByContradiction.

        (** Putting everything together, we conclude that [j] is completed by [job_arrival j + R]. *) 
        Lemma job_completed_by_arrival_plus_R_2:
          completed_by sched j (job_arrival j + R).
        Proof.
          have HelpAuto: forall m n, n <= n + m; first by intros; rewrite leq_addr.
          move: H_busy_interval => [[/andP [GT LT] _] _].
          have L1 := solution_for_A_exists
                       tsk L (fun tsk A R => task_run_to_completion_threshold tsk
                                          + interference_bound_function tsk A R) A_sp F_sp.
          specialize (L1 H0).
          feed_n 2 L1; try done.
          { move: (H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive)
            => [t1' [t2' [_ [BOUND BUSY]]]].
            have EQ:= busy_interval_is_unique _ _ _ _ _ _ _ _ H_busy_interval BUSY.
            destruct EQ as [EQ1 EQ2].
            subst t1' t2'; clear BUSY.
              by rewrite -(ltn_add2l t1); apply leq_trans with t2.
          }
          specialize (L1 A); feed_n 2 L1.
          { by apply/andP; split. }
          { by intros x LTG; apply/eqP; rewrite eqn_add2l H_equivalent. }
          move: L1 => [F [EQSUM [F2LEF1 FIX2]]].
          apply/negP; intros CONTRc; move: CONTRc => /negP CONTRc.
            by eapply j_is_completed_earlier_contradiction in CONTRc; eauto 2.
        Qed.
        
      End FixpointIsNoLessThanArrival.

      (** CASE 2: the value of the fix-point is less than the relative arrival time of 
         job j (which turns out to be impossible, i.e. the solution of the response-time 
         recurrence is always equal to or greater than the relative arrival time). *)
      Section FixpointCannotBeSmallerThanArrival.

        (** Assume that [A_sp + F_sp] is less than A. *)
        Hypothesis H_fixpoint_is_less_that_relative_arrival_of_j: A_sp + F_sp < A.

        (** Note that the relative arrival time of job j is less than L. *)
        Lemma relative_arrival_is_bounded: A < L.
        Proof.
          rewrite /A.
          move: (H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive) => [t1' [t2' [_ [BOUND BUSY]]]].
          have EQ:= busy_interval_is_unique _ _ _ _ _ _ _ _ H_busy_interval BUSY. destruct EQ as [EQ1 EQ2].
          subst t1' t2'; clear BUSY.
          apply leq_trans with (t2 - t1); last by rewrite leq_subLR.
          move: (H_busy_interval)=> [[/andP [T1 T3] [_ _]] _].
            by apply ltn_sub2r; first apply leq_ltn_trans with (job_arrival j).
        Qed.                  

        (** We can use [j_receives_at_least_run_to_completion_threshold] to prove that the service 
           received by j by time [t1 + (A_sp + F_sp)] is no less than run-to-completion threshold. *)
        Lemma service_of_job_ge_run_to_completion_threshold:
          service sched j (t1 + (A_sp + F_sp)) >= job_run_to_completion_threshold j.
        Proof.
          move: (H_busy_interval) => [[NEQ [QT1 NTQ]] QT2].
          move: (NEQ) => /andP [GT LT]. 
          move: (H_job_interference_is_bounded t1 t2 (A_sp + F_sp) j) => IB. 
          feed_n 5 IB; try done.
          { apply/negP; intros COMPL.
            apply completion_monotonic with (t' := t1 + A) in COMPL; try done; last first.
            { by rewrite leq_add2l; apply ltnW. }
            { rewrite /A subnKC in COMPL; last by done.
              move: COMPL; rewrite /completed_by leqNgt; move => /negP COMPL; apply: COMPL. 
              rewrite /service -(service_during_cat _ _ _ (job_arrival j)); last by apply/andP; split.
              rewrite (cumulative_service_before_job_arrival_zero) // add0n.
                by rewrite /service_during big_geq //.
            } 
          }
          rewrite -/A in IB.
          have ALTT := relative_arrival_is_bounded.
          simpl in IB; rewrite H_equivalent in IB; last by apply ltn_trans with A.
          have ESERV :=
            @j_receives_at_least_run_to_completion_threshold
              _ _ H1 H2 H3 PState H5 _ _ arr_seq sched tsk
              interference interfering_workload _ j _ _ _ t1 t2 _ (job_run_to_completion_threshold j) _ (A_sp + F_sp). 
          feed_n 7 ESERV; eauto 2.
          specialize (ESERV H3 H4).
          feed_n 2 ESERV; eauto using job_run_to_completion_threshold_le_job_cost.
            by rewrite {2}H_Asp_Fsp_fixpoint leq_add //; apply H_valid_run_to_completion_threshold.
        Qed.

        (** However, this is a contradiction. Since job [j] has not yet arrived, its service 
           is equal to [0]. However, run-to-completion threshold is always positive. *)
        Lemma relative_arrival_time_is_no_less_than_fixpoint:
          False.
        Proof.
          move: (H_busy_interval) => [[NEQ [QT1 NTQ]] QT2].
          move: (NEQ) => /andP [GT LT].                    
          have ESERV := service_of_job_ge_run_to_completion_threshold.
          move: ESERV; rewrite leqNgt; move => /negP ESERV; apply: ESERV.
          rewrite /service cumulative_service_before_job_arrival_zero;
            eauto 5 using job_run_to_completion_threshold_positive. 
          rewrite -[X in _ <= X](@subnKC t1) //.
            by rewrite -/A leq_add2l ltnW.
        Qed.

      End FixpointCannotBeSmallerThanArrival.

    End FixpointInsideBusyInterval.
    
  End ProofOfTheorem.

  (** Using the lemmas above, we prove that [R] is a response-time bound. *)  
  Theorem uniprocessor_response_time_bound:
    response_time_bounded_by tsk R. 
  Proof. 
    intros j ARR JOBtsk. unfold job_response_time_bound.
    move: (posnP (@job_cost _ H3 j)) => [ZERO|POS].
    { by rewrite /completed_by ZERO. } 
    move: (H_busy_interval_exists j ARR JOBtsk POS) => [t1 [t2 [NEQ [T2 BUSY]]]].
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
        exfalso; apply relative_arrival_time_is_no_less_than_fixpoint
                   with (j := j) (t1 := t1) (t2 := t2) (A_sp := A1) (F_sp := F1); auto.
  Qed.

End Abstract_RTA. 
