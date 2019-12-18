Require Import prosa.classic.util.all.
Require Import prosa.classic.analysis.global.parallel.bertogna_fp_theory.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeIterationFP.

  Import ResponseTimeAnalysisFP.

  (* In this section, we define the algorithm of Bertogna and Cirinei's
     response-time analysis for FP scheduling with parallel jobs. *)
  Section Analysis.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    (* During the iterations of the algorithm, we pass around pairs
       of tasks and computed response-time bounds. *)
    Let task_with_response_time := (sporadic_task * time)%type.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider a platform with num_cpus processors, ... *)
    Variable num_cpus: nat.

    (* ..., and priorities based on an FP policy. *)
    Variable higher_priority: FP_policy sporadic_task.

    (* Next we define the fixed-point iteration for computing
       Bertogna's response-time bound of a task set. *)
    
    (* First, given a sequence of pairs R_prev = <..., (tsk_hp, R_hp)> of
       response-time bounds for the higher-priority tasks, we define an
       iteration that computes the response-time bound of the current task:

           R_tsk (0) = task_cost tsk
           R_tsk (step + 1) =  f (R step),

       where f is the response-time recurrence, step is the number of iterations,
       and R_tsk (0) is the initial state. *)
    Definition per_task_rta (tsk: sporadic_task)
                            (R_prev: seq task_with_response_time) (step: nat) :=
      iter step
        (fun t => task_cost tsk +
                  div_floor
                    (total_interference_bound_fp task_cost task_period R_prev t)
                    num_cpus)
        (task_cost tsk).

    (* To ensure that the iteration converges, we will apply per_task_rta
       a "sufficient" number of times: task_deadline tsk - task_cost tsk + 1.
       This corresponds to the time complexity of the iteration. *)
    Definition max_steps (tsk: sporadic_task) := task_deadline tsk - task_cost tsk + 1.
    
    (* Next we compute the response-time bounds for the entire task set.
       Since high-priority tasks may not be schedulable, we allow the
       computation to fail.
       Thus, given the response-time bound of previous tasks, we either
       (a) append the computed response-time bound (tsk, R) of the current task
           to the list of pairs, or,
       (b) return None if the response-time analysis failed. *)
    Definition fp_bound_of_task hp_pairs tsk :=
      if hp_pairs is Some rt_bounds then
        let R := per_task_rta tsk rt_bounds (max_steps tsk) in
          if R <= task_deadline tsk then
            Some (rcons rt_bounds (tsk, R))
          else None
      else None.

    (* The response-time analysis for a given task set is defined
       as a left-fold (reduce) based on the function above.
       This either returns a list of task and response-time bounds, or None. *)
    Definition fp_claimed_bounds (ts: seq sporadic_task) :=
      foldl fp_bound_of_task (Some [::]) ts.

    (* The schedulability test simply checks if we got a list of
       response-time bounds (i.e., if the computation did not fail). *)
    Definition fp_schedulable (ts: seq sporadic_task) :=
      fp_claimed_bounds ts != None.
    
    (* In the following section, we prove several helper lemmas about the
       list of response-time bounds. The results seem trivial, but must be proven
       nonetheless since the list of response-time bounds is computed with
       a specific algorithm and there are no lemmas in the library for that. *)
    Section SimpleLemmas.

      (* First, we show that the first component of the computed list is the set of tasks. *)
      Lemma fp_claimed_bounds_unzip :
        forall ts hp_bounds, 
          fp_claimed_bounds ts = Some hp_bounds ->
          unzip1 hp_bounds = ts.
      Proof.
        unfold fp_claimed_bounds in *; intros ts.
        induction ts using last_ind; first by destruct hp_bounds.
        {
          intros hp_bounds SOME.
          destruct (lastP hp_bounds) as [| hp_bounds'].
          {
            rewrite -cats1 foldl_cat /= in SOME.
            unfold fp_bound_of_task at 1 in SOME; simpl in *; desf.
            by destruct l.
          }
          rewrite -cats1 foldl_cat /= in SOME.
          unfold fp_bound_of_task at 1 in SOME; simpl in *; desf.
          move: H0 => /eqP EQSEQ.
          rewrite eqseq_rcons in EQSEQ.
          move: EQSEQ => /andP [/eqP SUBST /eqP EQSEQ]; subst.
          unfold unzip1; rewrite map_rcons; f_equal.
          by apply IHts.
        }
      Qed.
      
      (* Next, we show that some properties of the analysis are preserved for the
         prefixes of the list: (a) the tasks do not change, (b) R <= deadline,
         (c) R is computed using the response-time equation, ... *) 
      Lemma fp_claimed_bounds_rcons :
        forall ts' hp_bounds tsk1 tsk2 R,
          (fp_claimed_bounds (rcons ts' tsk1) = Some (rcons hp_bounds (tsk2, R)) ->
           (fp_claimed_bounds ts' = Some hp_bounds /\
            tsk1 = tsk2 /\
            R = per_task_rta tsk1 hp_bounds (max_steps tsk1) /\
            R <= task_deadline tsk1)).
      Proof.
        intros ts hp_bounds tsk tsk' R.
        rewrite -cats1.
        unfold fp_claimed_bounds in *.
        rewrite foldl_cat /=.
        unfold fp_bound_of_task at 1; simpl; desf.
        intros EQ; inversion EQ; move: EQ H0 => _ /eqP EQ.
        rewrite eqseq_rcons in EQ.
        move: EQ => /andP [/eqP EQ /eqP RESP].
        by inversion RESP; repeat split; subst.
      Qed.

      (* ..., which implies that any prefix of the computation is the computation
         of the prefix. *)
      Lemma fp_claimed_bounds_take :
        forall ts hp_bounds i,
          fp_claimed_bounds ts = Some hp_bounds ->
          i <= size hp_bounds ->
          fp_claimed_bounds (take i ts) = Some (take i hp_bounds).
      Proof.                                                        
        intros ts hp_bounds i SOME LTi.
        have UNZIP := fp_claimed_bounds_unzip ts hp_bounds SOME.
        rewrite <- UNZIP in *.
        rewrite -[hp_bounds]take_size /unzip1 map_take in SOME.
        fold (unzip1 hp_bounds) in *; clear UNZIP.
        rewrite leq_eqVlt in LTi.
        move: LTi => /orP [/eqP EQ | LTi]; first by subst.
        remember (size hp_bounds) as len; apply eq_leq in Heqlen.
        induction len; first by rewrite ltn0 in LTi.
        {
          assert (TAKElen: fp_claimed_bounds (take len (unzip1 (hp_bounds))) =
                             Some (take len (hp_bounds))).
          {
            assert (exists p, p \in hp_bounds).
            {
              destruct hp_bounds; first by rewrite ltn0 in Heqlen.
              by exists t; rewrite in_cons eq_refl orTb.
            } destruct H as [[tsk R] _].
             rewrite (take_nth tsk) in SOME; last by rewrite size_map.
            rewrite (take_nth (tsk,R)) in SOME; last by done.
            destruct (nth (tsk, R) hp_bounds len) as [tsk_len R_len].
            by apply fp_claimed_bounds_rcons in SOME; des.
          }
          rewrite ltnS leq_eqVlt in LTi.
          move: LTi => /orP [/eqP EQ | LESS]; first by subst.
          apply ltnW in Heqlen.
          by specialize (IHlen Heqlen TAKElen LESS).
        }
      Qed.
      
      (* If the analysis suceeds, the computed response-time bounds are no larger
         than the deadline... *)
      Lemma fp_claimed_bounds_le_deadline :
        forall ts' rt_bounds tsk R,
          fp_claimed_bounds ts' = Some rt_bounds ->
          (tsk, R) \in rt_bounds ->
          R <= task_deadline tsk.
      Proof.
        intros ts; induction ts as [| ts' tsk_lst] using last_ind.
        {
          intros rt_bounds tsk R SOME IN.
          by inversion SOME; subst; rewrite in_nil in IN.
        }
        {
          intros rt_bounds tsk_i R SOME IN.
          destruct (lastP rt_bounds) as [|rt_bounds (tsk_lst', R_lst)];
            first by rewrite in_nil in IN.
          rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
          destruct IN as [LAST | FRONT].
          {
            move: LAST => /eqP LAST.
            rewrite -cats1 in SOME.
            unfold fp_claimed_bounds in *.
            rewrite foldl_cat /= in SOME.
            unfold fp_bound_of_task in SOME.
            desf; rename H0 into EQ.
            move: EQ => /eqP EQ.
            rewrite eqseq_rcons in EQ.
            move: EQ => /andP [_ /eqP EQ].
            inversion EQ; subst.
            by apply Heq0.
          }
          {
            apply IHts with (rt_bounds := rt_bounds); last by ins.
            by apply fp_claimed_bounds_rcons in SOME; des.
          }
        }
      Qed.
      
      (* ... and the computed response-time bounds are no smaller than
         the task costs. *)
      Lemma fp_claimed_bounds_ge_cost :
        forall ts' rt_bounds tsk R,
          fp_claimed_bounds ts' = Some rt_bounds ->
          (tsk, R) \in rt_bounds ->
          R >= task_cost tsk.
      Proof.
        intros ts; induction ts as [| ts' tsk_lst] using last_ind.
        {
          intros rt_bounds tsk R SOME IN.
          by inversion SOME; subst; rewrite in_nil in IN.
        }
        {
          intros rt_bounds tsk_i R SOME IN.
          destruct (lastP rt_bounds) as [|rt_bounds (tsk_lst', R_lst)];
            first by rewrite in_nil in IN.
          rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
          destruct IN as [LAST | FRONT].
          {
            move: LAST => /eqP LAST.
            rewrite -cats1 in SOME.
            unfold fp_claimed_bounds in *.
            rewrite foldl_cat /= in SOME.
            unfold fp_bound_of_task in SOME.
            desf; rename H0 into EQ.
            move: EQ => /eqP EQ.
            rewrite eqseq_rcons in EQ.
            move: EQ => /andP [_ /eqP EQ].
            inversion EQ; subst.
            by destruct (max_steps tsk_lst');
              [by apply leqnn | by apply leq_addr].
          }
          {
            apply IHts with (rt_bounds := rt_bounds); last by ins.
            by apply fp_claimed_bounds_rcons in SOME; des.
          }
        }
      Qed.

      (* Short lemma about unfolding the iteration one step. *)
      Lemma per_task_rta_fold :
        forall tsk rt_bounds,
          task_cost tsk +
           div_floor (total_interference_bound_fp task_cost task_period rt_bounds
                     (per_task_rta tsk rt_bounds (max_steps tsk))) num_cpus
          = per_task_rta tsk rt_bounds (max_steps tsk).+1.
      Proof.
          by done.
      Qed.

    End SimpleLemmas.

    (* In this section, we prove that if the task set is sorted by priority,
       the tasks in fp_claimed_bounds are interfering tasks.  *)
    Section HighPriorityTasks.

      (* Consider a list of previous tasks and a task tsk to be analyzed. *)
      Variable ts: taskset_of sporadic_task.

      (* Assume that the task set is sorted by unique priorities, ... *)
      Hypothesis H_task_set_is_sorted: sorted higher_priority ts.
      Hypothesis H_task_set_has_unique_priorities:
        FP_is_antisymmetric_over_task_set higher_priority ts.

      (* ...the priority order is transitive, ...*)
      Hypothesis H_priority_transitive: FP_is_transitive higher_priority.
      
      (* ... and that the response-time analysis succeeds. *)
      Variable hp_bounds: seq task_with_response_time.
      Variable R: time.
      Hypothesis H_analysis_succeeds: fp_claimed_bounds ts = Some hp_bounds.

      (* Let's refer to tasks by index. *)
      Variable elem: sporadic_task.
      Let TASK := nth elem ts.
                    
      (* We prove that higher-priority tasks have smaller index. *)
      Lemma fp_claimed_bounds_hp_tasks_have_smaller_index :
        forall hp_idx idx,
          hp_idx < size ts ->
          idx < size ts ->
          hp_idx != idx ->
          higher_priority (TASK hp_idx) (TASK idx) ->
          hp_idx < idx.
      Proof.
        unfold TASK; clear TASK.
        rename ts into ts'; destruct ts' as [ts UNIQ]; simpl in *.
        intros hp_idx idx LThp LT NEQ HP.
        rewrite ltn_neqAle; apply/andP; split; first by done.
        by apply sorted_rel_implies_le_idx with (leT := higher_priority) (xs := ts) (default := elem).
      Qed.
      
    End HighPriorityTasks.

    (* In this section, we show that the fixed-point iteration converges. *)
    Section Convergence.

      (* Consider any set of higher-priority tasks. *)
      Variable ts_hp: seq sporadic_task.

      (* Assume that the response-time analysis succeeds for the higher-priority tasks. *)
      Variable rt_bounds: seq task_with_response_time.
      Hypothesis H_test_succeeds: fp_claimed_bounds ts_hp = Some rt_bounds.

      (* Consider any task tsk to be analyzed, ... *)
      Variable tsk: sporadic_task.

      (* ... and assume all tasks have valid parameters. *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline (rcons ts_hp tsk).

      (* To simplify, let f denote the fixed-point iteration. *)
      Let f := per_task_rta tsk rt_bounds.

      (* Assume that f (max_steps tsk) is no larger than the deadline. *)
      Hypothesis H_no_larger_than_deadline: f (max_steps tsk) <= task_deadline tsk.

      (* First, we show that f is monotonically increasing. *)
      Lemma bertogna_fp_comp_f_monotonic :
        forall x1 x2, x1 <= x2 -> f x1 <= f x2.
      Proof.
        unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
        rename H_test_succeeds into SOME,
               H_valid_task_parameters into VALID.
        intros x1 x2 LEx; unfold f, per_task_rta.
        apply fun_mon_iter_mon; [by ins | by ins; apply leq_addr |].
        clear LEx x1 x2; intros x1 x2 LEx.
        rewrite leq_add2l leq_div2r //.
        unfold total_interference_bound_fp.
        rewrite big_seq_cond.
        rewrite [\sum_(_ <- _ | true) _]big_seq_cond.
        apply leq_sum; move => i /andP [IN _].
        destruct i as [i R].
        have GE_COST := fp_claimed_bounds_ge_cost ts_hp rt_bounds i R SOME IN.
        have UNZIP := fp_claimed_bounds_unzip ts_hp rt_bounds SOME.
        unfold interference_bound_generic; simpl.
        apply W_monotonic; try (by done).
        have INts: i \in ts_hp by rewrite -UNZIP; apply/mapP; exists (i, R).
        by exploit (VALID i);
          [by rewrite mem_rcons in_cons INts orbT | by ins; des].
      Qed.

      (* If the iteration converged at an earlier step, then it remains stable. *)
      Lemma bertogna_fp_comp_f_converges_early :
        (exists k, k <= max_steps tsk /\ f k = f k.+1) ->
        f (max_steps tsk) = f (max_steps tsk).+1.
      Proof.
        by intros EX; des; apply fixedpoint.iter_fix with (k := k).
      Qed.

      (* Else, we derive a contradiction. *)
      Section DerivingContradiction.

        (* Assume instead that the iteration continued to diverge. *)
        Hypothesis H_keeps_diverging:
          forall k,
            k <= max_steps tsk -> f k != f k.+1.

        (* By monotonicity, it follows that the value always increases. *)
        Lemma bertogna_fp_comp_f_increases :
          forall k,
            k <= max_steps tsk ->
            f k < f k.+1.
        Proof.
          intros k LT.
          rewrite ltn_neqAle; apply/andP; split.
            by apply H_keeps_diverging.
            by apply bertogna_fp_comp_f_monotonic, leqnSn.
        Qed.

        (* In the end, the response-time bound must exceed the deadline. Contradiction! *)
        Lemma bertogna_fp_comp_rt_grows_too_much :
          forall k,
            k <= max_steps tsk ->
            f k > k + task_cost tsk - 1.
        Proof.
          have INC := bertogna_fp_comp_f_increases.
          rename H_valid_task_parameters into TASK_PARAMS.
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *; des.
          exploit (TASK_PARAMS tsk);
            [by rewrite mem_rcons in_cons eq_refl orTb | intro PARAMS; des].
          induction k.
          {
            intros _; rewrite add0n -addn1 subh1;
              first by rewrite -addnBA // subnn addn0 /= leqnn.
            by apply PARAMS.
          }
          {
            intros LT.
            specialize (IHk (ltnW LT)).
            apply leq_ltn_trans with (n := f k); last by apply INC, ltnW.
            rewrite -addn1 -addnA [1 + _]addnC addnA -addnBA // subnn addn0.
            rewrite -(ltn_add2r 1) in IHk.
            rewrite subh1 in IHk;
              last by apply leq_trans with (n := task_cost tsk);
                [by apply PARAMS | by apply leq_addl].
            by rewrite -addnBA // subnn addn0 addn1 ltnS in IHk.
          }  
        Qed.

      End DerivingContradiction.
      
      (* Using the lemmas above, we prove the convergence of the iteration after max_steps. *)
      Lemma per_task_rta_converges:
        f (max_steps tsk) = f (max_steps tsk).+1.
      Proof.
        have TOOMUCH := bertogna_fp_comp_rt_grows_too_much.
        have INC := bertogna_fp_comp_f_increases.
        rename H_no_larger_than_deadline into LE,
               H_valid_task_parameters into TASK_PARAMS.
        unfold valid_sporadic_taskset, is_valid_sporadic_task in *; des.
       
        (* Either f converges by the deadline or not. *)
        destruct ([exists k in 'I_(max_steps tsk).+1, f k == f k.+1]) eqn:EX.
        {
          move: EX => /exists_inP EX; destruct EX as [k _ ITERk].
          apply bertogna_fp_comp_f_converges_early.
          by exists k; split; [by rewrite -ltnS; apply ltn_ord | by apply/eqP].
        }

        (* If not, then we reach a contradiction *)
        apply negbT in EX; rewrite negb_exists_in in EX.
        move: EX => /forall_inP EX.
        rewrite leqNgt in LE; move: LE => /negP LE.
        exfalso; apply LE.

        assert (DIFF: forall k : nat, k <= max_steps tsk -> f k != f k.+1).
        {
          intros k LEk; rewrite -ltnS in LEk.
          by exploit (EX (Ordinal LEk)); [by done | intro DIFF; apply DIFF].
        }          
        exploit TOOMUCH; [by apply DIFF | by apply leq_addr |].
        exploit (TASK_PARAMS tsk);
          [by rewrite mem_rcons in_cons eq_refl orTb | intro PARAMS; des].
        rewrite subh1; last by apply PARAMS2.
        rewrite -addnBA // subnn addn0 subn1 prednK //.
        intros LT; apply (leq_ltn_trans LT).
        by rewrite /max_steps [_ - _ + 1]addn1; apply INC, leq_addr.
      Qed.
      
    End Convergence.
    
    Section MainProof.

      (* Consider a task set ts. *)
      Variable ts: taskset_of sporadic_task.
      
      (* Assume that all tasks have valid parameters, ... *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.

      (* ...and constrained deadlines.*)
      Hypothesis H_constrained_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

       (* Assume that the task set is totally ordered by unique priorities,
          and that the priority order is transitive. *)
      Hypothesis H_task_set_is_sorted: sorted higher_priority ts.
      Hypothesis H_task_set_has_unique_priorities:
        FP_is_antisymmetric_over_task_set higher_priority ts.
      Hypothesis H_priority_is_total:
        FP_is_total_over_task_set higher_priority ts.
      Hypothesis H_priority_transitive: FP_is_transitive higher_priority.

      (* Next, consider any arrival sequence such that...*)
      Variable arr_seq: arrival_sequence Job.

     (* ...all jobs come from task set ts, ...*)
      Hypothesis H_all_jobs_from_taskset:
        forall j, arrives_in arr_seq j -> job_task j \in ts.
      
      (* ...they have valid parameters,...*)
      Hypothesis H_valid_job_parameters:
        forall j,
          arrives_in arr_seq j ->
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
      
      (* ... and satisfy the sporadic task model.*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period job_arrival job_task arr_seq.
      
      (* Then, consider any schedule of this arrival sequence such that... *)
      Variable sched: schedule Job num_cpus.
      Hypothesis H_at_least_one_cpu: num_cpus > 0.
      Hypothesis H_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched arr_seq.
      
      (* ...jobs only execute after they arrived and no longer
         than their execution costs,... *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched.
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      (* Assume that the scheduler is work-conserving and respects the FP policy. *)
      Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
      Hypothesis H_respects_FP_policy:
        respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_priority.

      Let no_deadline_missed_by_task (tsk: sporadic_task) :=
        task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
      Let no_deadline_missed_by_job :=
        job_misses_no_deadline job_arrival job_cost job_deadline sched.
      Let response_time_bounded_by (tsk: sporadic_task) :=
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.
          
      (* In the following theorem, we prove that any response-time bound contained
         in fp_claimed_bounds is safe. The proof follows by induction on the task set:

           Induction hypothesis: all higher-priority tasks have safe response-time bounds.
           Inductive step: We prove that the response-time bound of the current task is safe.

         Note that the inductive step is a direct application of the main Theorem from
         bertogna_fp_theory.v. *)
      Theorem fp_analysis_yields_response_time_bounds :
        forall tsk R,
          (tsk, R) \In fp_claimed_bounds ts ->
          response_time_bounded_by tsk R.
      Proof.
        rename H_valid_job_parameters into JOBPARAMS, H_valid_task_parameters into TASKPARAMS.
        unfold valid_sporadic_taskset in *.
        intros tsk R MATCH.
        assert (SOME: exists hp_bounds, fp_claimed_bounds ts = Some hp_bounds /\
                                        (tsk, R) \in hp_bounds).
        {
          destruct (fp_claimed_bounds ts); last by done.
          by exists l; split.
        } clear MATCH; des; rename SOME0 into IN.

        have UNZIP := fp_claimed_bounds_unzip ts hp_bounds SOME.
        
        set elem := (tsk,R).
        move: IN => /(nthP elem) [idx LTidx EQ].
        set NTH := fun k => nth elem hp_bounds k.
        set TASK := fun k => (NTH k).1.
        set RESP := fun k => (NTH k).2.
        cut (response_time_bounded_by (TASK idx) (RESP idx));
          first by unfold TASK, RESP, NTH; rewrite EQ.
        clear EQ.

        assert (PAIR: forall idx, (TASK idx, RESP idx) = NTH idx).
          by intros i; unfold TASK, RESP; destruct (NTH i).

        assert (SUBST: forall i, i < size hp_bounds -> TASK i = nth tsk ts i).
          by intros i LTi; rewrite /TASK /NTH -UNZIP (nth_map elem) //.

        assert (SIZE: size hp_bounds = size ts).
          by rewrite -UNZIP size_map.

        induction idx as [idx IH'] using strong_ind.

        assert (IH: forall tsk_hp R_hp, (tsk_hp, R_hp) \in take idx hp_bounds -> response_time_bounded_by tsk_hp R_hp).
        {
          intros tsk_hp R_hp INhp.
          move: INhp => /(nthP elem) [k LTk EQ].
          rewrite size_take LTidx in LTk.
          rewrite nth_take in EQ; last by done.
          cut (response_time_bounded_by (TASK k) (RESP k));
            first by unfold TASK, RESP, NTH; rewrite EQ.
          by apply IH'; try (by done); apply (ltn_trans LTk).
        } clear IH'.

        unfold response_time_bounded_by in *.

        exploit (fp_claimed_bounds_rcons (take idx ts) (take idx hp_bounds) (TASK idx) (TASK idx) (RESP idx)).
        {
          by rewrite PAIR SUBST // -2?take_nth -?SIZE // (fp_claimed_bounds_take _ hp_bounds).
        }
        intros [_ [_ [REC DL]]].

        apply bertogna_cirinei_response_time_bound_fp with
              (task_cost0 := task_cost) (task_period0 := task_period)
              (task_deadline0 := task_deadline) (job_deadline0 := job_deadline) (tsk0 := (TASK idx))
              (job_task0 := job_task) (ts0 := ts) (hp_bounds0 := take idx hp_bounds)
              (higher_eq_priority := higher_priority); try (by done).
        {
          cut (NTH idx \in hp_bounds = true);
            [intros IN | by apply mem_nth].
          by rewrite set_mem -UNZIP; apply/mapP; exists (TASK idx, RESP idx); rewrite PAIR.
        }
        {
          intros hp_tsk IN INTERF.
          exists (RESP (index hp_tsk ts)).
          move: (IN) => INDEX; apply nth_index with (x0 := tsk) in INDEX.
          rewrite -{1}[hp_tsk]INDEX -SUBST; last by rewrite SIZE index_mem.
          assert (UNIQ: uniq hp_bounds).
          {
            apply map_uniq with (f := fst); unfold unzip1 in *; rewrite UNZIP.
            by destruct ts.
          }
          rewrite -filter_idx_lt_take //.
          {
            rewrite PAIR mem_filter; apply/andP; split;
              last by apply mem_nth; rewrite SIZE index_mem.
            {
              rewrite /NTH index_uniq; [| by rewrite SIZE index_mem | by done ].
              {
                move: INTERF => /andP [HP NEQ].
                apply fp_claimed_bounds_hp_tasks_have_smaller_index with
                  (ts := ts) (elem := tsk) (hp_bounds := hp_bounds);
                  try (by done);
                  [by rewrite index_mem | by rewrite -SIZE | | by rewrite INDEX -SUBST].
                apply/eqP; intro BUG; subst idx.
                rewrite SUBST -{1}INDEX in NEQ;
                  first by rewrite eq_refl in NEQ.
                by rewrite SIZE index_mem INDEX.
              }
            }
          }
        }
        {
          rewrite REC per_task_rta_fold.
          apply per_task_rta_converges with (ts_hp := take idx ts);
            [by apply fp_claimed_bounds_take; try (by apply ltnW) | | by rewrite -REC ].
          rewrite SUBST // -take_nth -?SIZE //.
          by intros i IN; eapply TASKPARAMS, mem_take, IN.
        }
      Qed.
      
      (* Therefore, if the schedulability test suceeds, ...*)
      Hypothesis H_test_succeeds: fp_schedulable ts.
      
      (*..., no task misses its deadline. *)
      Theorem taskset_schedulable_by_fp_rta :
        forall tsk, tsk \in ts -> no_deadline_missed_by_task tsk.
      Proof.
        have RLIST := (fp_analysis_yields_response_time_bounds).
        have UNZIP := (fp_claimed_bounds_unzip ts).
        have DL := (fp_claimed_bounds_le_deadline ts).
        unfold no_deadline_missed_by_task, task_misses_no_deadline,
               job_misses_no_deadline, completed,
               fp_schedulable, valid_sporadic_job in *.
        rename H_valid_job_parameters into JOBPARAMS.
        move => tsk INtsk j ARRj JOBtsk.
        
        destruct (fp_claimed_bounds ts) as [rt_bounds |]; last by ins.
        feed (UNZIP rt_bounds); first by done.
        assert (EX: exists R, (tsk, R) \in rt_bounds).
        {
          rewrite set_mem -UNZIP in INtsk; move: INtsk => /mapP EX.
          by destruct EX as [p]; destruct p as [tsk' R]; simpl in *; subst tsk'; exists R.
        } des.
        exploit (RLIST tsk R); eauto 1; intro COMPLETED.
        exploit (DL rt_bounds tsk R); [by ins | by ins | clear DL; intro DL].
        apply leq_trans with (n := service sched j (job_arrival j + R)); last first.
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
          apply extend_sum; rewrite // leq_add2l.
          specialize (JOBPARAMS j ARRj); des; rewrite JOBPARAMS1.
          by rewrite JOBtsk.
        }
        by done.
      Qed.

      (* For completeness, since all jobs of the arrival sequence
         are spawned by the task set, we also conclude that no job in
         the schedule misses its deadline. *)
      Theorem jobs_schedulable_by_fp_rta :
        forall j, arrives_in arr_seq j -> no_deadline_missed_by_job j.
      Proof.
        intros j ARRj.
        have SCHED := taskset_schedulable_by_fp_rta.
        unfold no_deadline_missed_by_task, task_misses_no_deadline in *.
        apply SCHED with (tsk := job_task j); try (by done).
        by apply H_all_jobs_from_taskset.
      Qed.
      
    End MainProof.

  End Analysis.

End ResponseTimeIterationFP.
