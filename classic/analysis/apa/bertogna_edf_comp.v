Require Import prosa.classic.util.all.
Require Import prosa.classic.analysis.apa.bertogna_edf_theory.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeIterationEDF.

  Import ResponseTimeAnalysisEDF.

  (* In this section, we define the algorithm corresponding to the APA-reduction
     of Bertogna and Cirinei's RTA for EDF scheduling. *)
  Section Analysis.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* As input for each iteration of the algorithm, we consider pairs
       of tasks and response-time bounds. *)
    Let task_with_response_time := (sporadic_task * time)%type.

    (* Consider a platform with num_cpus processors. *)  
    Variable num_cpus: nat.

    (* Assume that every task has a processor affinity alpha. *)
    Variable alpha: task_affinity sporadic_task num_cpus.

    (* For the reduction to subproblems, consider a subaffinity alpha' for each task. *)
    Variable alpha': task_affinity sporadic_task num_cpus.

    (* First, recall the interference bound under EDF. Note that we use
       subaffinity (alpha' tsk) when computing the set of interfering tasks. *)
    Let I (rt_bounds: seq task_with_response_time)
          (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline alpha tsk
                                   (alpha' tsk) (* Subproblem alpha' *)
                                   rt_bounds delta.

    (* Then, we define the response-time recurrence. Note that we divide the
       interference by the cardinality of (alpha' tsk). *)
    Definition edf_response_time_bound (rt_bounds: seq task_with_response_time)
                                           (tsk: sporadic_task) (delta: time) :=
      task_cost tsk + div_floor (I rt_bounds tsk delta)
                                #|alpha' tsk|.

    (* Also note that a response-time is only valid if it is no larger
       than the deadline. *)
    Definition R_le_deadline (pair: task_with_response_time) :=
      let (tsk, R) := pair in
        R <= task_deadline tsk.

    (* Next, we define the fixed-point iteration for computing the
       response-time bound of each task. *)
    
    (* Given a sequence 'rt_bounds' of task and response-time bounds
       from the previous iteration, we compute the response-time
       bound of a single task using the RTA for EDF. *)
    Definition update_bound (rt_bounds: seq task_with_response_time) pair :=
      let '(tsk, R) := pair in
        (tsk, edf_response_time_bound rt_bounds tsk R).

    (* To compute the response-time bounds of the entire task set,
       we start the iteration with a sequence of tasks and costs:
       <(task1, cost1), (task2, cost2), ...>. *)
    Let initial_state (ts: seq sporadic_task) :=
      map (fun tsk => (tsk, task_cost tsk)) ts.

    (* Then, we successively update the the response-time bounds based
       on the slack computed in the previous iteration. *)
    Definition edf_rta_iteration (rt_bounds: seq task_with_response_time) :=
      map (update_bound rt_bounds) rt_bounds.

    (* To ensure that the procedure converges, we stop the iteration
       after a "sufficient" number of times, which corresponds to
       the time complexity of the procedure. *)
    Let max_steps (ts: seq sporadic_task) :=
      \sum_(tsk <- ts) (task_deadline tsk - task_cost tsk) + 1.

    (* This yields the following definition for the RTA. At the end
       we check if all computed response-time bounds are less than
       or equal to the deadline, in which case they are valid. *)
    Definition edf_claimed_bounds (ts: seq sporadic_task) :=
      let R_values := iter (max_steps ts) edf_rta_iteration (initial_state ts) in
        if (all R_le_deadline R_values) then
          Some R_values
        else None.

    (* The schedulability test simply checks if we got a list of
       response-time bounds (i.e., if the computation did not fail). *)
    Definition edf_schedulable (ts: seq sporadic_task) :=
      edf_claimed_bounds ts != None.

    (* In the following section, we prove several helper lemmas about the
       list of tasks/response-time bounds. *)
    Section SimpleLemmas.

      (* Updating a single response-time bound does not modify the task. *)
      Lemma edf_claimed_bounds_unzip1_update_bound :
        forall l rt_bounds,
          unzip1 (map (update_bound rt_bounds) l) = unzip1 l.
      Proof.
        induction l; first by done.
        intros rt_bounds.
        simpl; f_equal; last by done.
        by unfold update_bound; desf.
      Qed.

      (* At any point of the iteration, the tasks are the same. *)
      Lemma edf_claimed_bounds_unzip1_iteration :
        forall l k,
          unzip1 (iter k edf_rta_iteration (initial_state l)) = l.
      Proof.
        intros l k; clear -k.
        induction k; simpl.
        {
          unfold initial_state.
          induction l; first by done.
          by simpl; rewrite IHl.
        }
        {
          unfold edf_rta_iteration. 
          by rewrite edf_claimed_bounds_unzip1_update_bound.
        }
      Qed.

      (* The iteration preserves the size of the list. *)
      Lemma edf_claimed_bounds_size :
        forall l k,
          size (iter k edf_rta_iteration (initial_state l)) = size l.
      Proof.
        intros l k; clear -k.
        induction k; simpl; first by rewrite size_map.
        by rewrite size_map.
      Qed.

      (* If the analysis succeeds, the computed response-time bounds are no smaller
         than the task cost. *)
      Lemma edf_claimed_bounds_ge_cost :
        forall l k tsk R,
          (tsk, R) \in (iter k edf_rta_iteration (initial_state l)) ->
          R >= task_cost tsk.
      Proof.
        intros l k tsk R IN.
        destruct k.
        {
          move: IN => /mapP IN; destruct IN as [x IN EQ]; inversion EQ.
          by apply leqnn.
        }
        {
          rewrite iterS in IN.
          move: IN => /mapP IN; destruct IN as [x IN EQ].
          unfold update_bound in EQ; destruct x; inversion EQ.
          by unfold edf_response_time_bound; apply leq_addr.
        }
      Qed.

      (* If the analysis suceeds, the computed response-time bounds are no larger
         than the deadline. *)
      Lemma edf_claimed_bounds_le_deadline :
        forall ts rt_bounds tsk R,
          edf_claimed_bounds ts = Some rt_bounds ->
          (tsk, R) \in rt_bounds ->
          R <= task_deadline tsk.
      Proof.
        intros ts rt_bounds tsk R SOME PAIR; unfold edf_claimed_bounds in SOME.
        destruct (all R_le_deadline (iter (max_steps ts)
                                          edf_rta_iteration (initial_state ts))) eqn:DEADLINE;
          last by done.
        move: DEADLINE => /allP DEADLINE.
        inversion SOME as [EQ]; rewrite -EQ in PAIR.
        by specialize (DEADLINE (tsk, R) PAIR).
      Qed.

      (* The list contains a response-time bound for every task in the task set. *)
      Lemma edf_claimed_bounds_has_R_for_every_task :
        forall ts rt_bounds tsk,
          edf_claimed_bounds ts = Some rt_bounds ->
          tsk \in ts ->
          exists R,
            (tsk, R) \in rt_bounds.
      Proof.
        intros ts rt_bounds tsk SOME IN.
        unfold edf_claimed_bounds in SOME.
        destruct (all R_le_deadline (iter (max_steps ts) edf_rta_iteration (initial_state ts)));
          last by done.
        inversion SOME as [EQ]; clear SOME EQ.
        generalize dependent tsk.
        induction (max_steps ts) as [| step]; simpl in *.
        {
          intros tsk IN; unfold initial_state.
          exists (task_cost tsk).
          by apply/mapP; exists tsk.
        }
        {
          intros tsk IN.
          set prev_state := iter step edf_rta_iteration (initial_state ts).
          fold prev_state in IN, IHstep.
          specialize (IHstep tsk IN); des.
          exists (edf_response_time_bound prev_state tsk R).
          by apply/mapP; exists (tsk, R); [by done | by f_equal].
        }
      Qed.
     
    End SimpleLemmas.

    (* In this section, we prove the convergence of the RTA procedure.
       Since we define the RTA procedure as the application of a function
       a fixed number of times, this translates into proving that the value
       of the iteration at (max_steps ts) is equal to the value at (max_steps ts) + 1. *)
    Section Convergence.

      (* Consider any sequence of tasks with valid parameters. *)
      Variable ts: seq sporadic_task.
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.
      
      (* To simplify, let f denote the RTA procedure. *)
      Let f (k: nat) := iter k edf_rta_iteration (initial_state ts).

      (* Since the iteration is applied directly to a list of tasks and response-times,
         we define a corresponding relation "<=" over those lists. *)

      (* Let 'all_le' be a binary relation over lists of tasks/response-time bounds.
         It states that every element of list l1 has a response-time bound R that is less
         than or equal to the corresponding response-time bound R' in list l2 (point-wise).
         In addition, the relation states that the tasks of both lists are unchanged. *)
      Let all_le := fun (l1 l2: list task_with_response_time) =>
        (unzip1 l1 == unzip1 l2) &&
        all (fun p => (snd (fst p)) <= (snd (snd p))) (zip l1 l2).

      (* Similarly, we define a strict version of 'all_le' called 'one_lt', which states that
         there exists at least one element whose response-time bound increases. *)
      Let one_lt := fun (l1 l2: list task_with_response_time) =>
        (unzip1 l1 == unzip1 l2) &&
        has (fun p => (snd (fst p)) < (snd (snd p))) (zip l1 l2).

      (* Next, we prove some basic properties about the relation all_le. *)
      Section RelationProperties.

        (* The relation is reflexive, ... *)
        Lemma all_le_reflexive : reflexive all_le.
        Proof.
          intros l; unfold all_le; rewrite eq_refl andTb.
          destruct l; first by done.
          by apply/(zipP t (fun x y => snd x <= snd y)).
        Qed.

        (* ... and transitive. *)
        Lemma all_le_transitive: transitive all_le.
        Proof.
          unfold transitive, all_le.
          move => y x z /andP [/eqP ZIPxy LExy] /andP [/eqP ZIPyz LEyz].
          apply/andP; split; first by rewrite ZIPxy -ZIPyz.
          move: LExy => /(zipP _ (fun x y => snd x <= snd y)) LExy.
          move: LEyz => /(zipP _ (fun x y => snd x <= snd y)) LEyz.
          assert (SIZExy: size (unzip1 x) = size (unzip1 y)).
            by rewrite ZIPxy.
          assert (SIZEyz: size (unzip1 y) = size (unzip1 z)).
            by rewrite ZIPyz.
          rewrite 2!size_map in SIZExy; rewrite 2!size_map in SIZEyz.
          destruct y.
          {
            apply size0nil in SIZExy; symmetry in SIZEyz.
            by apply size0nil in SIZEyz; subst.
          }
          apply/(zipP t (fun x y => snd x <= snd y)); first by rewrite SIZExy -SIZEyz. 
          intros i LTi.
          exploit LExy; first by rewrite SIZExy.
          {
            rewrite size_zip -SIZEyz -SIZExy minnn in LTi.
            by rewrite size_zip -SIZExy minnn; apply LTi.
          }
          instantiate (1 := t); intro LE.
          exploit LEyz; first by apply SIZEyz.
          {
            rewrite size_zip SIZExy SIZEyz minnn in LTi.
            by rewrite size_zip SIZEyz minnn; apply LTi.
          }
          by instantiate (1 := t); intro LE'; apply (leq_trans LE).
        Qed.

        (* At any step of the iteration, the corresponding list
           is larger than or equal to the initial state. *)
        Lemma bertogna_edf_comp_iteration_preserves_minimum :
          forall step, all_le (initial_state ts) (f step). 
        Proof.
          unfold f.
          intros step; destruct step; first by apply all_le_reflexive.
          apply/andP; split.
          {
            assert (UNZIP0 := edf_claimed_bounds_unzip1_iteration ts 0).
            by simpl in UNZIP0; rewrite UNZIP0 edf_claimed_bounds_unzip1_iteration.
          }  
          destruct ts as [| tsk0 ts'].
          {
            clear -step; induction step; first by done.
            by rewrite iterSr IHstep.
          }

          apply/(zipP (tsk0,0) (fun x y => snd x <= snd y));
            first by rewrite edf_claimed_bounds_size size_map.

          intros i LTi; rewrite iterS; unfold edf_rta_iteration at 1.
          have MAP := @nth_map _ (tsk0,0) _ (tsk0,0).
          rewrite size_zip edf_claimed_bounds_size size_map minnn in LTi.
          rewrite MAP; clear MAP; last by rewrite edf_claimed_bounds_size.
          destruct (nth (tsk0, 0) (initial_state (tsk0 :: ts')) i) as [tsk_i R_i] eqn:SUBST.
          rewrite SUBST; unfold update_bound.
          unfold initial_state in SUBST.
          have MAP := @nth_map _ tsk0 _ (tsk0, 0).
          rewrite ?MAP // in SUBST; inversion SUBST; clear MAP. 
          assert (EQtsk: tsk_i = fst (nth (tsk0, 0) (iter step edf_rta_iteration
                                                         (initial_state (tsk0 :: ts'))) i)).
          {
            have MAP := @nth_map _ (tsk0,0) _ tsk0 (fun x => fst x).
            rewrite -MAP; clear MAP; last by rewrite edf_claimed_bounds_size.
            have UNZIP := edf_claimed_bounds_unzip1_iteration; unfold unzip1 in UNZIP.
            by rewrite UNZIP; symmetry. 
          }
          destruct (nth (tsk0, 0) (iter step edf_rta_iteration (initial_state (tsk0 :: ts')))) as [tsk_i' R_i'].
          by simpl in EQtsk; rewrite -EQtsk; subst; apply leq_addr.
        Qed.

        (* The application of the function is inductive. *)
        Lemma bertogna_edf_comp_iteration_inductive (P : seq task_with_response_time -> Type) :
          P (initial_state ts) ->
          (forall k, P (f k) -> P (f (k.+1))) ->
          P (f (max_steps ts)).
        Proof.
          by intros P0 Pn; induction (max_steps ts); last by apply Pn.
        Qed.

        (* As a last step, we show that edf_rta_iteration preserves order, i.e., for any
           list l1 no smaller than the initial state, and list l2 such that
           l1 <= l2, we have (edf_rta_iteration l1) <= (edf_rta_iteration l2). *)
        Lemma bertogna_edf_comp_iteration_preserves_order :
          forall l1 l2,
            all_le (initial_state ts) l1 ->
            all_le l1 l2 ->
            all_le (edf_rta_iteration l1) (edf_rta_iteration l2).
        Proof.
          rename H_valid_task_parameters into VALID.
          intros x1 x2 LEinit LE.
          move: LE => /andP [/eqP ZIP LE]; unfold all_le.

          assert (UNZIP': unzip1 (edf_rta_iteration x1) = unzip1 (edf_rta_iteration x2)).
          {
            by rewrite 2!edf_claimed_bounds_unzip1_update_bound.
          }

          apply/andP; split; first by rewrite UNZIP'.
          apply f_equal with (B := nat) (f := fun x => size x) in UNZIP'.
          rename UNZIP' into SIZE.
          rewrite size_map [size (unzip1 _)]size_map in SIZE.
          move: LE => /(zipP _ (fun x y => snd x <= snd y)) LE.
          destruct x1 as [| p0 x1'], x2 as [| p0' x2']; try (by ins).
          apply/(zipP p0 (fun x y => snd x <= snd y)); first by done.
          
          intros i LTi.
          exploit LE; first by rewrite 2!size_map in SIZE.
          {
            by rewrite size_zip 2!size_map -size_zip in LTi; apply LTi.
          }
          rewrite 2!size_map in SIZE.
          instantiate (1 := p0); intro LEi.
          rewrite (nth_map p0);
            last by rewrite size_zip 2!size_map -SIZE minnn in LTi.
          rewrite (nth_map p0);
            last by rewrite size_zip 2!size_map SIZE minnn in LTi.
          unfold update_bound, edf_response_time_bound; desf; simpl.
          rename s into tsk_i, s0 into tsk_i', t into R_i, t0 into R_i', Heq into EQ, Heq0 into EQ'.
          assert (EQtsk: tsk_i = tsk_i').
          {
            destruct p0 as [tsk0 R0], p0' as [tsk0' R0']; simpl in H2; subst.
            have MAP := @nth_map _ (tsk0',R0) _ tsk0' (fun x => fst x) i ((tsk0', R0) :: x1').
            have MAP' := @nth_map _ (tsk0',R0) _ tsk0' (fun x => fst x) i ((tsk0', R0') :: x2').
            assert (FSTeq: fst (nth (tsk0', R0)((tsk0', R0) :: x1') i) =
                           fst (nth (tsk0',R0) ((tsk0', R0') :: x2') i)).
            {
              rewrite -MAP;
                last by simpl; rewrite size_zip 2!size_map /= -H0 minnn in LTi.
              rewrite -MAP';
                last by simpl; rewrite size_zip 2!size_map /= H0 minnn in LTi.
              by f_equal; simpl; f_equal.
            }
            apply f_equal with (B := sporadic_task) (f := fun x => fst x) in EQ.
            apply f_equal with (B := sporadic_task) (f := fun x => fst x) in EQ'.
            by rewrite FSTeq EQ' /= in EQ; rewrite EQ.
          }
          subst tsk_i'; rewrite leq_add2l.
          unfold I, total_interference_bound_edf; apply leq_div2r.
          rewrite 2!big_cons.
          destruct p0 as [tsk0 R0], p0' as [tsk0' R0'].
          simpl in H2; subst tsk0'.
          rename R_i into delta, R_i' into delta'.
          rewrite EQ EQ' in LEi; simpl in LEi.
          rename H0 into SIZE, H1 into UNZIP; clear EQ EQ'.

          assert (SUBST: forall l delta,
                    \sum_(j <- l | let '(tsk_other, _) := j in
                      different_task_in alpha tsk_i (alpha' tsk_i) tsk_other)
                        (let '(tsk_other, R_other) := j in
                          interference_bound_edf task_cost task_period task_deadline tsk_i delta
                            (tsk_other, R_other)) =
                    \sum_(j <- l | different_task_in alpha tsk_i (alpha' tsk_i) (fst j))
                      interference_bound_edf task_cost task_period task_deadline tsk_i delta j).
          {
            intros l x; clear -l.
            induction l; first by rewrite 2!big_nil.
            by rewrite 2!big_cons; rewrite IHl; desf; rewrite /= Heq in Heq0.
          } rewrite 2!SUBST; clear SUBST.

          assert (VALID': valid_sporadic_taskset task_cost task_period task_deadline
                                                       (unzip1 ((tsk0, R0) :: x1'))).
          {
            move: LEinit => /andP [/eqP EQinit _].
            rewrite -EQinit; unfold valid_sporadic_taskset.
            move => tsk /mapP IN. destruct IN as [p INinit EQ]; subst.
            by move: INinit => /mapP INinit; destruct INinit as [tsk INtsk]; subst; apply VALID.
          }

          assert (GE_COST: all (fun p => task_cost (fst p) <= snd p) ((tsk0, R0) :: x1')). 
          {
            clear LE; move: LEinit => /andP [/eqP UNZIP' LE].
            move: LE => /(zipP _ (fun x y => snd x <= snd y)) LE.
            specialize (LE (tsk0, R0)).
            apply/(all_nthP (tsk0,R0)).
            intros j LTj; generalize UNZIP'; simpl; intro SIZE'.
            have F := @f_equal _ _ size (unzip1 (initial_state ts)).
            apply F in SIZE'; clear F; rewrite /= 3!size_map in SIZE'.
            exploit LE; [by rewrite size_map /= | |].
            {
              rewrite size_zip size_map /= SIZE' minnn.
              by simpl in LTj; apply LTj.
            }
            clear LE; intro LE.
            unfold initial_state in LE.
            have MAP := @nth_map _ tsk0 _ (tsk0,R0).
            rewrite MAP /= in LE;
              [clear MAP | by rewrite SIZE'; simpl in LTj].
            apply leq_trans with (n := task_cost (nth tsk0 ts j));
              [apply eq_leq; f_equal | by done].
            have MAP := @nth_map _ (tsk0, R0) _ tsk0 (fun x => fst x).
            rewrite -MAP; [clear MAP | by done].
            unfold unzip1 in UNZIP'; rewrite -UNZIP'; f_equal.
            clear -ts; induction ts; [by done | by simpl; f_equal].
          }
          move: GE_COST => /allP GE_COST.

          assert (LESUM: \sum_(j <- x1' | different_task_in alpha tsk_i (alpha' tsk_i) (fst j))
                        interference_bound_edf task_cost task_period task_deadline tsk_i delta j <=                                  \sum_(j <- x2' | different_task_in alpha tsk_i (alpha' tsk_i) (fst j))
                        interference_bound_edf task_cost task_period task_deadline tsk_i delta' j).
          {
            set elem := (tsk0, R0); rewrite 2!(big_nth elem).
            rewrite -SIZE.
            rewrite big_mkcond [\sum_(_ <- _ | different_task_in _ _ _ _)_]big_mkcond.
            rewrite big_seq_cond [\sum_(_ <- _ | true) _]big_seq_cond.
            apply leq_sum; intros j; rewrite andbT; intros INj.
            rewrite mem_iota add0n subn0 in INj; move: INj => /andP [_ INj].
            assert (FSTeq: fst (nth elem x1' j) = fst (nth elem x2' j)).
            {
              have MAP := @nth_map _ elem _ tsk0 (fun x => fst x).
              by rewrite -2?MAP -?SIZE //; f_equal.
            } rewrite -FSTeq.
            destruct (different_task_in alpha tsk_i (alpha' tsk_i) (fst (nth elem x1' j))) eqn:INTERF;
              last by done.
            {
              exploit (LE elem); [by rewrite /= SIZE | | intro LEj].
              {
                rewrite size_zip 2!size_map /= -SIZE minnn in LTi.
                by rewrite size_zip /= -SIZE minnn; apply (leq_ltn_trans INj).
              }
              simpl in LEj.
              exploit (VALID' (fst (nth elem x1' j))); last intro VALIDj.
              {
                apply/mapP; exists (nth elem x1' j); last by done.
                by rewrite in_cons; apply/orP; right; rewrite mem_nth.
              }
              exploit (GE_COST (nth elem x1' j)); last intro GE_COSTj.
              {
                by rewrite in_cons; apply/orP; right; rewrite mem_nth.
              }
              unfold is_valid_sporadic_task in *.
              destruct (nth elem x1' j) as [tsk_j R_j] eqn:SUBST1,
                       (nth elem x2' j) as [tsk_j' R_j'] eqn:SUBST2.
              rewrite SUBST1 SUBST2 in LEj; clear SUBST1 SUBST2.
              simpl in FSTeq; rewrite -FSTeq; simpl in LEj; simpl in VALIDj; des.
              by apply interference_bound_edf_monotonic.
            }
          }
          destruct (different_task_in alpha tsk_i (alpha' tsk_i) tsk0) eqn:INTERFtsk0; last by done.
          apply leq_add; last by done.
          {             
            exploit (LE (tsk0, R0)); [by rewrite /= SIZE | | intro LEj];
              first by instantiate (1 := 0); rewrite size_zip /= -SIZE minnn.
            exploit (VALID' tsk0); first by rewrite in_cons; apply/orP; left.
            exploit (GE_COST (tsk0, R0)); first by rewrite in_cons eq_refl orTb.
            unfold is_valid_sporadic_task; intros GE_COST0 VALID0; des; simpl in LEj.
            by apply interference_bound_edf_monotonic.
          }
        Qed.

        (* It follows from the properties above that the iteration is monotonically increasing. *)
        Lemma bertogna_edf_comp_iteration_monotonic: forall k, all_le (f k) (f k.+1).
        Proof.
          unfold f; intros k.
          apply fun_mon_iter_mon_generic with (x1 := k) (x2 := k.+1);
            try (by done);
            [ by apply all_le_reflexive
            | by apply all_le_transitive
            | by apply bertogna_edf_comp_iteration_preserves_order
            | by apply bertogna_edf_comp_iteration_preserves_minimum].
        Qed.

      End RelationProperties.

      (* Knowing that the iteration is monotonically increasing (with respect to all_le),
         we show that the RTA procedure converges to a fixed point. *)

      (* First, note that when there are no tasks, the iteration trivially converges. *)
      Lemma bertogna_edf_comp_f_converges_with_no_tasks :
        size ts = 0 ->
        f (max_steps ts) = f (max_steps ts).+1.
      Proof.
        intro SIZE; destruct ts; last by inversion SIZE.
        unfold max_steps; rewrite big_nil /=.
        by unfold edf_rta_iteration.
      Qed.

      (* Otherwise, if the iteration reached a fixed point before (max_steps ts), then
         the value at (max_steps ts) is still at a fixed point. *)
      Lemma bertogna_edf_comp_f_converges_early :
        (exists k, k <= max_steps ts /\ f k = f k.+1) ->
        f (max_steps ts) = f (max_steps ts).+1.
      Proof.
        by intros EX; des; apply (@fixedpoint.iter_fix _ _ _ k).
      Qed.

      (* Else, we derive a contradiction. *)
      Section DerivingContradiction.

        (* Assume that there are tasks. *)
        Hypothesis H_at_least_one_task: size ts > 0.

        (* Assume that the iteration continued to diverge. *)
        Hypothesis H_keeps_diverging:
          forall k,
            k <= max_steps ts -> f k != f k.+1.

        (* Since the iteration is monotonically increasing, it must be
           strictly increasing. *)
        Lemma bertogna_edf_comp_f_increases :
          forall k,
            k <= max_steps ts -> one_lt (f k) (f k.+1).
        Proof.
          rename H_at_least_one_task into NONEMPTY.
          intros step LEstep; unfold one_lt; apply/andP; split;
            first by rewrite 2!edf_claimed_bounds_unzip1_iteration.
          rewrite -[has _ _]negbK; apply/negP; unfold not; intro ALL.
          rewrite -all_predC in ALL.
          move: ALL => /allP ALL.
          exploit (H_keeps_diverging step); [by done | intro DIFF].
          assert (DUMMY: exists tsk: sporadic_task, True).
          {
            destruct ts as [|tsk0]; first by rewrite ltnn in NONEMPTY.
            by exists tsk0.
          }
          des; clear DUMMY.
          move: DIFF => /eqP DIFF; apply DIFF.
          apply eq_from_nth with (x0 := (tsk, 0));
            first by simpl; rewrite size_map.
          {
            intros i LTi.
            remember (nth (tsk, 0)(f step) i) as p_i;rewrite -Heqp_i.
            remember (nth (tsk, 0)(f step.+1) i) as p_i';rewrite -Heqp_i'.
            rename Heqp_i into EQ, Heqp_i' into EQ'.
            exploit (ALL (p_i, p_i')).
            {
              rewrite EQ EQ'.
              rewrite -nth_zip; last by unfold f; rewrite iterS size_map.
              apply mem_nth; rewrite size_zip.
              unfold f; rewrite iterS size_map.
              by rewrite minnn.
            }
            unfold predC; simpl; rewrite -ltnNge; intro LTp.

            have GROWS := bertogna_edf_comp_iteration_monotonic step.
            move: GROWS => /andP [_ /allP GROWS].
            exploit (GROWS (p_i, p_i')).
            {
              rewrite EQ EQ'.
              rewrite -nth_zip; last by unfold f; rewrite iterS size_map.
              apply mem_nth; rewrite size_zip.
              unfold f; rewrite iterS size_map.
              by rewrite minnn.
            }
            simpl; intros LE.
            destruct p_i as [tsk_i R_i], p_i' as [tsk_i' R_i'].
            simpl in *.
            assert (EQtsk: tsk_i = tsk_i').
            {
              unfold edf_rta_iteration in EQ'.
              rewrite (nth_map (tsk, 0)) in EQ'; last by done.
              by unfold update_bound in EQ'; desf.
            }
            rewrite EQtsk; f_equal.
            by apply/eqP; rewrite eqn_leq; apply/andP; split.
          }
        Qed.

        (* In the end, each response-time bound is so high that the sum
           of all response-time bounds exceeds the sum of all deadlines.
           Contradiction! *)
        Lemma bertogna_edf_comp_rt_grows_too_much :
          forall k,
            k <= max_steps ts ->
            \sum_((tsk, R) <- f k) (R - task_cost tsk) + 1 > k.
        Proof.
          have LT := bertogna_edf_comp_f_increases.
          have MONO := bertogna_edf_comp_iteration_monotonic.
          rename H_at_least_one_task into NONEMPTY.
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
          rename H_valid_task_parameters into VALID.
          intros step LE.
          assert (DUMMY: exists tsk: sporadic_task, True).
          {
            destruct ts as [|tsk0]; first by rewrite ltnn in NONEMPTY.
            by exists tsk0.
          } destruct DUMMY as [elem _].

          induction step.
          {
            by rewrite addn1.
          }
          {
            rewrite -addn1 ltn_add2r.
            apply leq_ltn_trans with (n := \sum_(i <- f step) (let '(tsk, R) := i in R - task_cost tsk)).
            {
              rewrite -ltnS; rewrite addn1 in IHstep.
              by apply IHstep, ltnW.
            }
            rewrite (eq_bigr (fun x => snd x - task_cost (fst x)));
              last by ins; destruct i.
            rewrite [\sum_(_ <- f step.+1)_](eq_bigr (fun x => snd x - task_cost (fst x)));
              last by ins; destruct i.
            unfold f at 2; rewrite iterS.
            rewrite big_map; fold (f step).
            rewrite -(ltn_add2r (\sum_(i <- f step) task_cost (fst i))).
            rewrite -2!big_split /=.
            rewrite big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
            rewrite (eq_bigr (fun i => snd i)); last first.
            {
              intro i; rewrite andbT; intro IN;
              rewrite subh1; first by rewrite -addnBA // subnn addn0.
              have GE_COST := edf_claimed_bounds_ge_cost ts step.
              by destruct i; apply GE_COST.
            }
            rewrite [\sum_(_ <- _ | _)(_ - _ + _)](eq_bigr (fun i => snd (update_bound (f step) i))); last first.
            {
              intro i; rewrite andbT; intro IN.
              unfold update_bound; destruct i; simpl.
              rewrite subh1; first by rewrite -addnBA // subnn addn0.
              apply (edf_claimed_bounds_ge_cost ts step.+1).
              by rewrite iterS; apply/mapP; exists (s, t).
            }
            rewrite -2!big_seq_cond.
           
            specialize (LT step (ltnW LE)).
            specialize (MONO step).
            move: LT => /andP [_ LT]; move: LT => /hasP LT.
            destruct LT as [[x1 x2] INzip LT]; simpl in *.
            move: MONO => /andP [_ /(zipP _ (fun x y => snd x <= snd y)) MONO].
            rewrite 2!(big_nth (elem, 0)).
            apply mem_zip_exists with (elem := (elem, 0)) (elem' := (elem, 0)) in INzip; des;
              last by rewrite size_map.
            rewrite -> big_cat_nat with (m := 0) (n := idx) (p := size (f step));
              [simpl | by done | by apply ltnW].
            rewrite -> big_cat_nat with (m := idx) (n := idx.+1) (p := size (f step));
              [simpl | by done | by done].
            rewrite big_nat_recr /=; last by done.
            rewrite -> big_cat_nat with (m := 0) (n := idx) (p := size (f step));
              [simpl | by done | by apply ltnW].
            rewrite -> big_cat_nat with (m := idx) (n := idx.+1) (p := size (f step));
              [simpl | by done | by done].
            rewrite big_nat_recr /=; last by done.
            rewrite [\sum_(idx <= i < idx) _]big_geq // add0n.
            rewrite [\sum_(idx <= i < idx) _]big_geq // add0n.
            rewrite -addn1 -addnA; apply leq_add.
            {
              rewrite big_nat_cond [\sum_(_ <= _ < _ | true) _]big_nat_cond.
              apply leq_sum; move => i /andP [/andP [LT1 LT2] _].
              exploit (MONO (elem,0)); [by rewrite size_map | | intro LEi].
              {
                rewrite size_zip; apply (ltn_trans LT2).
                by apply leq_trans with (n := size (f step));
                  [by done | by rewrite size_map minnn].
              }
              unfold edf_rta_iteration in LEi.
              by rewrite -> nth_map with (x1 := (elem, 0)) in LEi;
                last by apply (ltn_trans LT2).
            }
            rewrite -addnA [_ + 1]addnC addnA; apply leq_add.
            {
              unfold edf_rta_iteration in INzip2; rewrite addn1.
              rewrite -> nth_map with (x1 := (elem, 0)) in INzip2; last by done.
              by rewrite -INzip2 -INzip1.
            }
            {
              rewrite big_nat_cond [\sum_(_ <= _ < _ | true) _]big_nat_cond.
              apply leq_sum; move => i /andP [/andP [LT1 LT2] _].
              exploit (MONO (elem,0));
                [ by rewrite size_map
                | by rewrite size_zip; apply (leq_trans LT2); rewrite size_map minnn | intro LEi ].
              unfold edf_rta_iteration in LEi.
              by rewrite -> nth_map with (x1 := (elem, 0)) in LEi; last by done.
            }
          }
        Qed.

      End DerivingContradiction. 

      (* Using the lemmas above, we prove that edf_rta_iteration reaches
         a fixed point after (max_steps ts) step, ... *)
      Lemma edf_claimed_bounds_finds_fixed_point_of_list :
        forall rt_bounds,
          edf_claimed_bounds ts = Some rt_bounds ->
          valid_sporadic_taskset task_cost task_period task_deadline ts ->
          f (max_steps ts) = edf_rta_iteration (f (max_steps ts)). 
      Proof.
        intros rt_bounds SOME VALID.
        unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
        unfold edf_claimed_bounds in SOME; desf.
        rename Heq into LE.
        fold (f (max_steps ts)) in *; fold (f (max_steps ts).+1).

        (* Either the task set is empty or not. *)
        destruct (size ts == 0) eqn:EMPTY;
          first by apply bertogna_edf_comp_f_converges_with_no_tasks; apply/eqP.
        apply negbT in EMPTY; rewrite -lt0n in EMPTY.

        (* Either f converges by the deadline or not. *)
        destruct ([exists k in 'I_((max_steps ts).+1), f k == f k.+1]) eqn:EX.
        {
          move: EX => /exists_inP EX; destruct EX as [k _ ITERk].
          destruct k as [k LTk]; simpl in ITERk.
          apply bertogna_edf_comp_f_converges_early.
          exists k; split; [by apply LTk | by apply/eqP].
        }

        (* If not, then we reach a contradiction *)
        apply negbT in EX; rewrite negb_exists_in in EX.
        move: EX => /forall_inP EX.

        assert (SAMESUM: \sum_(tsk <- ts) task_cost tsk = \sum_(p <- f (max_steps ts)) task_cost (fst p)).
        {
          have MAP := @big_map _ 0 addn _ _ (fun x => fst x) (f (max_steps ts))
                               (fun x => true) (fun x => task_cost x).
          have UNZIP := edf_claimed_bounds_unzip1_iteration ts (max_steps ts).
          fold (f (max_steps ts)) in UNZIP; unfold unzip1 in UNZIP.
          by rewrite UNZIP in MAP; rewrite MAP.
        }
        
        (* Show that the sum is less than the sum of all deadlines. *)
        assert (SUM: \sum_(p <- f (max_steps ts)) (snd p - task_cost (fst p)) + 1 <= max_steps ts). 
        {
          unfold max_steps at 2; rewrite leq_add2r.
          rewrite -(leq_add2r (\sum_(tsk <- ts) task_cost tsk)).
          rewrite {1}SAMESUM -2!big_split /=.
          rewrite big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
          rewrite (eq_bigr (fun x => snd x)); last first.
          {
            intro i; rewrite andbT; intro IN.
            rewrite subh1; first by rewrite -addnBA // subnn addn0.
            have GE_COST := edf_claimed_bounds_ge_cost ts (max_steps ts).
            fold (f (max_steps ts)) in GE_COST.
            by destruct i; apply GE_COST.
          }
          rewrite (eq_bigr (fun x => task_deadline x)); last first.
          {
            intro i; rewrite andbT; intro IN.
            rewrite subh1; first by rewrite -addnBA // subnn addn0.
            by specialize (VALID i IN); des.
          }
          rewrite -2!big_seq_cond.
          have MAP := @big_map _ 0 addn _ _ (fun x => fst x) (f (max_steps ts))
                               (fun x => true) (fun x => task_deadline x).
          have UNZIP := edf_claimed_bounds_unzip1_iteration ts (max_steps ts).
          fold (f (max_steps ts)) in UNZIP; unfold unzip1 in UNZIP.
          rewrite UNZIP in MAP; rewrite MAP.
          rewrite big_seq_cond [\sum_(_ <- _|true)_]big_seq_cond.
          apply leq_sum; intro i; rewrite andbT; intro IN.
          move: LE => /allP LE; unfold R_le_deadline in LE.
          by specialize (LE i IN); destruct i.
        }

        have TOOMUCH :=
          bertogna_edf_comp_rt_grows_too_much EMPTY _ (max_steps ts) (leqnn (max_steps ts)).
        exploit TOOMUCH; [| intro BUG].
        {
          intros k LEk; rewrite -ltnS in LEk.
          by exploit (EX (Ordinal LEk)); [by done | by ins].
        }
        rewrite (eq_bigr (fun i => snd i - task_cost (fst i))) in BUG;
          last by ins; destruct i.
        by apply (leq_ltn_trans SUM) in BUG; rewrite ltnn in BUG. 
      Qed.

      (* ...and since there cannot be a vector of response-time bounds with values less than
         the task costs, this solution is also the least fixed point. *)
      Lemma edf_claimed_bounds_finds_least_fixed_point :
        forall v,
          all_le (initial_state ts) v ->
          v = edf_rta_iteration v ->
          all_le (f (max_steps ts)) v.
      Proof.
        intros v GE0 EQ.
        apply bertogna_edf_comp_iteration_inductive; first by done.
        intros k GEk.
        rewrite EQ.
        apply bertogna_edf_comp_iteration_preserves_order; last by done.
        by apply bertogna_edf_comp_iteration_preserves_minimum.
      Qed.

      
      (* Therefore, with regard to the response-time bound recurrence,  
         the individual response-time bounds (elements of the list) are
         also fixed points. *)
      Theorem edf_claimed_bounds_finds_fixed_point_for_each_bound :
        forall tsk R rt_bounds,
          edf_claimed_bounds ts = Some rt_bounds ->
          (tsk, R) \in rt_bounds ->
          R = edf_response_time_bound rt_bounds tsk R. 
      Proof.
        intros tsk R rt_bounds SOME IN.
        have CONV := edf_claimed_bounds_finds_fixed_point_of_list rt_bounds.
        rewrite -iterS in CONV; fold (f (max_steps ts).+1) in CONV.
        unfold edf_claimed_bounds in *; desf.
        exploit (CONV); [by done | by done | intro ITER; clear CONV].
        unfold f in ITER.

        cut (update_bound (iter (max_steps ts)
               edf_rta_iteration (initial_state ts)) (tsk,R) = (tsk, R)).
        {
          intros EQ.
          have F := @f_equal _ _ (fun x => snd x) _ (tsk, R).
          by apply F in EQ; simpl in EQ.
        }
        set s := iter (max_steps ts) edf_rta_iteration (initial_state ts).
        fold s in ITER, IN.
        move: IN => /(nthP (tsk,0)) IN; destruct IN as [i LT EQ].
        generalize EQ; rewrite ITER iterS in EQ; intro EQ'.
        fold s in EQ.
        unfold edf_rta_iteration in EQ.
        have MAP := @nth_map _ (tsk,0) _ _ (update_bound s). 
        by rewrite MAP // EQ' in EQ; rewrite EQ.
      Qed.
      
    End Convergence.

    (* Now we prove the correctness of the response-time bounds. *)
    Section MainProof.

      (* Consider a task set ts where... *)
      Variable ts: taskset_of sporadic_task.
      
      (* ... all tasks have valid parameters ... *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.

      (* ... and constrained deadlines. *)
      Hypothesis H_constrained_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

      (* Assume that alpha' is a non-empty subaffinity of alpha. *)
      Hypothesis H_non_empty_affinity:
        forall tsk, tsk \in ts -> #|alpha' tsk| > 0.
      Hypothesis H_subaffinity:
        forall tsk, tsk \in ts -> is_subaffinity (alpha' tsk) (alpha tsk).
                                      
      (* Next, consider any arrival sequence such that...*)
      Variable arr_seq: arrival_sequence Job.

     (* ...all jobs come from task set ts, ...*)
      Hypothesis H_all_jobs_from_taskset:
        forall j,
          arrives_in arr_seq j -> job_task j \in ts.
      
      (* ...they have valid parameters,...*)
      Hypothesis H_valid_job_parameters:
        forall j,
          arrives_in arr_seq j ->
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
      
      (* ... and satisfy the sporadic task model.*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period job_arrival job_task arr_seq.
      
      (* Then, consider any schedule with at least one CPU such that...*)
      Variable sched: schedule Job num_cpus.
      Hypothesis H_jobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched arr_seq.

      (* ...jobs only execute after they arrived and no longer
         than their execution costs,... *)
      Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
      Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

      (* ...and jobs are sequential. *)
      Hypothesis H_sequential_jobs: sequential_jobs sched.
      
      (* Assume a work-conserving APA scheduler that respects EDF policy. *)
      Hypothesis H_respects_affinity: respects_affinity job_task sched alpha.
      Hypothesis H_work_conserving: apa_work_conserving job_arrival job_cost job_task arr_seq
                                                        sched alpha.
      Hypothesis H_edf_policy:
        respects_JLFP_policy_under_weak_APA job_arrival job_cost job_task
                                            arr_seq sched alpha (EDF job_arrival job_deadline).

      (* To avoid a long list of parameters, we provide some local definitions. *)      
      Definition no_deadline_missed_by_task (tsk: sporadic_task) :=
        task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
      Definition no_deadline_missed_by_job :=
        job_misses_no_deadline job_arrival job_cost job_deadline sched.
      Let response_time_bounded_by (tsk: sporadic_task) :=
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.
      
      (* In the following theorem, we prove that any response-time bound contained
         in edf_claimed_bounds is safe. The proof follows by direct application of
         the main Theorem from bertogna_edf_theory.v. *)
      Theorem edf_analysis_yields_response_time_bounds :
        forall tsk R,
          (tsk, R) \In edf_claimed_bounds ts ->
          response_time_bounded_by tsk R.
      Proof.
        have BOUND := bertogna_cirinei_response_time_bound_edf.
        intros tsk R IN j ARRj JOBj.
        destruct (edf_claimed_bounds ts) as [rt_bounds |] eqn:SOME; last by done.
        unfold edf_rta_iteration in *.
        unfold is_response_time_bound_of_task in *.
        apply BOUND with (task_cost := task_cost) (task_period := task_period)
           (arr_seq := arr_seq) (task_deadline := task_deadline) (job_deadline := job_deadline)
           (job_task := job_task) (ts := ts) (tsk := tsk) (rt_bounds := rt_bounds) (alpha := alpha) (alpha' := alpha'); try (by ins).
        by unfold edf_claimed_bounds in SOME; desf; rewrite edf_claimed_bounds_unzip1_iteration.
        by ins; apply edf_claimed_bounds_finds_fixed_point_for_each_bound with (ts := ts).
        by ins; rewrite (edf_claimed_bounds_le_deadline ts rt_bounds).
      Qed.
      
      (* Therefore, if the schedulability test suceeds, ...*)
      Hypothesis H_test_succeeds: edf_schedulable ts.
      
      (*... no task misses its deadline. *)
      Theorem taskset_schedulable_by_edf_rta :
        forall tsk, tsk \in ts -> no_deadline_missed_by_task tsk.
      Proof.
        have RLIST := (edf_analysis_yields_response_time_bounds).
        have DL := (edf_claimed_bounds_le_deadline ts).
        have HAS := (edf_claimed_bounds_has_R_for_every_task ts).
        unfold no_deadline_missed_by_task, task_misses_no_deadline,
               job_misses_no_deadline, completed,
               edf_schedulable,
               valid_sporadic_job in *.
        rename H_valid_job_parameters into JOBPARAMS.
        intros tsk INtsk j ARRj JOBtsk.
        destruct (edf_claimed_bounds ts) as [rt_bounds |] eqn:SOME; last by ins.
        exploit (HAS rt_bounds tsk); [by ins | by ins | clear HAS; intro HAS; des].
        have COMPLETED := RLIST tsk R HAS j ARRj JOBtsk.
        exploit (DL rt_bounds tsk R);
          [by ins | by ins | clear DL; intro DL].
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
         are spawned by the task set, we conclude that no job misses
         its deadline. *)
      Theorem jobs_schedulable_by_edf_rta :
        forall j, arrives_in arr_seq j -> no_deadline_missed_by_job j.
      Proof.
        intros j ARRj.
        have SCHED := taskset_schedulable_by_edf_rta.
        unfold no_deadline_missed_by_task, task_misses_no_deadline in *.
        apply SCHED with (tsk := job_task j); try (by done).
        by apply H_all_jobs_from_taskset.
      Qed.
     
    End MainProof.

  End Analysis.

End ResponseTimeIterationEDF.
