Require Export prosa.results.edf.rta.bounded_nps.
Require Export prosa.implementation.refinements.fast_search_space_computation.

(** First, we define the concept of higher-or-equal-priority workload.  *)
Definition bound_on_total_hep_workload (ts : seq Task) (tsk : Task) A Δ :=
  \sum_(tsk_o <- ts | tsk_o != tsk)
   task_rbf tsk_o (minn ((A + ε) + task_deadline tsk - task_deadline tsk_o) Δ).

(** Next, we provide a function that checks a single point [P=(A,F)] of the search space when
    adopting a fully-preemptive policy. *)
Definition check_point_FP (ts : seq Task) (tsk : Task) (R : nat) (P : nat * nat) :=
  (task_rbf tsk (P.1 + ε) + bound_on_total_hep_workload ts tsk P.1 (P.1 + P.2) <= P.1 + P.2)
  && (P.2 <= R).

(** Further, we provide a way to compute the blocking bound when using nonpreemptive policies. *)
Definition blocking_bound_NP (ts : seq Task) (tsk : Task) (A : nat) :=
  \max_(tsk_o <- [seq i | i <- ts]
       | blocking_relevant tsk_o
         && (task_deadline tsk + A < task_deadline tsk_o)) (task_cost tsk_o - ε).

(** Finally, we provide a function that checks a single point [P=(A,F)] of the search space when
    adopting a fully-nonpreemptive policy. *)
Definition check_point_NP (ts : seq Task) (tsk : Task) (R : nat) (P : nat * nat) :=
  (blocking_bound_NP ts tsk P.1
   + (task_rbf tsk (P.1 + ε) - (task_cost tsk - ε))
   + bound_on_total_hep_workload ts tsk P.1 (P.1 + P.2) <= P.1 + P.2)
  && (P.2 + (task_cost tsk - ε) <= R).

(** * Search Space Definitions *)
Section SearchSpaceDefinition.

  (** Assume that an arrival curve based on a concrete prefix is given ... *)
  #[local] Existing Instance ConcreteMaxArrivals.
  Definition Task := concrete_task : eqType.
  Definition Job := concrete_job : eqType.

  (** ... and that we know the maximum non-preemptive segment for each task. *)
  Context (TMNSP : TaskMaxNonpreemptiveSegment Task).

  (** First, we recall the notion of correct search space as defined by
    abstract RTA. *)
  Definition correct_search_space ts (tsk : Task) L :=
    [seq A <- iota 0 L | is_in_search_space ts tsk L A].

  (** Next, we provide a computation-oriented way to compute abstract RTA's search space for
    fixed-priority schedules, as we will prove that earliest-deadline-first is equivalent.
    We start with a function that computes the search space in a generic
    interval <<[l,r)>>, ... *)
  Definition search_space_emax_FP_h (tsk : Task) l r :=
    let h := get_horizon_of_task tsk in
    let offsets := map (muln h) (iota l r) in
    let emax_offsets := repeat_steps_with_offset tsk offsets in
    map predn emax_offsets.

  (** ... which we then apply to the interval <<[0, (L %/h).+1)>>.  *)
  Definition search_space_emax_FP L (tsk : Task) :=
    let h := get_horizon_of_task tsk in
    search_space_emax_FP_h (tsk : Task) 0 (L %/h).+1.

  (** Analogously, we define the search space for a task scheduled under earliest-deadline-first
    in a generic interval <<[l,r)>>, ... *)
  Definition task_search_space_emax_EDF_h (tsk tsko : Task) (l r : nat) :=
    let h := get_horizon_of_task tsko in
    let offsets := map (muln h) (iota l r) in
    let emax_offsets := repeat_steps_with_offset tsko offsets in
    let emax_edf_offsets := shift_points_neg (shift_points_pos emax_offsets (task_deadline tsko))
                                             (task_deadline tsk) in
    map predn emax_edf_offsets.

  (** ...which we then apply to the interval <<[0, (L %/h).+1)>>. *)
  Definition task_search_space_emax_EDF (tsk tsko : Task) (L : nat) :=
    let h := get_horizon_of_task tsko in
    task_search_space_emax_EDF_h tsk tsko
                                 0 ((L + (task_deadline tsk - task_deadline tsko)) %/ h).+1.

  (** Finally, we define the overall search space as the concatenation of per-task search
    spaces. *)
  Definition search_space_emax_EDF ts (tsk : Task) (L : nat) :=
    \cat_(tsko <- ts) task_search_space_emax_EDF tsk tsko L.

End SearchSpaceDefinition.

(** * Fast Search Space Computation Lemmas *)
Section FastSearchSpaceComputationSubset.

  (** Consider a given maximum busy-interval length [L], ... *)
  Variable L : duration.

  (** ... a task set [ts] with valid arrivals, positive task costs, and arrival curves
      with positive steps, ... *)
  Variable ts : seq Task.
  Hypothesis H_valid_task_set : task_set_with_valid_arrivals ts.
  Hypothesis H_all_tsk_positive_cost : forall tsk, tsk \in ts -> 0 < task_cost tsk.
  Hypothesis H_all_tsk_positive_step :
    forall tsk, tsk \in ts -> fst (head (0,0) (steps_of (get_arrival_curve_prefix tsk))) > 0.

  (** ... and a task belonging to [ts]. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** First, we show that the earliest-deadline-first search space is a generalization of
      the fixed-priority search space. *)
  Lemma EDF_ss_generalize_FP_ss :
    task_search_space_emax_EDF_h
      tsk tsk 0 ((L + (task_deadline tsk - task_deadline tsk)) %/ get_horizon_of_task tsk).+1
    = search_space_emax_FP L tsk.
  Proof.
    rewrite /task_search_space_emax_EDF_h /search_space_emax_FP /search_space_emax_FP_h.
    rewrite subnn addn0.
    set (S := repeat_steps_with_offset _ _) in *.
    replace (shift_points_neg _ _) with S; first by done.
    symmetry; unfold shift_points_neg, shift_points_pos.
    elim: S => [//|a S IHS].
    rewrite //= leq_addr //= IHS.
    by replace ( _ + _ - _) with a; last lia.
  Qed.

  (** Finally, we show that the abstract RTA's standard search space is a subset of the
      computation-oriented version defined above. *)
  Lemma search_space_subset_EDF :
    forall A, A \in correct_search_space ts tsk L -> A \in search_space_emax_EDF ts tsk L.
  Proof.
    move=> A; unfold correct_search_space, is_in_search_space.
    rewrite mem_filter => /andP [/andP [LT /orP [CH|CH]] IN]; unfold search_space_emax_EDF.
    { move: (H_tsk_in_ts) => INTS.
      apply in_cat in INTS; destruct INTS as [ts_l [ts_r EQ]].
      rewrite EQ; rewrite big_cat big_cons //= !mem_cat; apply/orP; right; apply/orP; left.
      unfold task_search_space_emax_EDF; rewrite EDF_ss_generalize_FP_ss.
      by eapply task_search_space_subset; eauto. }
    { move: CH => /hasP [tsko INts /andP [NEQtsk NEQ]].
      apply in_cat in INts; destruct INts as [ts_l [ts_r EQ]]; subst.
      have INts:tsko \in ts_l++[::tsko]++ts_r by rewrite !mem_cat mem_seq1; apply/orP;right;apply/orP;left.
      rewrite big_cat big_cons //= !mem_cat; apply/orP; right; apply/orP; left; apply/mapP.
      exists A.+1; last by lia.
      apply /mapP; exists (A.+1 + task_deadline tsk); last by rewrite -addnBA // subnn addn0.
      rewrite mem_filter; apply/andP; split; first by lia.
      have AD : task_deadline tsko <= A + task_deadline tsk.
      { move_neq_up CONTR.
        have Z1 : A + task_deadline tsk - task_deadline tsko = 0 by lia.
        have Z2 : A + 1 + task_deadline tsk - task_deadline tsko = 0 by lia.
        by rewrite Z1 Z2 eq_refl in NEQ. }
      apply /mapP; exists (A.+1 + task_deadline tsk - task_deadline tsko); last by rewrite subnKC; lia.
      set rto := repeat_steps_with_offset; set ght := get_horizon_of_task.
      have IN_RTO : forall B L', (B \in search_space_emax_FP L' tsko) ->
                            B.+1 \in rto tsko [seq ght tsko * i | i <- iota 0 (L' %/ ght tsko).+1].
      { move =>  B L' /mapP [C INC EQC].
        have POS : C > 0 by eapply nonshifted_offsets_are_positive; eauto 2.
        by rewrite EQC prednK.  }
      destruct (leqP (task_deadline tsko) (task_deadline tsk)) as [EE|EE].
      { rewrite -addnBA //; rewrite -!addnBA // -addnA[1+_] addnC addnA in NEQ.
        rewrite -addn1 -addnA [1 + _ ]addnC addnA addn1.
        set (B := A + (task_deadline tsk - task_deadline tsko)) in *.
        have  CH : task_rbf_changes_at tsko B; [ done | clear NEQ ].
        have LTB : B < L + (task_deadline tsk - task_deadline tsko) by unfold B; lia.
        by apply IN_RTO; last by eapply task_search_space_subset; eauto. }
      { apply ltnW in EE.
        rewrite -subnBA//-subnBA//-addnBAC in NEQ; last by rewrite /concept.task_deadline /TaskDeadline; lia.
        rewrite -subnBA // -addn1 -addnBAC //; last by lia.
        set (B := A - (task_deadline tsko - task_deadline tsk)) in *.
        have  CH : task_rbf_changes_at tsko B; [ done | clear NEQ ].
        replace (task_deadline tsk - task_deadline tsko) with 0; [rewrite addn0 addn1 |lia].
        by apply IN_RTO; last eapply task_search_space_subset; eauto 2; unfold B; lia. } }
  Qed.

End FastSearchSpaceComputationSubset.
