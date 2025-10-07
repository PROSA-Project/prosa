Require Export prosa.analysis.facts.model.ideal_uni_exceed.
Require Export prosa.analysis.definitions.sbf.sbf.
Require Export prosa.analysis.definitions.sbf.busy.
Require Export prosa.model.processor.ideal_uni_exceed.

(** In this file, we instantiate the supply-bound function for ideal uniprocessors
    with exceedance. *)

(** Let us state the definition first. *)
Section SBFDefinition.

  (** Let [e] be the bound on exceedance in any busy window. *)
  Variable e : work.
  (** Then, the SBF is defined as follows. *)
  Definition eps_sbf (Δ : nat) : work := Δ - e.

End SBFDefinition.

(** Next, we establish some facts about the above-defined [SBF]. *)
Section SBFFacts.

  (** Consider tasks characterized by _nominal_ execution times ... *)
  Context {Task : TaskType} `{TaskCost Task}.

  (** ... and their associated jobs with costs and arrival times. *)
  Context {Job : JobType} `{JobTask Job Task}
          `{JobCost Job} `{JobArrival Job}.

  (** Consider any JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** Assume an arrival sequence ...*)
  Variable arr_seq : arrival_sequence Job.

  (** ... and a corresponding ideal uniprocessor schedule subject to exceedance. *)
  Variable sched : schedule (exceedance_proc_state Job).

  (** Assume [e] is the bound on exceedance in a busy interval ... *)
  Variable e : work.

  (** ... of a given task [tsk]. *)
  Variable tsk : Task.

  (** Let us state the exceedance using [Instance] to make it locally available
      to the typeclasses database. *)
  #[local] Instance EPS_SBF_inst : SupplyBoundFunction := eps_sbf e.

  (** Let us formally state the assumption that the total exceedance inside
      the busy interval of [tsk] is bounded by [e]. *)
  Hypothesis H_exceedance_in_busy_interval_bounded :
    forall j t1 t2,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
        busy_interval_prefix arr_seq sched j t1 t2 ->
        \sum_(t1 <= t < t2) is_exceedance_exec (sched t) <= e.

  (** Since we model exceedance as blackouts, we trivially have that the
      blackouts are bounded by [e]. *)
  Lemma blackout_during_bounded j t1 t2 t :
    arrives_in arr_seq j ->
    job_of_task tsk j ->
    busy_interval_prefix arr_seq sched j t1 t2  ->
    t1 <= t <= t2 ->
    blackout_during sched t1 t <= e.
  Proof.
    move => ARRIN TSK PRE /andP[INEQ1 INEQ2].
    rewrite /blackout_during.
    rewrite (eq_sum_seq _ _ _ _ (fun t => is_exceedance_exec (sched t))).
    - specialize ( H_exceedance_in_busy_interval_bounded j t1 t2 ).
      feed_n 3 H_exceedance_in_busy_interval_bounded => //=.
      apply: leq_trans; last by apply H_exceedance_in_busy_interval_bounded.
      rewrite (big_cat_nat _ INEQ2) //=.
      by lia.
    -  move => t' /[!mem_index_iota]IN _.
       rewrite blackout_implies_exceedance_execution.
       by apply /eqP.
  Qed.

  (** Using the above, we can prove that our definition of SBF is valid. *)
  Lemma eps_sbf_is_valid : valid_busy_sbf arr_seq sched tsk EPS_SBF_inst.
  Proof.
    rewrite /valid_busy_sbf /valid_pred_sbf /EPS_SBF_inst /eps_sbf //=.
    split; first lia.
    rewrite /pred_sbf_respected => j t1 t2 ARRIN [TSK BUSYPREFIX] t LEQ.
    have Hsplit : t = t1 + (t - t1) by lia.
    rewrite Hsplit.
    have -> : t1 + (t - t1) - t1 - e = (t - t1) - e by lia.
    set (Δ := (t - t1)) in *.
    have ? : Δ - supply_during sched t1 (t1 + Δ) <= e; try lia.
    rewrite -blackout_during_complement //=.
    apply: blackout_during_bounded => //=.
    by lia.
  Qed.

  (** Finally, we prove that our SBF only takes steps of one unit. *)
  Lemma eps_sbf_is_unit : unit_supply_bound_function EPS_SBF_inst.
  Proof.
    rewrite /unit_supply_bound_function => Δ.
    rewrite /EPS_SBF_inst /eps_sbf //=.
    by lia.
  Qed.

End SBFFacts.
