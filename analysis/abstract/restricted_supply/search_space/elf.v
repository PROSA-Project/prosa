Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.abstract.search_space.
Require Export prosa.analysis.definitions.blocking_bound.elf.
Require Export prosa.analysis.facts.workload.elf_athep_bound.

(** * Abstract Search Space is a Subset of Restricted Supply ELF Search Space *)
Section SearchSpaceSubset.

  (** Consider any type of tasks with relative priority points. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.
  Context `{PriorityPoint Task}.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : seq Task.

  (** Let [max_arrivals] be a family of valid arrival curves. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve :
    valid_taskset_arrival_curve ts max_arrivals.

  (** Consider any FP policy. *)
  Context {FP : FP_policy Task}.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Let [L] be an arbitrary positive constant. Normally, [L] denotes
      an upper bound on the length of a busy interval of a job of
      [tsk]. In this file, however, [L] can be any positive
      constant. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.

  (** We introduce [task_rbf] as an abbreviation of the task request bound function. *)
  Let task_rbf := task_request_bound_function tsk.

  (** To reduce the time complexity of the analysis, we introduce the
      notion of a search space for ELF. Intuitively, this corresponds
      to all "interesting" arrival offsets that the job under analysis
      might have with regard to the beginning of its busy window. *)

  (** In the case of the search space for ELF, we consider three
      conditions.

      First, we ask whether [rbf A ≠ rbf (A + ε)]. *)
  Let task_rbf_changes_at (A : duration) :=
    task_rbf A != task_rbf (A + ε).

  (** Second, we limit our search space to those arrival offsets where
      the bound on higher-or-equal priority workload changes in value.

      Since the bound on workload from higher priority task does not depend
      on the arrival offset [A], we are only concerned about the workload from
      equal priority tasks.
      For this, we ask whether there exists a task [tsko ≠ tsk] in task set [ts]
      such that
     [ep_task_interfering_interval_length tsk tsko (A - ε) != ep_task_interfering_interval_length tsk tsko A]. *)
  Let bound_on_ep_task_workload_changes_at (A : duration) :=
    let new_hep_job_released_by tsko :=
      (ep_task tsk tsko) && (tsko != tsk)
      && (ep_task_interfering_interval_length tsk tsko (A - ε) != ep_task_interfering_interval_length tsk tsko A)
    in has new_hep_job_released_by ts.

  (** Third, we ask whether [blocking_bound (A - ε) ≠ blocking_bound A]. *)
  Let blocking_bound_changes_at (A : duration) :=
    blocking_bound ts tsk (A - ε) != blocking_bound ts tsk A.

  (** The final search space for ELF is the set of offsets less
      than [L] and where [task_rbf], [blocking_bound] or
      [bound_on_ep_task_workload] changes in value. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && (blocking_bound_changes_at A
                || task_rbf_changes_at A
                || bound_on_ep_task_workload_changes_at A).

  (** To rule out pathological cases with the search space, we assume
      that the task cost is positive and the arrival curve is
      non-pathological. *)
  Hypothesis H_task_cost_pos : 0 < task_cost tsk.
  Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

  (** For brevity, let us introduce a shorthand for an intra-IBF. The
      abstract search space is derived via intra-IBF. *)
  Let intra_IBF (A F : duration) :=
    task_rbf (A + ε) - task_cost tsk
    + (blocking_bound ts tsk A + bound_on_athep_workload ts tsk A F).

  (** Then, abstract RTA's standard search space is a subset of the
      computation-oriented version defined above. *)
  Lemma search_space_sub :
    forall A,
      abstract.search_space.is_in_search_space L intra_IBF A ->
      is_in_search_space A.
  Proof.
    move => A [-> | [/andP [POSA LTL] [x [LTx INSP2]]]]; apply/andP; split => //.
    { apply/orP; left; apply/orP; right.
      rewrite /task_rbf_changes_at /task_rbf task_rbf_0_zero //=.
      { rewrite eq_sym -lt0n add0n.
        by apply task_rbf_epsilon_gt_0 => //. } }
    { apply contraT; rewrite !negb_or => /andP [/andP [/negPn/eqP PI /negPn/eqP RBF]  WL].
      exfalso; apply INSP2.
      rewrite /intra_IBF subnK // RBF.
      apply /eqP; rewrite eqn_add2l PI eqn_add2l.
      rewrite /bound_on_athep_workload /bound_on_ep_task_workload /bound_on_hp_task_workload /ep_task_interfering_interval_length.
      rewrite subnK //.
      rewrite eqn_add2l.
      apply /eqP; rewrite big_seq_cond [RHS]big_seq_cond.
      apply eq_big => // tsk_i /andP [TS OTHER].
      move: WL.
      rewrite /bound_on_ep_task_workload_changes_at /ep_task_interfering_interval_length => /hasPn WL.
      move: {WL} (WL tsk_i TS) =>  /nandP [/negbTE EQ|/negPn/eqP WL].
      { by move: OTHER; rewrite EQ. }
      have [leq_x|gtn_x] := leqP `|Num.max 0%R (ep_task_interfering_interval_length tsk tsk_i A)| x.
      { move: WL.
        rewrite subnK // /task_rbf => WL.
        by rewrite WL (minn_idPl leq_x). }
      move: WL.
      rewrite subnK // /task_rbf => WL.
      by rewrite WL (minn_idPr (ltnW gtn_x)). }
  Qed.

End SearchSpaceSubset.
