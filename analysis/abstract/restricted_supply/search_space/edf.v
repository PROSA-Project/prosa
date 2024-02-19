Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.abstract.search_space.
Require Export prosa.analysis.definitions.blocking_bound.edf.
Require Export prosa.analysis.facts.workload.edf_athep_bound.

(** * Abstract Search Space is a Subset of Restricted Supply EDF Search Space *)

(** A response-time analysis usually involves solving the
    response-time equation for various relative arrival times
    (w.r.t. the beginning of the corresponding busy interval) of a job
    under analysis. To reduce the time complexity of the analysis, the
    state of the art uses the notion of a search space. Intuitively,
    this corresponds to all "interesting" arrival offsets that the job
    under analysis might have with regard to the beginning of its busy
    window.

    In this file, we prove that the search space derived from the aRSA
    theorem is a subset of the search space for the EDF scheduling
    policy with restricted supply. In other words, by solving the
    response-time equation for points in the EDF search space, one
    also checks all points in the aRTA search space, which makes EDF
    compatible with aRTA w.r.t. the search space. *)
Section SearchSpaceSubset.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : seq Task.

  (** Let [max_arrivals] be a family of valid arrival curves. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve :
    valid_taskset_arrival_curve ts max_arrivals.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Let [L] be an arbitrary positive constant. Normally, [L] denotes
      an upper bound on the length of a busy interval of a job of
      [tsk]. In this file, however, [L] can be any positive
      constant. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.

  (** For brevity, let's denote the relative deadline of a task as D. *)
  Let D tsk := task_deadline tsk.

  (** We introduce [rbf] as an abbreviation of the task request bound function. *)
  Let rbf := task_request_bound_function.

  (** To reduce the time complexity of the analysis, we introduce the
      notion of a search space for EDF. Intuitively, this corresponds
      to all "interesting" arrival offsets that the job under analysis
      might have with regard to the beginning of its busy window. *)

  (** In the case of the search space for EDF, we consider three
      conditions. First, we ask whether [task_rbf A ≠ task_rbf (A +
      ε)]. *)
  Let task_rbf_changes_at (A : duration) :=
    rbf tsk A != rbf tsk (A + ε).

  (** Second, we ask whether there exists a task [tsko] from [ts] such
      that [tsko ≠ tsk] and [rbf(tsko, A + D tsk - D tsko) ≠ rbf(tsko,
      A + ε + D tsk - D tsko)]. *)
  Let bound_on_total_hep_workload_changes_at (A : duration) :=
    let new_hep_job_released_by tsko :=
      (tsk != tsko) && (rbf tsko (A + D tsk - D tsko) != rbf tsko ((A + ε) + D tsk - D tsko))
    in has new_hep_job_released_by ts.

  (** Third, we ask whether [blocking_bound (A - ε) ≠ blocking_bound A]. *)
  Let blocking_bound_changes_at (A : duration) :=
    blocking_bound ts tsk (A - ε) != blocking_bound ts tsk A.

  (** The final search space for EDF is the set of offsets less
      than [L] and where [priority_inversion_bound], [task_rbf], or
      [bound_on_total_hep_workload] changes in value. *)
  Definition is_in_search_space (A : duration) :=
    (A < L) && (blocking_bound_changes_at A
                || task_rbf_changes_at A
                || bound_on_total_hep_workload_changes_at A).

  (** To rule out pathological cases with the search space, we assume
      that the task cost is positive and the arrival curve is
      non-pathological. *)
  Hypothesis H_task_cost_pos : 0 < task_cost tsk.
  Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

  (** For brevity, let us introduce a shorthand for an intra-IBF. The
      abstract search space is derived via intra-IBF. *)
  Let intra_IBF (A F : duration) :=
    rbf tsk (A + ε) - task_cost tsk
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
      rewrite /task_rbf_changes_at /rbf task_rbf_0_zero // eq_sym -lt0n add0n.
      by apply task_rbf_epsilon_gt_0 => //.
    }
    { apply contraT; rewrite !negb_or => /andP [/andP [/negPn/eqP PI /negPn/eqP RBF]  WL].
      exfalso; apply INSP2.
      rewrite /intra_IBF subnK // RBF.
      apply /eqP; rewrite eqn_add2l PI eqn_add2l.
      rewrite /bound_on_athep_workload subnK //.
      apply /eqP; rewrite big_seq_cond [RHS]big_seq_cond.
      apply eq_big => // tsk_i /andP [TS OTHER].
      move: WL; rewrite /bound_on_total_hep_workload_changes_at /D => /hasPn WL.
      move: {WL} (WL tsk_i TS) =>  /nandP [/negPn/eqP EQ|/negPn/eqP WL];
                                  first by move: OTHER; rewrite EQ => /neqP.
      case: (ltngtP (A + ε + task_deadline tsk - task_deadline tsk_i) x) => [ltn_x|gtn_x|eq_x]; rewrite /minn.
      { by rewrite ifT //; lia. }
      { rewrite ifF //.
        by move: gtn_x; rewrite leq_eqVlt  => /orP [/eqP EQ|LEQ]; lia. }
      { case: (A + task_deadline tsk - task_deadline tsk_i < x).
        - by rewrite -/rbf WL.
        - by rewrite eq_x. } }
  Qed.

End SearchSpaceSubset.
