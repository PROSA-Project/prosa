Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.abstract.search_space.
Require Export prosa.analysis.definitions.blocking_bound_fp.


(** * Abstract Search Space is a Subset of Restricted Supply FP Search Space *)

(** A response-time analysis usually involves solving the
    response-time equation for various relative arrival times
    (w.r.t. the beginning of the corresponding busy interval) of a job
    under analysis. To reduce the time complexity of the analysis, the
    state of the art uses the notion of a search space. Intuitively,
    this corresponds to all "interesting" arrival offsets that the job
    under analysis might have with regard to the beginning of its busy
    window.

    In this file, we prove that the search space derived from the aRTA
    theorem is a subset of the search space for the FP scheduling
    policy with restricted supply. In other words, by solving the
    response-time equation for points in the FP search space, one also
    checks all points in the aRTA search space, which makes FP
    compatible with aRTA w.r.t. the search space. *)
Section SearchSpaceSubset.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** Consider an FP policy that indicates a higher-or-equal priority
      relation. *)
  Context {FP : FP_policy Task}.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : list Task.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e.,
      for any task [tsk] in [ts] [max_arrival tsk] is (1) an arrival
      bound of [tsk], and (2) it is a monotonic function that equals
      [0] for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve :
    valid_taskset_arrival_curve ts max_arrivals.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.
  Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.

  (** Let [L] be any positive constant. Typically, [L] denotes an
      upper bound on the length of a busy interval of a [tsk]'s upper
      bound on the length of a busy interval of any job of [tsk]. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.

  (** For the fixed-priority scheduling policy, the search space is
      defined as the set of offsets below [L] where the RBF of the
      task under analysis makes a step. *)
  Definition is_in_search_space A :=
    (A < L) && (task_rbf A != task_rbf (A + ε)).

  (** To rule out pathological cases with the search space, we assume
      that the task cost is positive and the arrival curve is
      non-pathological. *)
  Hypothesis H_task_cost_pos : 0 < task_cost tsk.
  Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

  (** For brevity, let us introduce a shorthand for an intra-IBF (used
      by aRTA). The abstract search space is derived via intra-IBF. *)
  Let intra_IBF (tsk : Task) (A F : duration) :=
    task_rbf (A + ε) - task_cost tsk
    + (blocking_bound ts tsk + total_ohep_rbf F).

  (** Then, abstract RTA's standard search space is a subset of the
      computation-oriented version defined above. *)
  Lemma search_space_sub :
    forall A,
      search_space.is_in_search_space tsk L intra_IBF A ->
      is_in_search_space A.
  Proof.
    move => A [ZERO|[/andP [GTA LTA]] [x [LTx NEQ]]]; rewrite /is_in_search_space.
    { subst; rewrite H_L_positive //=.
      rewrite /task_rbf task_rbf_0_zero // eq_sym -lt0n add0n.
      exact: task_rbf_epsilon_gt_0.
    }
    { rewrite LTA //=; move: NEQ => /neqP; rewrite neq_ltn => /orP [LT|LT].
      { rewrite ltn_add2r in LT.
        have F : forall a b c, a - c < b - c -> a < b by clear; lia.
        apply F in LT; rewrite subnK in LT => //.
        by rewrite neq_ltn; apply/orP; left.
      }
      { rewrite ltn_add2r in LT.
        have F : forall a b c, a - c < b - c -> a < b by clear; lia.
        apply F in LT; rewrite subnK in LT => //.
        by rewrite neq_ltn; apply/orP; right.
      }
    }
  Qed.

End SearchSpaceSubset.
