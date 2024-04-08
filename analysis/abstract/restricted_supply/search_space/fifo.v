Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.abstract.search_space.
Require Import prosa.analysis.facts.priority.fifo.
Require Import prosa.analysis.definitions.sbf.pred.

(** * The Abstract Search Space is a Subset of the FIFO Search Space *)

(** A response-time analysis usually involves solving the
    response-time equation for various relative arrival times
    (w.r.t. the beginning of the corresponding busy interval) of a job
    under analysis. To reduce the time complexity of the analysis, the
    state of the art uses the notion of a search space. Intuitively,
    this corresponds to all "interesting" arrival offsets that the job
    under analysis might have with regard to the beginning of its busy
    window.

    In this file, we prove that the search space derived from the aRTA
    theorem is a subset of the search space for the FIFO scheduling
    policy with restricted supply. In other words, by solving the
    response-time equation for points in the FIFO search space, one also
    checks all points in the aRTA search space, which makes FIFO
    compatible with aRTA w.r.t. the search space. *)
Section SearchSpaceSubset.

  (** Consider a restricted-supply uniprocessor model where the
      minimum amount of supply is defined via a monotone
      unit-supply-bound function [SBF]. *)
  Context {SBF : SupplyBoundFunction}.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** Consider an arbitrary task set [ts]. *)
  Variable ts : seq Task.

  (** Let [max_arrivals] be a family of valid arrival curves, i.e.,
      for any task [tsk] in [ts] [max_arrival tsk] is (1) an arrival
      bound of [tsk], and (2) it is a monotonic function that equals
      [0] for the empty interval [delta = 0]. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve :
    valid_taskset_arrival_curve ts max_arrivals.

  (** For brevity, let's denote the request-bound function of a task
      as [rbf]. *)
  Let rbf tsk := task_request_bound_function tsk.

  (** Let [L] be an arbitrary positive constant. Typically, [L]
      denotes an upper bound on the length of a busy interval of a job
      of [tsk]. In this file, however, [L] can be any positive
      constant. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.

  (** In the case of [FIFO], the concrete search space is the set of
      offsets less than [L] such that there exists a task [tsk] in
      [ts] such that [rbf tsk (A) ≠ rbf tsk (A + ε)]. *)
  Definition is_in_search_space (A : duration) :=
    let rbf_makes_a_step tsk := rbf tsk A != rbf tsk (A + ε) in
    (A < L) && has rbf_makes_a_step ts.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** To rule out pathological cases with the search space, we assume
      that the task cost is positive and the arrival curve is
      non-pathological. *)
  Hypothesis H_task_cost_pos : 0 < task_cost tsk.
  Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

  (** For brevity, let us introduce a shorthand for an IBF (used by
      aRTA). The abstract search space is derived via IBF. *)
  Local Definition IBF (A F : duration) :=
    (F - SBF F) + (total_request_bound_function ts (A + ε) - task_cost tsk).

  (** Then, abstract RTA's standard search space is a subset of the
      computation-oriented version defined above. *)
  Lemma search_space_sub :
    forall A,
      abstract.search_space.is_in_search_space L IBF A ->
      is_in_search_space A.
  Proof.
    move => A [INSP | [/andP [POSA LTL] [x [LTx INSP2]]]].
    { subst A.
      apply/andP; split=> [//|].
      apply /hasP; exists tsk => [//|].
      rewrite neq_ltn; apply/orP; left.
      rewrite /rbf task_rbf_0_zero // add0n.
      by apply task_rbf_epsilon_gt_0 => //.
    }
    { apply /andP; split=> [//|].
      apply /hasPn => EQ2.
      rewrite /IBF in INSP2; rewrite /total_request_bound_function.
      rewrite subnK in INSP2 => //.
      apply INSP2; clear INSP2.
      have ->// : total_request_bound_function ts A = total_request_bound_function ts (A + ε).
      apply eq_big_seq => //= task IN.
      by move: (EQ2 task IN) => /negPn /eqP. }
  Qed.

End SearchSpaceSubset.
