Require Export prosa.results.fixed_priority.rta.bounded_nps.
Require Export prosa.implementation.refinements.fast_search_space_computation.

(** Throughout this file, we work with Prosa's fixed-priority policy implementation. *)
#[local] Existing Instance NumericFPAscending.

(** First, we define the concept of higher-or-equal-priority and different task, ...  *)
Definition ohep_task (tsk1 : Task) (tsk2 : Task) :=
  hep_task tsk1 tsk2 && (tsk1 != tsk2).

(** ... cumulative request-bound function for higher-or-equal-priority tasks
        (including the task under analysis), ...  *)
Definition total_hep_rbf (ts : seq Task) (tsk : Task) (Δ : duration) :=
  total_hep_request_bound_function_FP ts tsk Δ.

(** ... and an analogous definition that does not include the task under analysis. *)
Definition total_ohep_rbf (ts : seq Task) (tsk : Task) (Δ : duration) :=
  total_ohep_request_bound_function_FP ts tsk Δ.

(** Next, we provide a function that checks a single point [P=(A,F)] of the search space
    when adopting a fully-preemptive policy. *)
Definition check_point_FP (ts : seq Task) (tsk : Task) (R : nat) (P : nat * nat) :=
  (task_rbf tsk (P.1 + ε) + total_ohep_rbf ts tsk (P.1 + P.2) <= P.1 + P.2) && (P.2 <= R).

(** Further, we provide a way to compute the blocking bound when using nonpreemptive policies. *)
Definition blocking_bound_NP (ts : seq Task) (tsk : Task) :=
  \max_(tsk_other <- ts | ~~ hep_task tsk_other tsk) (concept.task_cost tsk_other - ε).

(** Finally, we provide a function that checks a single point [P=(A,F)] of the search space when
    adopting a fully-nonpreemptive policy. *)
Definition check_point_NP (ts : seq Task) (tsk : Task) (R : nat) (P : nat * nat) :=
  (blocking_bound_NP ts tsk
   + (task_rbf tsk (P.1 + ε) - (concept.task_cost tsk - ε))
   + total_ohep_rbf ts tsk (P.1 + P.2) <= P.1 + P.2)
  && (P.2 + (concept.task_cost tsk - ε) <= R).

(** * Search Space Definitions *)

(** First, we recall the notion of correct search space as defined by
    abstract RTA. *)
Definition correct_search_space (tsk : Task) (L : duration) :=
  [seq A <- iota 0 L | is_in_search_space tsk L A].

(** Next, we provide a computation-oriented way to compute abstract RTA's search space. We
    start with a function that computes the search space in a generic interval <<[a,b)>>, ... *)
Definition search_space_emax_FP_h (tsk : Task) a b :=
  let h := get_horizon_of_task tsk in
  let offsets := map (muln h) (iota a b) in
  let emax_offsets := repeat_steps_with_offset tsk offsets in
  map predn emax_offsets.

(** ... which we then apply to the interval <<[0, (L %/h).+1)>>.  *)
Definition search_space_emax_FP (tsk : Task) (L : duration) :=
  let h := get_horizon_of_task tsk in
  search_space_emax_FP_h tsk 0 (L %/h).+1.

(** In this section, we prove that the computation-oriented search space defined above
    contains each of the points contained in abstract RTA's standard definition. *)
Section FastSearchSpaceComputationSubset.

  (** Consider a given maximum busy-interval length [L], ... *)
  Variable L : duration.

  (** ... a task set with valid arrivals, ... *)
  Variable ts : seq Task.
  Hypothesis H_valid_arrivals : task_set_with_valid_arrivals ts.

  (** ... and a task belonging to [ts] with positive cost. *)
  Variable tsk : Task.
  Hypothesis H_positive_cost : 0 < task_cost tsk.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Then, abstract RTA's standard search space is a subset of the computation-oriented
      version defined above. *)
  Lemma search_space_subset_FP :
    forall A, A \in correct_search_space tsk L -> A \in search_space_emax_FP tsk L.
  Proof.
    move=> A IN.
    move: IN; rewrite mem_filter => /andP[/andP[LEQ_L NEQ] _].
    by apply (task_search_space_subset _ ts) => //.
  Qed.

End FastSearchSpaceComputationSubset.
