Require Export prosa.model.priority.fifo.
Require Export prosa.model.task.preemption.parameters.
Require Export prosa.analysis.definitions.sbf.busy.
Require Export prosa.analysis.abstract.restricted_supply.search_space.fifo.

(** * Concrete to Abstract Fixpoint Reduction *)

(** In this file, we show that a solution to a concrete fixpoint
    equation under the FIFO policy implies a solution to the
    abstract fixpoint equation required by aRSA. *)
Section ConcreteToAbstractFixpointReduction.

  (** Consider any type of tasks, each characterized by a WCET
      [task_cost], an arrival curve [max_arrivals], a
      run-to-completion threshold [task_rtct], and a bound on the
      task's maximum non-preemptive segment
      [task_max_nonpreemptive_segment] ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.
  Context `{TaskRunToCompletionThreshold Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** ... and any type of jobs associated with these tasks, where each
      job has a task [job_task], a cost [job_cost], an arrival time
      [job_arrival], and a predicate indicating when the job is
      preemptable [job_preemptable]. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context `{JobPreemptable Job}.

  (** Consider any processor model ... *)
  Context `{PState : ProcessorState Job}.

  (** ... where the minimum amount of supply is defined via a monotone
      unit-supply-bound function [SBF]. *)
  Context {SBF : SupplyBoundFunction}.
  Hypothesis H_SBF_monotone : sbf_is_monotone SBF.
  Hypothesis H_unit_SBF : unit_supply_bound_function SBF.

  (** We consider an arbitrary task set [ts]. *)
  Variable ts : seq Task.

  (** Let [tsk] be any task in [ts] that is to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_tsk_in_ts : tsk \in ts.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and assume that [max_arrivals] defines a valid arrival curve
      for each task. *)
  Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.

  (** Consider any schedule. *)
  Variable sched : schedule PState.

  (** Next, we assume that [SBF] properly characterizes all busy
      intervals (w.r.t. task [tsk]) in [sched]. That is, (1) [SBF 0 =
      0] and (2) for any duration [Δ], at least [SBF Δ] supply is
      available in any busy-interval prefix of length [Δ]. *)
  Hypothesis H_valid_SBF : valid_busy_sbf arr_seq sched tsk SBF.

  (** We assume that [tsk] is described by a valid task
      run-to-completion threshold_ *)
  Hypothesis H_valid_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk.

  (** Let [L] be an arbitrary positive constant. Typically, [L]
      denotes an upper bound on the length of a busy interval of a job
      of [tsk]. In this file, however, [L] can be any positive
      constant. *)
  Variable L : duration.
  Hypothesis H_L_positive : 0 < L.

  (** To rule out pathological cases with the search space, we assume
      that the task cost is positive and the arrival curve is
      non-pathological. *)
  Hypothesis H_task_cost_pos : 0 < task_cost tsk.
  Hypothesis H_arrival_curve_pos : 0 < max_arrivals tsk ε.

  (** For brevity, we define the intra-supply interference bound
      function ([intra_IBF]). Note that in the case of FIFO,
      intra-supply IBF does not depend on the second argument.  *)
  Local Definition intra_IBF (A _Δ : duration) :=
    total_request_bound_function ts (A + ε) - task_cost tsk.

  (** Ultimately, we seek to apply aRSA to prove the correctness of
      the following [R]. *)
  Variable R : duration.
  Hypothesis H_R_is_maximum :
    forall (A : duration),
      is_in_search_space ts L A ->
      exists (F : duration),
        SBF F >= total_request_bound_function ts (A + ε)
        /\ A + R >= F.

  (** However, in order to connect the definition of [R] with aRSA, we
      must first restate the bound in the shape of the abstract
      response-time bound equation that aRSA expects, which we do
      next. *)

  (** We know that:
     - if [A] is in the abstract search space, then it is also in the
       concrete search space; and
     - if [A] is in the concrete search space, then there exists a
       solution that satisfies the inequalities stated in
       [H_R_is_maximum]. Using these facts, we prove that, if [A] is
       in the abstract search space, then there also exists a solution
       [F] to the response-time equation as expected by aRSA. *)
  Lemma soln_abstract_response_time_recurrence :
    forall A : duration,
      abstract.search_space.is_in_search_space L (fifo.IBF ts tsk) A ->
      exists F : duration,
        F <= A + R
        /\ task_rtct tsk + intra_IBF A F <= SBF F
        /\ SBF F + (task_cost tsk - task_rtct tsk) <= SBF (A + R).
  Proof.
    move => A SP; move: (H_R_is_maximum A) => MAX.
    rewrite /intra_IBF.
    feed MAX; first by apply: search_space_sub => //.
    move: MAX => [F' [FE LGL]].
    have Leq1 : SBF F' <= SBF (A + R) by apply H_SBF_monotone; lia.
    have Leq2 : total_request_bound_function ts (A + 1) >= task_cost tsk by apply task_cost_le_sum_rbf => //; lia.
    have Leq3 : task_cost tsk >= task_rtct tsk by apply H_valid_run_to_completion_threshold.
    unfold total_request_bound_function in *.
    have [F'' [LE EX]]:
      exists F'',
        0 <= F'' <= A + R
        /\ SBF F'' = SBF (A + R) - (task_cost tsk - task_rtct tsk).
    { apply exists_intermediate_point_leq.
      - by move=> t; rewrite !addn1; apply H_unit_SBF.
      - lia.
      - apply/andP; split.
        + rewrite (fst H_valid_SBF); lia.
        + lia.
    }
    exists F''; split; last split.
    + by move: LE; clear; lia.
    + by rewrite EX; lia.
    + by rewrite EX; lia.
  Qed.

End ConcreteToAbstractFixpointReduction.
