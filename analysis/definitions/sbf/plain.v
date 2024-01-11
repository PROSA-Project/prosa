Require Export prosa.util.all.
Require Export prosa.analysis.definitions.sbf.pred.

(** * Plain Supply Bound Functions (SBFs) *)

(** ** Parameter Semantics *)

(** In the following, we define the semantics of the classical supply
    bound functions (SBF). *)
Section SupplyBoundFunctions.

  (** Consider any type of jobs, ... *)
  Context {Job : JobType}.

  (** ... any kind of processor state model, ... *)
  Context `{PState : ProcessorState Job}.

  (** ... any valid arrival sequence, and ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... any schedule. *)
  Variable sched : schedule PState.

  (** We say that the SBF is respected if, for any time interval <<[t1, t2)>>,
      at least [SBF (t2 - t1)] cumulative supply is provided within the given
      interval. In other words, the SBF lower-bounds the provided supply. *)
  Definition supply_bound_function_respected (SBF : duration -> work) :=
    pred_sbf_respected arr_seq sched (fun _ _ _ => True) SBF.

  (** We say that a plain SBF is valid iff it is valid w.r.t. a
      predicate that is always true (i.e., [fun _ _ _ => True]). *)
  Definition valid_supply_bound_function (SBF : duration -> work) :=
    valid_pred_sbf arr_seq sched (fun _ _ _ => True) SBF.

  (** Suppose we are given an SBF characterizing the schedule. *)
  Context {SBF : SupplyBoundFunction}.

  (** Note that the predicate [(fun _ _ _ => True)] can be easily discarded. *)
  Remark sbf_respected_simplified :
    supply_bound_function_respected SBF ->
    forall (j : Job) (t1 t2 : instant),
      arrives_in arr_seq j ->
      t1 <= t2 ->
      SBF (t2 - t1) <= supply_during sched t1 t2.
  Proof.
    move => SUP j t1 t2 ARR LE.
    by apply: (SUP _ _ t2) => //; lia.
  Qed.

End SupplyBoundFunctions.
