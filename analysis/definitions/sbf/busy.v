Require Export prosa.util.all.
Require Export prosa.analysis.definitions.sbf.pred.
Require Export prosa.analysis.definitions.busy_interval.classical.

(** * SBF within Busy Interval *)

(** In the following, we define a weak notion of a supply-bound
    function, which is a valid SBF only within a busy interval of a
    task's job. *)
Section BusySupplyBoundFunctions.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (** ... and any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobTask Job Task}.

  (** Consider any kind of processor state model, ... *)
  Context `{PState : ProcessorState Job}.

  (** ... any valid arrival sequence, and ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... any schedule. *)
  Variable sched : schedule PState.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** Consider a task [tsk]. *)
  Variable tsk : Task.

  (** We define a predicate that determines whether an interval <<[t1,
      t2)>> is a busy-interval prefix of a job [j] of task [tsk]. *)
  Let bi_prefix_of_tsk j t1 t2 :=
    job_of_task tsk j /\ busy_interval_prefix arr_seq sched j t1 t2.

  (** We say that the SBF is respected in a busy interval w.r.t. task
      [tsk] if, for any busy interval <<[t1, t2)>> of a job [j ∈ tsk]
      and a subinterval <<[t1, t) ⊆ [t1, t2)>>, at least [SBF (t -
      t1)] cumulative supply is provided. *)
  Definition sbf_respected_in_busy_interval (SBF : duration -> work) :=
    pred_sbf_respected arr_seq sched bi_prefix_of_tsk SBF.

  (** Next, we define an SBF that is valid within a busy interval. *)
  Definition valid_busy_sbf (SBF : duration -> work) :=
    valid_pred_sbf arr_seq sched bi_prefix_of_tsk SBF.

End BusySupplyBoundFunctions.
