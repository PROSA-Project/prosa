Require Export prosa.util.epsilon.
Require Export prosa.model.task.arrival.curves.
Require Export prosa.analysis.facts.model.task_arrivals.

(** * Facts About Arrival Curves *)


(** We observe that tasks that exhibit job arrivals must have non-pathological
    arrival curves. This allows excluding pathological cases in higher-level
    proofs. *)
Section NonPathologicalCurve.

  (** Consider any kind of tasks characterized by an upper-bounding arrival curve... *)
  Context {Task : TaskType} `{MaxArrivals Task}.
  (** ... and the corresponding type of jobs. *)
  Context {Job : JobType} `{JobTask Job Task}.

  (** Consider an arbitrary task ... *)
  Variable tsk : Task.

  (** ... and an arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... that is compliant with the upper-bounding arrival curve. *)
  Hypothesis H_curve_is_valid : respects_max_arrivals arr_seq tsk (max_arrivals tsk).

  (** If we have evidence that a job of the task [tsk] ... *)
  Variable j : Job.
  Hypothesis H_job_of_tsk : job_of_task tsk j.

  (** ... arrives at any point in time, ... *)
  Hypothesis H_arrives : arrives_in arr_seq j.

  (** ... then the maximum number of job arrivals in a non-empty interval cannot
      be zero. *)
  Lemma non_pathological_max_arrivals :
    max_arrivals tsk ε > 0.
  Proof.
    move: (H_arrives) => [t ARR].
    move: (H_curve_is_valid t t.+1 ltac:(by done)).
    rewrite -addn1 -addnBAC // addnBl_leq // => VALID.
    apply: (leq_trans _ VALID).
    rewrite /number_of_task_arrivals size_of_task_arrivals_between.
    rewrite big_ltn addn1 // big_geq // addn0.
    rewrite /task_arrivals_at size_filter //= -has_count.
    by apply /hasP; exists j.
  Qed.

End NonPathologicalCurve.
