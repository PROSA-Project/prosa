Require Export prosa.util.all.
Require Export prosa.model.task.arrival.curves.
Require Export prosa.analysis.facts.sporadic.arrival_bound.

(** Arrival Curve for Sporadic Tasks *)

(** Any analysis that supports arbitrary arrival curves can also be
    used to analyze sporadic tasks. We establish this link below. *)
Section SporadicArrivalCurve.
  (** Consider any type of sporadic tasks. *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** The bound on the maximum number of arrivals in a given interval
      [max_sporadic_arrivals] is in fact a valid arrival curve, which
      we note with the following arrival-curve declaration. *)
  Global Program Instance MaxArrivalsSporadic : MaxArrivals Task := max_sporadic_arrivals.

  (** It remains to be shown that [max_sporadic_arrivals] satisfies
      all expectations placed on arrival curves. First, we observe
      that the bound is structurally sound. *)
  Lemma sporadic_arrival_curve_valid :
    forall tsk,
      valid_arrival_curve (max_sporadic_arrivals tsk).
  Proof.
    move=> tsk; split; first exact: div_ceil0.
    move=> delta1 delta2 LEQ.
    exact: div_ceil_monotone1.
  Qed.

  (** For convenience, we lift the preceding observation to the level
      of entire task sets. *)
  Remark sporadic_task_sets_arrival_curve_valid :
    forall ts,
      valid_taskset_arrival_curve ts max_arrivals.
  Proof. move=> ? ? ?; exact: sporadic_arrival_curve_valid. Qed.

   (** Next, we note that it is indeed an arrival bound. To this end,
       consider any type of jobs stemming from these tasks ... *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** ... and any well-formed arrival sequence of such jobs. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** We establish the validity of the defined curve. *)
  Section Validity.

    (** Let [tsk] denote any valid sporadic task to be analyzed. *)
    Variable tsk : Task.
    Hypothesis H_sporadic_model : respects_sporadic_task_model arr_seq tsk.
    Hypothesis H_valid_inter_min_arrival : valid_task_min_inter_arrival_time tsk.

    (** We observe that [max_sporadic_arrivals] is indeed an upper bound
        on the maximum number of arrivals. *)
    Lemma sporadic_arrival_curve_respects_max_arrivals :
      respects_max_arrivals arr_seq tsk (max_sporadic_arrivals tsk).
    Proof. by move=> t1 t2 LEQ; apply: sporadic_task_arrivals_bound. Qed.

  End Validity.

  (** For convenience, we lift the preceding observation to the level
      of entire task sets. *)
  Remark sporadic_task_sets_respects_max_arrivals :
    forall ts,
      valid_taskset_inter_arrival_times ts ->
      taskset_respects_sporadic_task_model ts arr_seq ->
      taskset_respects_max_arrivals arr_seq ts.
  Proof.
    move=> ts VAL SPO tsk IN.
    apply: sporadic_arrival_curve_respects_max_arrivals.
    - exact: SPO.
    - exact: VAL.
  Qed.

End SporadicArrivalCurve.

(** We add the lemmas into the "Hint Database" basic_rt_facts so that
    they become available for proof automation. *)
Global Hint Resolve
  sporadic_arrival_curve_valid
  sporadic_task_sets_arrival_curve_valid
  sporadic_arrival_curve_respects_max_arrivals
  sporadic_task_sets_respects_max_arrivals
  : basic_rt_facts.
