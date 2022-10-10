Require Export prosa.util.nat.
Require Export prosa.analysis.abstract.definitions.

(** * Auxiliary Lemmas About Interference and Interfering Workload. *)

(** In this file we provide a set of auxiliary definitions and lemmas
    about generic properties of Interference and Interfering
    Workload. *)
Section InterferenceAndInterferingWorkloadAuxiliary.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** First, we show that cumulative interference on an interval
      <<[al, ar)>> is bounded by the cumulative interference on an
      interval <<[bl,br)>> if <<[al,ar)>> ⊆ <<[bl,br)>>. *)
  Lemma cumulative_interference_sub :
    forall (j : Job) (al ar bl br : instant),
      bl <= al ->
      ar <= br ->
      cumulative_interference j al ar <= cumulative_interference j bl br.
  Proof.
    move => j al ar bl br LE1 LE2.
    destruct (leqP al ar) as [NEQ|NEQ].
    - rewrite /cumulative_interference /definitions.cumulative_interference.
      rewrite [in X in _ <= X](@big_cat_nat _ _ _ al) //=; try lia.
      by rewrite [in X in _ <= _ + X](@big_cat_nat _ _ _ ar) //=; lia.
    - by rewrite /cumulative_interference /definitions.cumulative_interference big_geq; lia.
  Qed.

  (** We show that the cumulative interference of a job can be split
      into disjoint intervals. *)
  Lemma cumulative_interference_cat :
    forall j t t1 t2,
      t1 <= t <= t2 ->
      cumulative_interference j t1 t2 = cumulative_interference j t1 t + cumulative_interference j t t2.
  Proof.
    move => j t t1 t2 /andP [LE1 LE2].
    rewrite /cumulative_interference /definitions.cumulative_interference.
    by rewrite {1}(@big_cat_nat _ _ _ t) //=.
  Qed.

End InterferenceAndInterferingWorkloadAuxiliary.
