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

  (** For convenience, we define a function that "folds" cumulative
      conditional interference with a predicate [fun _ _ => true] to
      cumulative (unconditional) interference. *)
  Lemma fold_cumul_interference :
    forall j t1 t2,
      cumul_cond_interference (fun _ _ => true) j t1 t2
      = cumulative_interference j t1 t2.
  Proof. by rewrite /cumulative_interference. Qed.

  (** In the following, consider a predicate [P]. *)
  Variable P : Job -> instant -> bool.

  (** First, we show that the cumulative conditional interference
      within a time interval <<[t1, t2)>> can be rewritten as a sum
      over all time instances satisfying [P j]. *)
  Lemma cumul_cond_interference_alt :
    forall j t1 t2,
      cumul_cond_interference P j t1 t2 = \sum_(t1 <= t < t2 | P j t) interference j t.
  Proof.
    move=> j t1 t2; rewrite [RHS]big_mkcond //=; apply eq_big_nat => t _.
    by rewrite /cond_interference; case: (P j t).
  Qed.

  (** Next, we show that cumulative interference on an interval <<[al, ar)>> is
      bounded by the cumulative interference on an interval <<[bl,br)>> if
      <<[al,ar)>> ⊆ <<[bl,br)>>. *)
  Lemma cumulative_interference_sub :
    forall (j : Job) (al ar bl br : instant),
      bl <= al ->
      ar <= br ->
      cumul_cond_interference P j al ar <= cumul_cond_interference P j bl br.
  Proof.
    move => j al ar bl br LE1 LE2.
    rewrite !cumul_cond_interference_alt.
    case: (leqP al ar) => [LEQ|LT]; last by rewrite big_geq.
    rewrite [leqRHS](@big_cat_nat _ _ _ al) //=; last by lia.
    by rewrite [in X in _ <= _ + X](@big_cat_nat _ _ _ ar) //=; lia.
  Qed.

  (** We show that the cumulative interference of a job can be split
      into disjoint intervals. *)
  Lemma cumulative_interference_cat :
    forall j t t1 t2,
      t1 <= t <= t2 ->
      cumul_cond_interference P j t1 t2
      = cumul_cond_interference P j t1 t + cumul_cond_interference P j t t2.
  Proof.
    move => j t t1 t2 /andP [LE1 LE2].
    by rewrite !cumul_cond_interference_alt {1}(@big_cat_nat _ _ _ t) //=.
  Qed.

End InterferenceAndInterferingWorkloadAuxiliary.
