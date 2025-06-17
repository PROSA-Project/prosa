Require Export prosa.analysis.definitions.interference.
Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.priority.classes.
Require Export prosa.analysis.abstract.definitions.
Require Export prosa.model.aggregate.service_of_jobs.
Require Export prosa.analysis.facts.model.service_of_jobs.


(** * Auxiliary Lemmas About Interference and Interfering Workload. *)

(** In this file we provide a set of auxiliary lemmas about generic
    properties of Interference and Interfering Workload. *)
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

  (** Consider any kind of fully supply-consuming uniprocessor model. *)
  Context `{PState : ProcessorState Job}.
  Hypothesis H_uniprocessor_proc_model : uniprocessor_model PState.
  Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

  (** Consider any valid arrival sequence with consistent arrivals ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any uni-processor schedule of this arrival
      sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after
      completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** For convenience, we define a function that "folds" cumulative
      conditional interference with a predicate [fun _ _ => true] to
      cumulative (unconditional) interference. *)
  Lemma fold_cumul_interference :
    forall j t1 t2,
      cumul_cond_interference (fun _ _ => true) j t1 t2
      = cumulative_interference j t1 t2.
  Proof. by rewrite /cumulative_interference. Qed.

  (** In this section, we prove a few basic properties of conditional
      interference w.r.t. a generic predicate [P]. *)
  Section CondInterferencePredicate.

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

    (** Next, we show that cumulative interference on an interval
        <<[al, ar)>> is bounded by the cumulative interference on an
        interval <<[bl,br)>> if <<[al,ar)>> ⊆ <<[bl,br)>>. *)
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

  End CondInterferencePredicate.

  (** Next, we show a few relations between interference functions
      conditioned on different predicates. *)
  Section CondInterferenceRelation.

    (** Consider predicates [P1, P2]. *)
    Variables P1 P2 : Job -> instant -> bool.

    (** We introduce a lemma (similar to ssreflect's [bigID] lemma)
        that allows us to split the cumulative conditional
        interference w.r.t predicate [P1] into a sum of two cumulative
        conditional interference w.r.t. predicates [P1 && P2] and [P1
        && ~~ P2], respectively. *)
    Lemma cumul_cond_interference_ID :
      forall j t1 t2,
        cumul_cond_interference P1 j t1 t2
        = cumul_cond_interference (fun j t => P1 j t && P2 j t) j t1 t2
          + cumul_cond_interference (fun j t => P1 j t && ~~ P2 j t) j t1 t2.
    Proof.
      move=> j t1 t2.
      rewrite -big_split //=; apply eq_bigr => t _.
      rewrite /cond_interference.
      by case (P1 _ _), (P2 _ _ ), (interference _ _).
    Qed.

    (** If two predicates [P1] and [P2] are equivalent, then they can
        be used interchangeably with [cumul_cond_interference]. *)
    Lemma cumul_cond_interference_pred_eq :
      forall (j : Job) (t1 t2 : instant),
        (forall j t, P1 j t <-> P2 j t) ->
        cumul_cond_interference P1 j t1 t2
        = cumul_cond_interference P2 j t1 t2.
    Proof.
      move=> j t1 t2 EQU.
      apply eq_bigr => t _; rewrite /cond_interference.
      move: (EQU j t).
      by case (P1 j t), (P2 j t), (interference _ _); move=> CONTR => //=; exfalso; apply notF, CONTR.
    Qed.

  End CondInterferenceRelation.

End InterferenceAndInterferingWorkloadAuxiliary.
