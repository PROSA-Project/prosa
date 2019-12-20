From mathcomp Require Import ssrnat ssrbool fintype.
Require Export prosa.analysis.facts.behavior.all.

(** This file provides an operation that transforms a finite prefix of
    a given schedule by applying a point-wise transformation to each
    instant up to a given horizon. *)

Section SchedulePrefixMap.
  
  (** For any type of jobs and... *)
  Context {Job : JobType}.

  (** ... any given type of processor states ... *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** ... we define a procedure that applies a given function to every
     point in a given finite prefix of the schedule.

     The point-wise transformation f is given a schedule and the point
     to transform, and must yield a transformed schedule that is used
     in subsequent operations. *)
  Fixpoint prefix_map
           (sched: schedule PState)
           (f: schedule PState -> instant -> schedule PState)
           (horizon: instant) :=
    match horizon with
    | 0 => sched
    | S t =>
      let
        prefix := prefix_map sched f t
      in f prefix t
    end.


  (** We provide a utility lemma that establishes that, if the
      point-wise transformation maintains a given property of the
      original schedule, then the prefix_map does so as well. *)
  Section PropertyPreservation.

    (** Given any property of schedules... *)
    Variable P: schedule PState -> Prop.

    (** ...and a point-wise transformation [f],... *)
    Variable f: schedule PState -> instant -> schedule PState.

    (** ...if [f] maintains property [P],... *)
    Hypothesis H_f_maintains_P: forall sched t, P sched -> P (f sched t).

    (** ...then so does a prefix map of [f]. *)
    Lemma prefix_map_property_invariance:
      forall sched h, P sched -> P (prefix_map sched f h).
    Proof.
      move=> sched h P_sched.
      induction h; first by rewrite /prefix_map.
      rewrite /prefix_map -/prefix_map.
      by apply: H_f_maintains_P.
    Qed.

  End PropertyPreservation.

  (** Next, we consider the case where the point-wise transformation
      establishes a new property step-by-step. *)
  Section PointwiseProperty.

    (** Given any property of schedules [P],... *)
    Variable P: schedule PState -> Prop.

    (** ...any point-wise property [Q],... *)
    Variable Q: schedule PState -> instant -> Prop.

    (** ...and a point-wise transformation [f],... *)
    Variable f: schedule PState -> instant -> schedule PState.

    (** ...if [f] maintains [P]... *)
    Hypothesis H_f_maintains_P:
      forall sched t_ref,
        P sched -> P (f sched t_ref).

    (** ...and establishes [Q] (provided that [P] holds)... *)
    Hypothesis H_f_grows_Q:
      forall sched t_ref,
        P sched ->
        (forall t', t' <  t_ref -> Q sched t') ->
        forall t', t' <= t_ref -> Q (f sched t_ref) t'.

    (** ...then the prefix-map operation will "grow" [Q] up to the horizon. *)
    Lemma prefix_map_pointwise_property:
      forall sched horizon,
        P sched ->
        forall t,
          t < horizon ->
          Q (prefix_map sched f horizon) t.
    Proof.
      move=> sched h P_holds.
      induction h as [|h Q_holds_before_h]; first by rewrite /prefix_map.
      rewrite /prefix_map -/prefix_map => t.
      rewrite ltnS => LE_t_h.
      apply H_f_grows_Q => //.
      by apply prefix_map_property_invariance.
    Qed.
    
  End PointwiseProperty.

End SchedulePrefixMap.
