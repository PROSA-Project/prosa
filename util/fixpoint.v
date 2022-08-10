From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq fintype bigop path.

Require Export prosa.util.rel.
Require Export prosa.util.list.
Require Export prosa.util.minmax.

(** * Fixpoint Search *)

(** This module provides some utilities for finding positive fixpoints of
    monotonic functions. *)

(** ** Least Positive Fixpoint *)

(** Finds the least fixpoint of a monotonic function, between a start point [s]
    and a horizon [h], given an amount of [fuel]. *)
Fixpoint find_fixpoint_from (f : nat -> nat) (x h fuel: nat): option nat :=
  if fuel is S fuel' then
    if f x == x then
      Some x
      else
        if (f x) <= h then
          find_fixpoint_from f (f x) h fuel'
        else None
    else None.

(** Given a horizon [h] and a monotonic function [f], find the least positive
    fixpoint of [f] no larger than [h], if any. *)
Definition find_fixpoint (f : nat -> nat) (h : nat) : option nat :=
    find_fixpoint_from f 1 h h.

(** In the following, we show that the fixpoint search works as expected. *)
Section FixpointSearch.

  (** Consider any function [f] ... *)
  Variable f : nat -> nat.

  (** ... and any given horizon. *)
  Variable h : nat.

  (** We show that the result of [find_fixpoint_from] is indeed a fixpoint. *)
  Lemma ffpf_finds_fixpoint :
    forall s x fuel: nat,
      find_fixpoint_from f s h fuel = Some x ->
      x = f x.
  Proof.
    move=> s x fuel.
    elim: fuel s => // fuel' IH s'.
    rewrite /find_fixpoint_from.
    case: (eqVneq (f s') s') => [F [] <- // | _].
    rewrite -/find_fixpoint_from.
    case: (f s' <= h) => //.
    by apply: IH.
  Qed.

  (** Using the above fact, we observe that the result of [find_fixpoint] is a
      fixpoint. *)
  Corollary ffp_finds_fixpoint :
    forall x : nat,
      find_fixpoint f h = Some x ->
      x = f x.
  Proof. by move=> x FOUND; apply: ffpf_finds_fixpoint FOUND. Qed.

  (** Next, we establish properties that rely on the monotonic properties of the
      function. *)
  Section MonotonicFunction.

    (** Suppose [f] is monotonically increasing ... *)
    Hypothesis H_f_mono: monotone leq f.

    (** ... and not zero at 1. *)
    Hypothesis F1: f 1 > 0.

    (** Assuming the function is monotonic, there is no fixpoint between [a] and
        [c], if [f a = c]. *)
    Lemma no_fixpoint_skipped :
      forall a c,
        c = f a ->
        forall b,
          a <= b < c ->
          b != f b.
    Proof.
      move=> a c EQ b /andP[LEQ LT].
      move: (H_f_mono a b LEQ) => MONO.
      by lia.
    Qed.

    (** It follows that [find_fixpoint_from] finds the least fixpoint larger
        than [s]. *)
    Lemma ffpf_finds_least_fixpoint :
      forall y s fuel,
        find_fixpoint_from f s h fuel = Some y ->
        forall x,
          s <= x < y ->
          x != f x.
    Proof.
      move=> y s fuel.
      elim: fuel s => // fuel' IH s FFP x /andP[LEQx LT].
      move: FFP; rewrite /find_fixpoint_from.
      case: (eqVneq (f s) s);
        first by move=> EQ []; lia.
      move=> EQ.
      case: (leqP (f s) h) => // LEQh.
      rewrite -/find_fixpoint_from => FFP.
      case: (leqP (f s) x) => [fsLEQs|sLTfs].
      { apply: (IH (f s)) => //.
        by apply /andP; split. }
      { apply: (no_fixpoint_skipped s (f s)) => //.
        by apply /andP; split. }
    Qed.

    (** Hence [find_fixpoint] finds the least positive fixpoint of [f]. *)
    Corollary ffp_finds_least_fixpoint :
      forall x y,
        0 < x < y ->
        find_fixpoint f h = Some y ->
        x != f x.
    Proof. by move=> x y LT FFP; apply: ffpf_finds_least_fixpoint; eauto. Qed.

  (** Furthermore, we observe that [find_fixpoint_from] finds positive fixpoints
      when provided with a positive starting point [s]. *)
  Lemma ffpf_finds_positive_fixpoint :
    forall s fuel x,
      Some x = find_fixpoint_from f s h fuel ->
      0 < s ->
      0 < x.
  Proof.
    move=> s fuel x.
    rewrite /find_fixpoint_from.
    elim: fuel s => // fuel' IH s.
    case: (eqVneq (f s) s) => [_ SOME | NEQ].
    - by move: SOME => []; lia.
    - case (f s <= h) => // SOME GT.
      have: 0 < f s. { by move: (H_f_mono 1 s GT) => MONO; lia. }
      by apply (IH (f s)).
    Qed.

    (** Hence [finds_fixpoint] finds only positive fixpoints. *)
    Lemma ffp_finds_positive_fixpoint :
      forall x,
        Some x = find_fixpoint f h ->
        0 < x.
    Proof.
      move=> x.
      rewrite /find_fixpoint => FIX.
      by apply: ffpf_finds_positive_fixpoint; first apply FIX.
    Qed.

    (** If [find_fixpoint_from] finds no fixpoint between s and h,
        there is none. *)
    Lemma ffpf_finds_none :
      forall s fuel,
        s <= f s ->
        fuel >= h - s ->
        find_fixpoint_from f s h fuel = None ->
        forall x,
          s <= x < h ->
          x != f x.
    Proof.
      move=> s fuel.
      elim: fuel s => [|fuel' IH s GEQ FUEL]; first by lia.
      rewrite /find_fixpoint_from.
      case: (eqVneq (f s) s) => // F.
      case: (leqP (f s) h) => [_ | GTNh _]; last first.
      { rewrite -/find_fixpoint_from => x /andP[SX LT].
        apply: (no_fixpoint_skipped s) => //.
        apply /andP; split => //.
        by apply: ltn_trans LT GTNh. }
      { rewrite -/find_fixpoint_from => FFP x /andP[SX XH].
        case: (leqP (f s) x) => FSX.
        { apply: (IH (f s)) => //.
          - by apply H_f_mono => //.
          - by lia.
          - by apply /andP; split. }
        { apply: (no_fixpoint_skipped s) => //.
          by apply /andP; split. }}
    Qed.

    (** Hence, if [find_fixpoint] finds no positive fixpoint less than h, there
        is none. *)
    Lemma ffp_finds_none :
      find_fixpoint f h = None ->
        forall x,
        0 < x < h ->
        x != f x.
    Proof.
      move=> FFP x /andP [POS LT].
      apply: (ffpf_finds_none 1 h).
      - by move: F1; case (f 1) => //.
      - by rewrite subn1; exact /leq_pred.
      - by exact: FFP.
      - by apply /andP; split.
    Qed.

  End MonotonicFunction.

End FixpointSearch.

(** ** Maximal Fixpoint across a Search Space *)

(** Given a function taking two inputs and a search space for the first
    argument, [find_max_fixpoint_of_seq] finds the maximum fixpoint with regard
    to the second argument across the search space, but only if a fixpoint exists
    for each point in the search space. *)
Definition find_max_fixpoint_of_seq (f : nat -> nat -> nat)
          (sp : seq nat) (h : nat) : option nat :=
  let is_some opt := opt != None in
  let fixpoints := [seq find_fixpoint (f s) h | s <- sp] in
  let max := \max_(fp <- fixpoints | is_some fp) (odflt 0) fp in
  if all is_some fixpoints then Some max else None.

(** We prove that the result of the [find_max_fixpoint_of_seq] is a fixpoint of
    the function for an element of the search space. *)
Lemma fmfs_finds_fixpoint :
  forall (f : nat -> nat -> nat) (sp : seq nat) (h x : nat),
    ~~ nilp sp ->
    find_max_fixpoint_of_seq f sp h = Some x ->
    exists2 a, a \in sp & x = f a x.
Proof.
  move=> f sp h x NN.
  rewrite /find_max_fixpoint_of_seq //=.
  set fps := [seq find_fixpoint (f s) h | s <- sp] => H.
  have ALL: all (fun opt => opt != None) fps
              by case: (all _ _) H => //.
  move: H. rewrite ifT //; move => [] H.
  have NN': ~~ nilp fps
    by rewrite /fps /nilp size_map -/(nilp sp).
  move: (bigmax_witness
           (fun fp => match fp with | Some x' => x' | None => 0 end)
           (has_all_nilp _ _ ALL NN'))
      => //= [w [IN [SOME MAX]]].
  case: w IN SOME MAX => // w IN _.
  rewrite {}H => WX.
  move: IN; rewrite WX /fps => /mapP [a IN FIX].
  exists a => //.
  by eapply ffp_finds_fixpoint, ssrfun.esym, FIX.
Qed.

(** Furthermore, we show that the result is the maximum of all fixpoints, with
    regard to the search space.*)
Lemma fmfs_is_maximum :
  forall (f : nat -> nat -> nat) (sp : seq nat) (h s r: nat),
    Some r = find_max_fixpoint_of_seq f sp h ->
    s \in sp ->
    exists2 v,
      Some v = find_fixpoint (f s) h & r >= v.
Proof.
  move=> f sp h s r.
  rewrite /find_max_fixpoint_of_seq //=.
  set fps := [seq find_fixpoint (f s) h | s <- sp] => H.
  have ALL : all (fun opt => opt != None) fps
    by case: (all _ _) H => //.
  move: H. rewrite ifT //; move => [] H IN.
  exists ((odflt 0) (find_fixpoint (f s) h)).
  - case FFP: (find_fixpoint _ _) => //=; exfalso.
    suff: find_fixpoint (f s) h != None;
      first by move=> /eqP.
    move: ALL => /allP //=; apply.
    by rewrite /fps; exact: map_f.
  - rewrite H.
    apply leq_bigmax_cond_seq; [|move: ALL => /allP //=; apply].
    all: by rewrite /fps; exact: map_f.
Qed.

(** ** Search Space Defined by a Predicate *)

Section PredicateSearchSpace.

  (** Consider a limit [L] ... *)
  Variable L : nat.

  (** ... and any predicate [P] on numbers. *)
  Variable P : pred nat.

  (** We create a derive predicate that defines the search space as all values
      less than [L] that satisfy [P]. *)
  Let is_in_search_space A := (A < L) && P A.

  (** This is used to create a corresponding sequence of points in the search
      space. *)
  Let sp := [seq s <- (iota 0 L) | P s].

  (** Based on this conversion, we define a function to find the maximum of all
      fixpoints within the search space. *)
  Definition find_max_fixpoint (f : nat -> nat -> nat) (h : nat) :=
    if (has P (iota 0 L)) then find_max_fixpoint_of_seq f sp h else None.

  (** The result of [find_max_fixpoint] is a fixpoint of the function [f] for a
      an element of the search space. *)
  Corollary fmf_finds_fixpoint :
    forall (f : nat -> nat -> nat) (h x: nat),
      find_max_fixpoint f h = Some x ->
      exists2 a, is_in_search_space a & x = f a x.
  Proof.
    move=> f h x SOME.
    have NILP: ~~ nilp sp.
    { move: SOME.
      rewrite /find_max_fixpoint has_count /sp /nilp size_filter.
      change (fun s : nat => P s) with P.
      by case (count P (iota 0 L)) => //. }
    have FP: exists2 a, a \in sp & x = f a x.
    { apply: fmfs_finds_fixpoint.
      - exact: NILP.
      - move: SOME.
        rewrite /find_max_fixpoint.
        case: (has P (iota 0 L)) => //; exact. }
    move: FP => [a IN FP].
    exists a => //.
    by move: IN; rewrite /sp /is_in_search_space mem_filter mem_iota andbC.
  Qed.

  (** Finally, we observe that there is no fixpoint in the search space larger
      than the result of [find_maximum_fixpoint]. *)
  Corollary fmf_is_maximum :
    forall {f : nat -> nat -> nat} {h s r: nat},
      Some r = find_max_fixpoint f h ->
      is_in_search_space s ->
        exists2 v, Some v = find_fixpoint (f s) h & r >= v.
  Proof.
    move=> f h s r.
    rewrite /find_max_fixpoint.
    case: (has P (iota 0 L)) => // SOME PRED.
    apply: fmfs_is_maximum; first exact SOME.
    by move: PRED; rewrite /is_in_search_space /sp mem_filter mem_iota //= add0n andbC.
  Qed.

End PredicateSearchSpace.
