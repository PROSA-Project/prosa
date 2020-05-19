From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype.
Require Import prosa.util.tactics.

(** This file introduces a function called [search_arg] that allows finding the
    argument within a given range for which a function is minimal w.r.t. to a
    given order while satisfying a given predicate, along with lemmas
    establishing the basic properties of [search_arg].

    Note that while this is quite similar to [arg min ...] / [arg max ...] in
    [ssreflect] ([fintype]), this function is subtly different in that it possibly
    returns None and that it does not require the last element in the given
    range to satisfy the predicate. In contrast, [ssreflect]'s notion of
    extremum in [fintype] uses the upper bound of the search space as the
    default value, which is rather unnatural when searching through a schedule.
*)

Section ArgSearch.
  
  (* Given a function [f] that maps the naturals to elements of type [T]... *)
  Context {T : Type}.
  Variable f: nat -> T.

  (* ... a predicate [P] on [T] ... *)
  Variable P: pred T.

  (* ... and an order [R] on [T] ... *)
  Variable R: rel T.

  (* ... we define the procedure [search_arg] to iterate a given search space
     [a, b), while checking each element whether [f] satisfies [P] at that
     point and returning the extremum as defined by [R]. *)
  Fixpoint search_arg (a b : nat) : option nat :=
    if a < b then
      match b with
      | 0 => None
      | S b' => match search_arg a b' with
                | None => if P (f b') then Some b' else None
                | Some x => if P (f b') && R (f b') (f x) then Some b' else Some x
                end
      end
    else None.

  (** In the following, we establish basic properties of [search_arg]. *)

  (* To begin, we observe that the search yields [None] iff predicate [P] does
     not hold for any of the points in the search interval. *)
  Lemma search_arg_none:
    forall a b,
      search_arg a b = None <-> forall x, a <= x < b -> ~~ P (f x).
  Proof.
    split.
    { (* if *)
      elim: b => [ _ | b' HYP]; first by move=> _ /andP [_ FALSE] //.
      rewrite /search_arg  -/search_arg.
      case: (boolP (a < b'.+1)) => [a_lt_b | not_a_lt_b' TRIV].
      - move: HYP. case: (search_arg a b') => [y | HYP NIL x].
        + case: (P (f b') && R (f b') (f y)) => //.
        + move=> /andP[a_le_x x_lt_b'].
          move: x_lt_b'.
          rewrite ltnS leq_eqVlt => /orP [/eqP EQ|LT].
          * rewrite EQ.
            move: NIL. case: (P (f b')) => //.
          * feed HYP => //.
            apply: (HYP x).
            by apply /andP; split.
      - move=> x /andP [a_le_x b_lt_b'].
        exfalso.
        move: not_a_lt_b'. rewrite -leqNgt ltnNge => /negP b'_lt_a.
        by move: (leq_ltn_trans a_le_x b_lt_b').
    }
    { (* only if *)
      rewrite /search_arg.
      elim: b  => [//|b'].
      rewrite -/search_arg => IND  NOT_SAT.
      have ->: search_arg a b' = None.
      {
        apply IND => x /andP [a_le_x x_lt_n].
        apply: (NOT_SAT x).
        apply /andP; split => //.
        by rewrite ltnS; apply ltnW.
      }
      case: (boolP (a < b'.+1)) => [a_lt_b | //].
      apply ifF.
      apply negbTE.
      apply (NOT_SAT b').
        by apply /andP; split.
    }
  Qed.

  (* Conversely, if we know that [f] satisfies [P] for at least one point in
     the search space, then [search_arg] yields some point. *)
  Lemma search_arg_not_none:
    forall a b,
      (exists x, (a <= x < b) /\ P (f x)) ->
      exists y, search_arg a b = Some y.
  Proof.
    move=> a b H_exists.
    destruct (search_arg a b) eqn:SEARCH; first by exists n.
    move: SEARCH. rewrite search_arg_none => NOT_exists.
    exfalso.
    move: H_exists => [x [RANGE Pfx]].
    by move: (NOT_exists x RANGE) => /negP not_Pfx.
  Qed.

  (* Since [search_arg] considers only points at which [f] satisfies [P], if it
     returns a point, then that point satisfies [P]. *)
  Lemma search_arg_pred:
    forall a b x,
      search_arg a b = Some x -> P (f x).
  Proof.
    move=> a b x.
    elim: b => [| n IND]; first by rewrite /search_arg // ifN.
    rewrite /search_arg -/search_arg.
    destruct (a < n.+1) eqn:a_lt_Sn; last by trivial.
    move: a_lt_Sn. rewrite ltnS => a_lt_Sn.
    destruct (search_arg a n) as [q|] eqn:REC;
      destruct (P (f n)) eqn:Pfn => //=;
      [elim: (R (f n) (f q)) => // |];
      by move=> x_is; injection x_is => <-.
  Qed.

  (* Since [search_arg] considers only points within a given range, if it
     returns a point, then that point lies within the given range. *)
  Lemma search_arg_in_range:
    forall a b x,
      search_arg a b = Some x -> a <= x < b.
  Proof.
    move=> a b x.
    elim: b => [| n IND]; first by rewrite /search_arg // ifN.
    rewrite /search_arg -/search_arg.
    destruct (a < n.+1) eqn:a_lt_Sn; last by trivial.
    move: a_lt_Sn. rewrite ltnS => a_lt_Sn.
    destruct (search_arg a n) as [q|] eqn:REC;
      elim: (P (f n)) => //=.
    - elim: (R (f n) (f q)) => //= x_is;
        first by injection x_is => <-; apply /andP; split.
      move: (IND x_is) => /andP [a_le_x x_lt_n].
      apply /andP; split => //.
      by rewrite ltnS ltnW.
    - move => x_is.
      move: (IND x_is) => /andP [a_le_x x_lt_n].
      apply /andP; split => //.
      by rewrite ltnS ltnW.
    - move => x_is.
      by injection x_is => <-; apply /andP; split.
  Qed.

  (* Let us assume that [R] is a reflexive and transitive total order... *)
  Hypothesis R_reflexive: reflexive R.
  Hypothesis R_transitive: transitive R.
  Hypothesis R_total: total R.

  (* ...then [search_arg] yields an extremum w.r.t. to [a, b), that is, if
     [search_arg] yields a point x, then [R (f x) (f y)] holds for any [y] in the
     search range [a, b) that satisfies [P]. *)
  Lemma search_arg_extremum:
    forall a b x,
      search_arg a b = Some x ->
      forall y,
        a <= y < b ->
        P (f y) ->
        R (f x) (f y).
  Proof.
    move=> a b x SEARCH.
    elim: b x SEARCH => n IND x; first by rewrite /search_arg.
    rewrite /search_arg -/search_arg.
    destruct (a < n.+1) eqn:a_lt_Sn; last by trivial.
    move: a_lt_Sn. rewrite ltnS => a_lt_Sn.
    destruct (search_arg a n) as [q|] eqn:REC;
      destruct (P (f n)) eqn:Pfn => //=.
    - rewrite <- REC in IND.
      destruct (R (f n) (f q)) eqn:REL => some_x_is;
        move=> y /andP [a_le_y y_lt_Sn] Pfy;
        injection some_x_is => x_is; rewrite -{}x_is //;
        move: y_lt_Sn; rewrite ltnS;
        rewrite leq_eqVlt => /orP [/eqP EQ | y_lt_n].
      + by rewrite EQ; apply (R_reflexive (f n)).
      + apply (R_transitive (f q)) => //.
        move: (IND q REC y) => HOLDS.
        apply HOLDS => //.
        by apply /andP; split.
      + rewrite EQ.
        move: (R_total (f q) (f n)) => /orP [R_qn | R_nq] //.
        by move: REL => /negP.
      + move: (IND q REC y) => HOLDS.
        apply HOLDS => //.
        by apply /andP; split.
    - move=> some_q_is y /andP [a_le_y y_lt_Sn] Pfy.
      move: y_lt_Sn. rewrite ltnS.
      rewrite leq_eqVlt => /orP [/eqP EQ | y_lt_n].
      + exfalso. move: Pfn => /negP Pfn. by subst.
      + apply IND => //. by apply /andP; split.
    - move=> some_n_is. injection some_n_is => n_is.
      move=> y /andP [a_le_y y_lt_Sn] Pfy.
      move: y_lt_Sn. rewrite ltnS.
      rewrite leq_eqVlt => /orP [/eqP EQ | y_lt_n].
      + by rewrite -n_is EQ; apply (R_reflexive (f n)).
      + exfalso.
        move: REC. rewrite search_arg_none => NONE.
        move: (NONE y) => not_Pfy.
        feed not_Pfy; first by apply /andP; split.
        by move: not_Pfy => /negP.
  Qed.

End ArgSearch.

Section ExMinn.

  (* We show that the fact that the minimal satisfying argument [ex_minn ex] of 
     a predicate [pred] satisfies another predicate [P] implies the existence
     of a minimal element that satisfies both [pred] and [P]. *) 
  Lemma prop_on_ex_minn:
    forall (P : nat -> Prop) (pred : nat -> bool) (ex : exists n, pred n),
      P (ex_minn ex) ->
      exists n, P n /\ pred n /\ (forall n', pred n' -> n <= n').
  Proof.
    intros.
    exists (ex_minn ex); repeat split; auto.
    all: have MIN := ex_minnP ex; move: MIN => [n Pn MIN]; auto.
  Qed.

  (* As a corollary, we show that if there is a constant [c] such 
     that [P c], then the minimal satisfying argument [ex_minn ex] 
     of a predicate [P] is less than or equal to [c]. *)
  Corollary ex_minn_le_ex:
    forall (P : nat -> bool) (exP : exists n, P n) (c : nat),
      P c -> 
      ex_minn exP <= c.
  Proof. 
    intros ? ? ? EX.
    rewrite leqNgt; apply/negP; intros GT.
    pattern (ex_minn (P:=P) exP) in GT;
      apply prop_on_ex_minn in GT; move: GT => [n [LT [Pn MIN]]].
    specialize (MIN c EX).
      by move: MIN; rewrite leqNgt; move => /negP MIN; apply: MIN.
  Qed.
  
End ExMinn.
