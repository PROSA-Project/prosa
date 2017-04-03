From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.

(* In this file, we define functions for picking numbers in an interval [0, n). *)

(** Auxiliary Functions *)

Definition default0 {n} (x: option 'I_n) : nat := if x is Some y then y else 0.

Definition arg_pred_nat n (P: pred 'I_n) ord :=
  [pred i | P i & [forall j: 'I_n, P j ==> ord i j]].

Definition pred_min_nat n (P: pred 'I_n) := arg_pred_nat n P leq.
Definition pred_max_nat n (P: pred 'I_n) := arg_pred_nat n P (fun x y => geq x y).

(** Defining Pick functions *)

(* (pick_any n P) returns some number < n that satisfies P, or 0 if it cannot be found. *)
Definition pick_any n (P: pred 'I_n) := default0 (pick P).

(* (pick_min n P) returns the smallest number < n that satisfies P, or 0 if it cannot be found. *)
Definition pick_min n (P: pred 'I_n) := default0 (pick (pred_min_nat n P)).

(* (pick_max n P) returns the largest number < n that satisfies P, or 0 if it cannot be found. *)
Definition pick_max n (P: pred 'I_n) := default0 (pick (pred_max_nat n P)).

(** Improved notation *)

(* Next we provide the following notation for the variations of pick:
     [pick-any x <= N | P], [pick-any x < N | P]
     [pick-min x <= N | P], [pick-min x < N | P]
     [pick-max x <= N | P], [pick-max x < N | P]. *)
Notation "[ 'pick-any' x <= N | P ]" :=
  (pick_any N.+1 (fun x : 'I_N.+1 => P%B))
  (at level 0, x ident, only parsing) : form_scope.
    
Notation "[ 'pick-any' x < N | P ]" :=
  (pick_any N (fun x : 'I_N => P%B))
  (at level 0, x ident, only parsing) : form_scope.

Notation "[ 'pick-min' x <= N | P ]" :=
  (pick_min N.+1 (fun x : 'I_N.+1 => P%B))
  (at level 0, x ident, only parsing) : form_scope.

Notation "[ 'pick-min' x < N | P ]" :=
  (pick_min N (fun x : 'I_N => P%B))
  (at level 0, x ident, only parsing) : form_scope.

Notation "[ 'pick-max' x <= N | P ]" :=
  (pick_max N.+1 (fun x : 'I_N.+1 => P%B))
  (at level 0, x ident, only parsing) : form_scope.

Notation "[ 'pick-max' x < N | P ]" :=
  (pick_max N (fun x : 'I_N => P%B))
  (at level 0, x ident, only parsing) : form_scope.

(** Lemmas about pick_any *)

Section PickAny.

  Variable n: nat.
  Variable p: pred 'I_n.

  Variable P: nat -> Prop.

  Hypothesis EX: exists x:'I_n, p x.

  Hypothesis HOLDS: forall x, p x -> P x.

  (* First, we show that any property P of (pick_any n p) can be proven by showing
     that P holds for any number < n that satisfies p. *)
  Lemma pick_any_holds: P (pick_any n p).
  Proof.
    rewrite /pick_any /default0.
    case: pickP; first by intros x PRED; apply HOLDS.
    intros NONE; red in NONE; exfalso.
    move: EX => [x PRED].
    by specialize (NONE x); rewrite PRED in NONE.
  Qed.

End PickAny.

(** Lemmas about pick_min *)
Section PickMin.

  Variable n: nat.
  Variable p: pred 'I_n.

  Variable P: nat -> Prop.

  (* Assume that there is some number < n that satisfies p. *)
  Hypothesis EX: exists x:'I_n, p x.

  Section Bound.

    (* First, we show that (pick_min n p) < n. *)
    Lemma pick_min_ltn: pick_min n p < n.
    Proof.
      rewrite /pick_min /odflt /oapp.
      case: pickP.
      {
        move => x /andP [PRED /forallP ALL].
          by rewrite /default0.
      }
      {
        intros NONE; red in NONE; exfalso.
        move: EX => [x PRED]; clear EX.
        set argmin := arg_min x p id.
        specialize (NONE argmin).
        suff ARGMIN: (pred_min_nat n p) argmin by rewrite ARGMIN in NONE.
        rewrite /argmin; case: arg_minP; first by done.
        intros y Py MINy.
        apply/andP; split; first by done.
        by apply/forallP; intros y0; apply/implyP; intros Py0; apply MINy.
      }
    Qed.

  End Bound.

  Section Minimum.
    
    Hypothesis MIN:
      forall x,
        p x ->
        x < n ->
        (forall y, p y -> x <= y) ->
        P x.
    
    (* Next, we show that any property P of (pick_min n p) can be proven by showing
       that P holds for the smallest number < n that satisfies p. *)
    Lemma pick_min_holds: P (pick_min n p).
    Proof.
      rewrite /pick_min /odflt /oapp.
      case: pickP.
      {
        move => x /andP [PRED /forallP ALL].
        apply MIN; try (by done).
          by intros y Py; specialize (ALL y); move: ALL => /implyP ALL; apply ALL.
      }
      {
        intros NONE; red in NONE; exfalso.
        move: EX => [x PRED]; clear EX.
        set argmin := arg_min x p id.
        specialize (NONE argmin).
        suff ARGMIN: (pred_min_nat n p) argmin by rewrite ARGMIN in NONE.
        rewrite /argmin; case: arg_minP; first by done.
        intros y Py MINy.
        apply/andP; split; first by done.
          by apply/forallP; intros y0; apply/implyP; intros Py0; apply MINy.
      }
    Qed.

  End Minimum.
  
End PickMin.

(** Lemmas about pick_max *)
Section PickMax.

  Variable n: nat.
  Variable p: pred 'I_n.

  Variable P: nat -> Prop.

  (* Assume that there is some number < n that satisfies p. *)
  Hypothesis EX: exists x:'I_n, p x.

  Section Bound.
    
    (* First, we show that (pick_max n p) < n. *)
    Lemma pick_max_ltn: pick_max n p < n.
    Proof.
      rewrite /pick_max /odflt /oapp.
      case: pickP.
      {
        move => x /andP [PRED /forallP ALL].
          by rewrite /default0.
      }
      {
        intros NONE; red in NONE; exfalso.
        move: EX => [x PRED]; clear EX.
        set argmax := arg_max x p id.
        specialize (NONE argmax).
        suff ARGMAX: (pred_max_nat n p) argmax by rewrite ARGMAX in NONE.
        rewrite /argmax; case: arg_maxP; first by done.
        intros y Py MAXy.
        apply/andP; split; first by done.
          by apply/forallP; intros y0; apply/implyP; intros Py0; apply MAXy.
      }
    Qed.

  End Bound.

  Section Maximum.
    
    Hypothesis MAX:
      forall x,
        p x ->
        x < n ->
        (forall y, p y -> x >= y) ->
        P x.
    
    (* Next, we show that any property P of (pick_max n p) can be proven by showing that
       P holds for the largest number < n that satisfies p. *)
    Lemma pick_max_holds: P (pick_max n p).
    Proof.
      rewrite /pick_max /odflt /oapp.
      case: pickP.
      {
        move => x /andP [PRED /forallP ALL].
        apply MAX; try (by done).
          by intros y Py; specialize (ALL y); move: ALL => /implyP ALL; apply ALL.
      }
      {
        intros NONE; red in NONE; exfalso.
        move: EX => [x PRED]; clear EX.
        set argmax := arg_max x p id.
        specialize (NONE argmax).
        suff ARGMAX: (pred_max_nat n p) argmax by rewrite ARGMAX in NONE.
        rewrite /argmax; case: arg_maxP; first by done.
        intros y Py MAXy.
        apply/andP; split; first by done.
          by apply/forallP; intros y0; apply/implyP; intros Py0; apply MAXy.
      }
    Qed.

  End Maximum.
  
End PickMax.