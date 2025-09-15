From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

(** In this section, we define the notion of monotonicity for functions. *)
Section MonotoneFunction.

  (** Consider a type [T], a relation [R] over type [T], and a
      function [f : T -> T]. *)
  Context {T : Type}.
  Variable R : rel T.
  Variable f : T -> T.

  (** We say that function [f] is monotone with respect to relation
      [R], iff [R x y] implies [R (f x) (f y)] for any [x y : T]. *)
  Definition monotone :=
    forall x y, R x y -> R (f x) (f y).

End MonotoneFunction.

(** In this section, we define some properties of relations on lists. *)
Section Order.

  (** Consider a type [T], a relation [R] over type [T], and a
      sequence [xs]. *)
  Context {T : eqType}.
  Variable R : T -> T -> bool.
  Variable xs : seq T.

  (** Relation [R] is total over list [xs], iff for any
      [x1 x2 \in xs], either [R x1 x2] or [R x2 x1] holds. *)
  Definition total_over_list :=
    forall x1 x2,
      x1 \in xs ->
      x2 \in xs ->
      R x1 x2 \/ R x2 x1.

  (** Relation [R] is antisymmetric over list [xs], iff for any
      [x1 x2 \in xs], [R x1 x2] and [R x2 x1] imply that [x1 = x2]. *)
  Definition antisymmetric_over_list :=
    forall x1 x2,
      x1 \in xs ->
      x2 \in xs ->
      R x1 x2 ->
      R x2 x1 ->
      x1 = x2.

End Order.
