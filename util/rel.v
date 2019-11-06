From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

(* In this section, we define some properties of relations
   that are important for fixed-point iterations. *)
Section Relations.

  Context {T: Type}.
  Variable R: rel T.
  Variable f: T -> T.
  
  Definition monotone (R: rel T) :=
    forall x y, R x y -> R (f x) (f y).

End Relations.

Section Order.

  Context {T: eqType}.
  Variable rel: T -> T -> bool.
  Variable l: seq T.
  
  Definition total_over_list :=
    forall x1 x2,
      x1 \in l ->
      x2 \in l ->
      (rel x1 x2 \/ rel x2 x1).
      
  Definition antisymmetric_over_list :=
    forall x1 x2,
      x1 \in l ->
      x2 \in l ->
      rel x1 x2 ->
      rel x2 x1 ->
      x1 = x2.

End Order.
