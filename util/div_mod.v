Require Export prosa.util.nat.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.


Definition div_floor (x y: nat) : nat := x %/ y.
Definition div_ceil (x y: nat) := if y %| x then x %/ y else (x %/ y).+1.

Lemma mod_elim:
  forall a b c,
    c>0 ->
    b<c ->
    (a + c - b)%%c = ( if a%%c >= b then (a%%c - b) else (a%%c + c - b)).
Proof.
  intros* CP BC.
  have G: a%%c < c by apply ltn_pmod.
  case (b <= a %% c)eqn:CASE;rewrite -addnBA;auto;rewrite -modnDml.
  - rewrite add_subC;auto. rewrite -modnDmr modnn addn0 modn_small;auto;ssromega.
  - rewrite modn_small;try ssromega.
Qed.

