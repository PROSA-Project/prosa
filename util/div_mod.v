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
  - rewrite add_subC;auto. rewrite -modnDmr modnn addn0 modn_small;auto;ssrlia.
  - rewrite modn_small;try ssrlia.
Qed.

(** We show that for any two integers [a] and [c], 
    [a] is less than [a %/ c * c + c] given that [c] is positive. *)
Lemma div_floor_add_g:
  forall a c,
    c > 0 ->
    a < a %/ c * c + c.
Proof.
  intros * POS.
  specialize (divn_eq a c) => DIV.
  rewrite [in X in X < _]DIV.
  rewrite ltn_add2l.
  now apply ltn_pmod.
Qed.    
