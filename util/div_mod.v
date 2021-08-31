Require Export prosa.util.nat prosa.util.subadditivity.
From mathcomp Require Export ssreflect ssrbool eqtype ssrnat seq fintype bigop div ssrfun.

(** First, we define functions [div_floor] and [div_ceil], which are
    divisions rounded down and up, respectively. *) 
Definition div_floor (x y : nat) : nat := x %/ y.
Definition div_ceil (x y : nat) := if y %| x then x %/ y else (x %/ y).+1.

(** We show that for any two integers [a] and [b], 
    [a] is less than [a %/ b * b + b] given that [b] is positive. *)
Lemma div_floor_add_g:
  forall a b,
    b > 0 ->
    a < a %/ b * b + b.
Proof.
  intros * POS.
  specialize (divn_eq a b) => DIV.
  rewrite [in X in X < _]DIV.
  rewrite ltn_add2l.
  by apply ltn_pmod.
Qed.

(** We show that the division with ceiling by a constant [T] is a subadditive function. *)
Lemma div_ceil_subadditive:
  forall T, subadditive (div_ceil^~T).
Proof.
  move=> T ab a b SUM.
  rewrite -SUM.
  destruct (T %| a) eqn:DIVa, (T %| b) eqn:DIVb.
  - have DIVab: T %| a + b by apply dvdn_add.
    by rewrite /div_ceil DIVa DIVb DIVab divnDl.
  - have DIVab: T %| a+b = false by rewrite -DIVb; apply dvdn_addr.
    by rewrite /div_ceil DIVa DIVb DIVab divnDl //=; ssrlia.
  - have DIVab: T %| a+b = false by rewrite -DIVa; apply dvdn_addl.
    by rewrite /div_ceil DIVa DIVb DIVab divnDr //=; ssrlia.
  - destruct (T %| a + b) eqn:DIVab.
    + rewrite /div_ceil DIVa DIVb DIVab.
      apply leq_trans with (a %/ T + b %/T + 1); last by ssrlia.
      by apply leq_divDl.
    + rewrite /div_ceil DIVa DIVb DIVab.
      apply leq_ltn_trans with (a %/ T + b %/T + 1); last by ssrlia.
      by apply leq_divDl.
Qed.


(** We prove a technical lemma stating that for any three integers [a,
    b, c] such that [c > b], [mod] can be swapped with subtraction in
    the expression [(a + c - b) %% c]. *) 
Lemma mod_elim:
  forall a b c,
    c > b ->
    (a + c - b) %% c = if a %% c >= b then (a %% c - b) else (a %% c + c - b).
Proof.
  intros * BC.
  have POS : c > 0 by ssrlia.
  have G : a %% c < c by apply ltn_pmod.
  case (b <= a %% c) eqn:CASE; rewrite -addnBA; auto; rewrite -modnDml.
  - rewrite addnABC; auto.
    by rewrite -modnDmr modnn addn0 modn_small; auto; ssrlia.
  - by rewrite modn_small; ssrlia.
Qed.
