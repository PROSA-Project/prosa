From mathcomp Require Export ssreflect ssrbool eqtype ssrnat seq fintype bigop div ssrfun.
Require Export prosa.util.list prosa.util.tactics.

(** * Additional Lemmas about [divn] and [modn] *)

(** Given two natural numbers [x] and [y], the fact that
    [x / y < (x + 1) / y] implies that [y] divides [x + 1]. *)
Lemma ltdivn_dvdn :
  forall x y,
    x %/ y < (x + 1) %/ y ->
    y %| (x + 1).
Proof.
  move=> x [|y]; rewrite addn1 ?divn0 // divnS //.
  by case: (y.+1 %| x.+1) => //; rewrite add0n ltnn.
Qed.

(** We show that the fact that [x / h = (x + y) / h] implies that
    [h] is larger than [x mod h + y mod h]. *)
Lemma addmod_le_mod :
  forall x y h,
    h > 0 ->
    x %/ h = (x + y) %/ h ->
    h > x %% h + y %% h.
Proof.
  move=> x y h POS /eqP.
  rewrite divnD // -{1}[x %/ h]addn0 -addnA eqn_add2l eq_sym addn_eq0 => /andP [_].
  by rewrite eqb0 -ltnNge.
Qed.

(** * Ceiling Division *)

(** We define division rounded up and prove a few basic properties. *)
Definition div_ceil (x y : nat) := if y %| x then x %/ y else (x %/ y).+1.

(** We start with an observation that [div_ceil 0 b] is equal to [0]
    for any [b]. *)
Lemma div_ceil0 :
  forall b, div_ceil 0 b = 0.
Proof.
  by move=> b; rewrite /div_ceil dvdn0 div0n.
Qed.

(** The ceiling quotient of a positive numerator is positive for any
    denominator. *)
Lemma div_ceil_gt0 :
  forall a b,
    a > 0 ->
    div_ceil a b > 0.
Proof.
  move=> a b POSa; rewrite /div_ceil.
  case DIV: (b %| a) => //.
  by rewrite divn_gt0 ?(dvdn_gt0 POSa DIV) //; apply: dvdn_leq.
Qed.

(** We show that [div_ceil] is monotone with respect to the first
    argument. *)
Lemma div_ceil_monotone1 :
  forall d m n,
    m <= n -> div_ceil m d <= div_ceil n d.
Proof.
  move=> d m n LEQ; rewrite /div_ceil.
  have LEQd := leq_div2r d LEQ.
  case Dm: (d %| m); case Dn: (d %| n) => //.
  rewrite ltn_divRL //.
  apply: leq_trans _ LEQ.
  by rewrite ltn_neqAle -dvdn_eq Dm leq_divM.
Qed.

(** We observe that when dividing a value exceeding [T * n], then
    the ceiling exceeds [n]. *)
Lemma div_ceil_multiple :
  forall Δ T n,
    T > 0 ->
    (T * n) < Δ ->
    n < div_ceil Δ T.
Proof.
  move=> delta T n POS LT; rewrite /div_ceil.
  case DIV: (T %| delta).
  - by rewrite ltn_divRL // mulnC.
  - by rewrite ltnS leq_divRL // mulnC; exact: ltnW LT.
Qed.

(** We prove a technical lemma stating that for any three integers [a, b, c]
    such that [c > b], [mod] can be swapped with subtraction in
    the expression [(a + c - b) %% c]. *)
Lemma mod_elim :
  forall a b c,
    c > b ->
    (a + c - b) %% c = if a %% c >= b then (a %% c - b) else (a %% c + c - b).
Proof.
  move=> a b c BC.
  have POS := leq_ltn_trans (leq0n b) BC.
  have LE := leq_trans (ltnW BC) (leq_addl a c).
  rewrite (modnB POS LE) modnDr (modn_small BC) ltnNge.
  by case: (b <= a %% c); rewrite /= ?add0n // mul1n addnC.
Qed.
