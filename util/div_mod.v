Require Export prosa.util.nat prosa.util.subadditivity.
From mathcomp Require Export ssreflect ssrbool eqtype ssrnat seq fintype bigop div ssrfun.

(** First, we define functions [div_floor] and [div_ceil], which are
    divisions rounded down and up, respectively. *) 
Definition div_floor (x y : nat) : nat := x %/ y.
Definition div_ceil (x y : nat) := if y %| x then x %/ y else (x %/ y).+1.

(** We start with an observation that [div_ceil 0 b] is equal to
    [0] for any [b]. *) 
Lemma div_ceil0:
  forall b, div_ceil 0 b = 0.
Proof.
  intros b; unfold div_ceil.
  by rewrite dvdn0; apply div0n.
Qed.

(** Next, we show that, given two positive integers [a] and [b],
    [div_ceil a b] is also positive. *)
Lemma div_ceil_gt0:
  forall a b,
    a > 0 -> b > 0 ->
    div_ceil a b > 0.
Proof.
  intros a b POSa POSb.
  unfold div_ceil.
  destruct (b %| a) eqn:EQ; last by done.
  by rewrite divn_gt0 //; apply dvdn_leq.
Qed.
  
(** We show that [div_ceil] is monotone with respect to the first
    argument. *)
Lemma div_ceil_monotone1:
  forall d m n,
    m <= n -> div_ceil m d <= div_ceil n d.
Proof.
  move => d m n LEQ.
  rewrite /div_ceil.
  have LEQd: m %/ d <= n %/ d by apply leq_div2r.
  destruct (d %| m) eqn:Mm; destruct (d %| n) eqn:Mn => //; first by ssrlia.
  rewrite ltn_divRL //.
  apply ltn_leq_trans with m => //.
  move: (leq_trunc_div m d) => LEQm.
  destruct (ltngtP (m %/ d * d) m) => //.
  move: e => /eqP EQ; rewrite -dvdn_eq in EQ.
  by rewrite EQ in Mm.
Qed.
  
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

(** Given [T] and [Δ] such that [Δ >= T > 0], we show that [div_ceil Δ T] 
    is strictly greater than [div_ceil (Δ - T) T]. *)
Lemma leq_div_ceil_add1:
  forall Δ T,
    T > 0 -> Δ >= T ->
    div_ceil (Δ - T) T < div_ceil Δ T.
Proof.
  intros * POS LE. rewrite /div_ceil.
  have lkc: (Δ - T) %/ T < Δ %/ T.
  { rewrite divnBr; last by auto.
    rewrite divnn POS.
    rewrite ltn_psubCl //; try ssrlia.
    by rewrite divn_gt0.
  }
  destruct (T %| Δ) eqn:EQ1.
  { have divck:  (T %| Δ) ->  (T %| (Δ - T)) by auto.
    apply divck in EQ1 as EQ2.
    rewrite EQ2; apply lkc.
  }
  by destruct (T %| Δ - T) eqn:EQ, (T %| Δ) eqn:EQ3; auto.
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
