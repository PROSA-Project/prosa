From mathcomp Require Export ssreflect ssrbool eqtype ssrnat seq fintype bigop div ssrfun.
Require Export prosa.util.nat prosa.util.subadditivity.

(** * Additional Lemmas about [divn] and [modn] *)

(** First, we show that if [t1 / h] is equal to [t2 / h] and [t1 <= t2],
    then [t1 mod h] is bounded by [t2 mod h]. *)
Lemma eqdivn_leqmodn :
  forall t1 t2 h,
    t1 <= t2 ->
    t1 %/ h = t2 %/ h ->
    t1 %% h <= t2 %% h.
Proof.
  move=> t1 t2 h LT EQ.
  destruct (posnP h) as [Z | POSh].
  { by subst; rewrite !modn0. }
  { have EX: exists k, t1 + k = t2.
    { exists (t2 - t1); lia. }
    destruct EX as [k EX]; subst t2; clear LT.
    rewrite modnD //; replace (h <= t1 %% h + k %% h) with false; first by lia.
    symmetry; apply/negP/negP; rewrite -ltnNge.
    symmetry in EQ; rewrite divnD // in EQ; move: EQ => /eqP.
    rewrite -{2}[t1 %/ h]addn0 -addnA eqn_add2l addn_eq0 => /andP [_ /eqP Z2].
    by move: Z2 => /eqP; rewrite eqb0 -ltnNge.
  }
Qed.

(** Given two natural numbers [x] and [y], the fact that
    [x / y < (x + 1) / y] implies that [y] divides [x + 1]. *)
Lemma ltdivn_dvdn :
  forall x y,
    x %/ y < (x + 1) %/ y ->
    y %| (x + 1).
Proof.
  move=> x y LT.
  destruct (posnP y) as [Z | POS]; first by subst y.
  move: LT; rewrite divnD // -addn1 -addnA leq_add2l addn_gt0 => /orP [ONE | LE].
  { by destruct y as [ | []]. }
  { rewrite lt0b in LE.
    destruct (leqP 2 y) as [LT2 | GE2]; last by destruct y as [ | []].
    clear POS; rewrite [1 %%  _]modn_small // in LE.
    move: LE; rewrite leq_eqVlt => /orP [/eqP EQ | LT].
    { rewrite [x](divn_eq x y) -addnA -EQ; apply dvdn_add.
      - by apply dvdn_mull, dvdnn.
      - by apply dvdnn.
    }
    { by move: LT; rewrite -addn1 leq_add2r leqNgt ltn_pmod //; lia. }
  }
Qed.

(** We prove an auxiliary lemma allowing us to change the order of
    operations [_ + 1] and [_ %% h]. *)
Lemma addn1_modn_commute :
  forall x h,
    h > 0 ->
    x %/ h = (x + 1) %/ h ->
    (x + 1) %% h = x %% h + 1 .
Proof.
  intros x h POS EQ.
  rewrite !addnS !addn0.
  rewrite addnS divnS // addn0 in EQ.
  destruct (h %| x.+1) eqn:DIV ; rewrite /= in EQ; first by lia.
  by rewrite modnS DIV.
Qed.

(** We show that the fact that [x / h = (x + y) / h] implies that
    [h] is larder than [x mod h + y mod h]. *)
Lemma addmod_le_mod :
  forall x y h,
    h > 0 ->
    x %/ h = (x + y) %/ h ->
    h > x %% h + y %% h.
Proof.
  intros x y h POS EQ.
  move: EQ => /eqP; rewrite divnD // -{1}[x %/ h]addn0 -addnA eqn_add2l eq_sym addn_eq0 => /andP [/eqP Z1 /eqP Z2].
  by move: Z2 => /eqP; rewrite eqb0 -ltnNge => LT.
Qed.

(** We prove that if [x] lies in an interval <<[kT, (k+1)T)>>, then
    [x %/ T] is equal to [k]. *)
Lemma divn_leq :
  forall k T x,
    k * T <= x < k.+1 * T ->
    x %/ T = k.
Proof.
  move => k T x NEQ.
  have [Z|POS] := posnP T.
  { subst; rewrite !muln0 in NEQ; lia. }
  apply/eqP; rewrite -(eqn_pmul2r POS); apply/eqP.
  move: x NEQ; induction k as [| k IHk] => x NEQ; first by rewrite divn_small; lia.
  rewrite -addn1 mulnDl mul1n.
  specialize (IHk (x - T)); feed IHk; first by lia.
  rewrite -IHk {6}(divn_eq T T) modnn addn0.
  by rewrite -mulnDl -divnDr ?dvdnn // subnK //; lia.
Qed.


(** * Floors and Ceilings of Fractions *)

(** We define notions of [div_floor] and [div_ceil]
    and prove a few basic lemmas. *)

(** We define functions [div_floor] and [div_ceil], which are
    divisions rounded down and up, respectively. *)
Definition div_floor (x y : nat) : nat := x %/ y.
Definition div_ceil (x y : nat) := if y %| x then x %/ y else (x %/ y).+1.

(** We start with an observation that [div_ceil 0 b] is equal to [0]
    for any [b]. *)
Lemma div_ceil0 :
  forall b, div_ceil 0 b = 0.
Proof.
  intros b; unfold div_ceil.
  by rewrite dvdn0; apply div0n.
Qed.

(** Next, we show that, given two positive integers [a] and [b],
    [div_ceil a b] is also positive. *)
Lemma div_ceil_gt0 :
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
Lemma div_ceil_monotone1 :
  forall d m n,
    m <= n -> div_ceil m d <= div_ceil n d.
Proof.
  move => d m n LEQ.
  rewrite /div_ceil.
  have LEQd: m %/ d <= n %/ d by apply leq_div2r.
  destruct (d %| m) eqn:Mm; destruct (d %| n) eqn:Mn => //; first by lia.
  rewrite ltn_divRL //.
  apply: (leq_trans _ LEQ).
  move: (leq_divM m d) => LEQm.
  destruct (ltngtP (m %/ d * d) m) as [| |e] => //.
  move: e => /eqP EQ; rewrite -dvdn_eq in EQ.
  by rewrite EQ in Mm.
Qed.

(** Given [T] and [Δ] such that [Δ >= T > 0], we show that [div_ceil Δ T]
    is strictly greater than [div_ceil (Δ - T) T]. *)
Lemma leq_div_ceil_add1 :
  forall Δ T,
    T > 0 -> Δ >= T ->
    div_ceil (Δ - T) T < div_ceil Δ T.
Proof.
  move=> Δ T POS LE. rewrite /div_ceil.
  have lkc: (Δ - T) %/ T < Δ %/ T.
  { rewrite divnBr; last by auto.
    rewrite divnn POS.
    rewrite ltn_psubCl //; lia.
  }
  destruct (T %| Δ) eqn:EQ1.
  { have divck:  (T %| Δ) ->  (T %| (Δ - T)) by auto.
    apply divck in EQ1 as EQ2.
    rewrite EQ2; apply lkc.
  }
  by destruct (T %| Δ - T) eqn:EQ, (T %| Δ) eqn:EQ3; auto.
Qed.

(** We show that the division with ceiling by a constant [T] is a subadditive function. *)
Lemma div_ceil_subadditive :
  forall T, subadditive (div_ceil^~T).
Proof.
  move=> T ab a b SUM.
  rewrite -SUM.
  destruct (T %| a) eqn:DIVa, (T %| b) eqn:DIVb.
  - have DIVab: T %| a + b by apply dvdn_add.
    by rewrite /div_ceil DIVa DIVb DIVab divnDl.
  - have DIVab: T %| a+b = false by rewrite -DIVb; apply dvdn_addr.
    by rewrite /div_ceil DIVa DIVb DIVab divnDl //=; lia.
  - have DIVab: T %| a+b = false by rewrite -DIVa; apply dvdn_addl.
    by rewrite /div_ceil DIVa DIVb DIVab divnDr //=; lia.
  - destruct (T %| a + b) eqn:DIVab.
    + rewrite /div_ceil DIVa DIVb DIVab.
      apply leq_trans with (a %/ T + b %/T + 1); last by lia.
      by apply leq_divDl.
    + rewrite /div_ceil DIVa DIVb DIVab.
      apply leq_ltn_trans with (a %/ T + b %/T + 1); last by lia.
      by apply leq_divDl.
Qed.

(** We observe that when dividing a value exceeding [T * n], then
    the ceiling exceeds [n]. *)
Lemma div_ceil_multiple :
  forall Δ T n,
    T > 0 ->
    (T * n) < Δ ->
    n < div_ceil Δ T.
Proof.
  move=> delta T n GT0 LT.
  rewrite /div_ceil.
  case DIV: (T %| delta);
    first by rewrite -(ltn_pmul2l GT0) [_ * (_ %/ _)]mulnC divnK.
  rewrite -[(_ %/ _).+1]addn1  -divnDMl // -(ltn_pmul2l GT0) [_ * (_ %/ _)]mulnC mul1n.
  by lia.
Qed.

(** We show that for any two integers [a] and [b],
    [a] is less than [a %/ b * b + b] given that [b] is positive. *)
Lemma div_floor_add_g :
  forall a b,
    b > 0 ->
    a < a %/ b * b + b.
Proof.
  move=> a b POS.
  specialize (divn_eq a b) => DIV.
  rewrite [in X in X < _]DIV.
  rewrite ltn_add2l.
  by apply ltn_pmod.
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
  have POS : c > 0 by lia.
  have G : a %% c < c by apply ltn_pmod.
  case (b <= a %% c) eqn:CASE; rewrite -addnBA; auto; rewrite -modnDml.
  - rewrite addnABC; auto.
    by rewrite -modnDmr modnn addn0 modn_small; auto; lia.
  - by rewrite modn_small; lia.
Qed.

