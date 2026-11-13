From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
Require Export mathcomp.boot.path mathcomp.zify.zify.

Require Import prosa.util.tactics.
Require Export prosa.util.supremum.

(** * Last Elements and Maxima of Sequences *)

(** Removing duplicates preserves the last element. *)
Lemma last_undup {T : eqType} (d : T) (xs : seq T) :
  last d (undup xs) = last d xs.
Proof. by case/lastP: xs => [//|ys x]; rewrite undup_rcons !last_rcons. Qed.

(** The last element is bounded by the maximum. *)
Lemma last_le_bigmax :
  forall xs, last 0 xs <= \max_(x <- xs) x.
Proof.
  case=> [|x xs]; first by rewrite big_nil.
  by apply: leq_bigmax_seq; [exact: mem_last | done].
Qed.

(** If every element in a set [ys] is greater than the corresponding element
    in another set [xs] then the maxima of [ys] is also greater than the
    maxima of [xs]. *)
Lemma bigmax_leq_nth :
  forall xs ys,
    (forall n, nth 0 xs n <= nth 0 ys n) ->
    (\max_(x <- xs) x) <= \max_(y <- ys) y.
Proof.
  move=> xs ys LE; apply/bigmax_leqP_seq => x /(nthP 0) [i LT <-] _.
  apply: leq_trans (LE i) _.
  case: (ltnP i (size ys)) => LTys; last by rewrite nth_default.
  by apply: leq_bigmax_seq; [exact: mem_nth | done].
Qed.

(** * Misc. Additional Lemmas about Sequences *)

(** If no element satisfies [P], filtering yields the empty sequence. *)
Lemma filter_in_pred0 :
  forall {X : eqType} (xs : seq X) (P : pred X),
    (forall x, x \in xs -> ~~ P x) ->
    filter P xs = [::].
Proof.
  move=> X xs P NONE; apply/eqP/negPn; rewrite -has_filter.
  exact/hasPn.
Qed.

(** We show that in a unique sequence of size greater than one
    there exist two unique elements.  *)
Lemma exists_two :
  forall {X : eqType} (xs : seq X),
    size xs > 1 ->
    uniq xs ->
    exists a b, a <> b /\ a \in xs /\ b \in xs.
Proof.
  move=> T [|a [|b xs]] //= _ /andP[NA _].
  exists a, b; split; first by apply/eqP; move: NA; rewrite in_cons negb_or => /andP[].
  by split; rewrite !in_cons eqxx ?orbT.
Qed.

(** If [head 0 xs <= x < last 0 xs], then some neighboring elements
    bracket [x]. The sequence [xs] need not be sorted. *)
Lemma belonging_to_segment_of_seq_is_total :
  forall (xs : seq nat) (x : nat),
    head 0 xs <= x < last 0 xs ->
    exists n,
      n.+1 < size xs
      /\ nth 0 xs n <= x < nth 0 xs n.+1.
Proof.
  move=> xs x; elim: xs => [//|a xs IH].
  case: xs IH => [|b xs] IH /= /andP[ha hl]; first by move: hl; rewrite ltnNge ha.
  case: (leqP b x) => [bx|xb]; last by exists 0; split=> //; rewrite ha xb.
  have /IH [i [ilt hi]] : b <= x < last b xs by rewrite bx hl.
  by exists i.+1; split.
Qed.

(** * Additional Lemmas about [sorted] *)

(** We show that if [[x | x ∈ xs : P x]] is sorted with respect to
    values of some function [f], then it can be split into two parts:
    [[x | x ∈ xs : P x /\ f x <= t]] and [[x | x ∈ xs : P x /\ f x <= t]]. *)
Lemma sorted_split :
  forall {X : eqType} (xs : seq X) P f t,
    sorted (fun x y => f x <= f y) xs ->
    [seq x <- xs | P x] = [seq x <- xs | P x & f x <= t] ++ [seq x <- xs | P x & f x > t].
Proof.
  clear; move=> X xs P f t; elim: xs => [//|a xs IHxs] /= SORT.
  have TR : transitive (T:=X) (fun x y : X => f x <= f y).
  { intros ? ? ? LE1 LE2; lia. }
  destruct (P a) eqn:Pa, (leqP (f a) t) as [R1 | R1]; simpl.
  { erewrite IHxs; first by reflexivity.
    by eapply path_sorted; eauto. }
  { erewrite IHxs; last by eapply path_sorted; eauto.
    replace ([seq x <- xs | P x & f x <= t]) with (@nil X); first by done.
    symmetry; move: SORT; rewrite path_sortedE // => /andP [ALL SORT].
    apply filter_in_pred0; intros ? IN; apply/negP; intros H; move: H => /andP [Px LEx].
    by move: ALL => /allP ALL; specialize (ALL _ IN); simpl in ALL; lia.
  }
  { by eapply IHxs, path_sorted; eauto. }
  { by eapply IHxs, path_sorted; eauto. }
Qed.

(** * Additional Lemmas about [last] *)

(** We show that if a sequence [xs] contains an element that
    satisfies a predicate [P], then the last element of [filter P xs]
    is in [xs]. *)
Lemma filter_last_mem :
  forall {X : eqType} (xs : seq X) (d : X) (P : pred X),
    has P xs ->
    last d (filter P xs) \in xs.
Proof.
  move=> X xs d P; rewrite has_filter.
  case EQ: (filter P xs) => [//|a ys] _ /=.
  move: (mem_last a ys).
  by rewrite -EQ mem_filter => /andP[].
Qed.

(** * Range of Indices *)

(** To have a more intuitive naming, we introduce the definition of
    [range a b] which is equal to [index_iota a b.+1]. *)
Definition range (a b : nat) := index_iota a b.+1.

(** In the following, we establish some lemmas about [index_iota] and [range]
    for lists. *)

(** Splitting [index_iota t1 t2] at [t] yields two concatenated iotas. *)
Lemma index_iota_cat :
  forall t t1 t2,
    t1 <= t <= t2 ->
    index_iota t1 t2 = index_iota t1 t ++ index_iota t t2.
Proof.
  move=> t t1 t2 /andP [LE1 LE2]; rewrite /index_iota.
  have -> : t2 - t1 = (t - t1) + (t2 - t) by lia.
  by rewrite iotaD (subnKC LE1).
Qed.

(** Filtering an interval by a sequence whose minimum is [x] yields [x]
    followed by the interval filtered by the values other than [x]. *)
Lemma index_iota_filter_step :
  forall x xs a b,
    a <= x < b ->
    (forall y, y \in xs -> x <= y) ->
    [seq ρ <- index_iota a b | ρ \in x :: xs]
    = x :: [seq ρ <- index_iota a b | ρ \in filter (predC1 x) xs].
Proof.
  move=> x xs a b /andP [AX XB] MIN.
  have PRE : [seq y <- index_iota a x | y \in x :: xs] = [::].
  { apply: filter_in_pred0 => y.
    rewrite mem_index_iota in_cons => /andP [_ YX].
    apply/negP => /orP [/eqP EQ | /MIN XY]; lia. }
  have -> : [seq y <- index_iota a b | y \in filter (predC1 x) xs]
      = filter (predC1 x) [seq y <- index_iota a b | y \in x :: xs].
  { rewrite -filter_predI; apply: eq_filter => y.
    by rewrite mem_filter /predI /predC1 /= in_cons; case: (y == x). }
  rewrite (index_iota_cat x) ?AX ?(ltnW XB) // filter_cat PRE /=.
  rewrite /index_iota -(subnSK XB) /= in_cons eqxx /= /predC1 /= eqxx /=.
  congr (x :: _); symmetry; apply/all_filterP/allP => y.
  rewrite mem_filter mem_iota => /andP [_ /andP [XY _]].
  by apply/eqP; lia.
Qed.

(** * Additional Lemmas about [count] *)

(** The count of a union equals the sum of the individual counts minus
    the count of their intersection. This form supports direct rewriting. *)
Lemma count_predUI' :
  forall (P1 P2 : pred nat) (xs : seq nat),
    count (predU P1 P2) xs = count P1 xs + count P2 xs - count (predI P1 P2) xs.
Proof.
  by move=> P1 P2 xs; rewrite -(count_predUI P1 P2 xs) addnK.
Qed.

(** * Shifting Sequences of Natural Numbers *)

(** We define a helper function that shifts a sequence of numbers "forward" by a
    constant offset, and an analogous version that shifts them "backwards,"
    removing any number that, in the absence of Rocq's saturating subtraction,
    would become negative. These functions are useful in transforming abstract RTA's
    search space. *)
Definition shift_points_pos (xs : seq nat) (s : nat) : seq nat :=
  map (addn s) xs.
Definition shift_points_neg (xs : seq nat) (s : nat) : seq nat :=
  let nonsmall := filter (fun x => x >= s) xs in
  map (fun x => x - s) nonsmall.

(** * Upstream Replacements and Dependent Results *)

(** TODO: MathComp's [last_filter] covers this lemma (merged PR #1649).
    Replace it after adopting the next MathComp release containing that result:
    https://github.com/math-comp/math-comp/pull/1649. *)

(** Filtering preserves the last element if it satisfies the predicate. *)
Lemma last_filter {T : Type} (d : T) (xs : seq T) (P : pred T) :
  P (last d xs) -> last d [seq x <- xs | P x] = last d xs.
Proof.
  case/lastP: xs => [//|ys x].
  by rewrite last_rcons => Px; rewrite filter_rcons Px last_rcons.
Qed.

(** TODO: MathComp's [sub_in_count] covers this lemma (merged PR #1649).
    Replace it after adopting the next MathComp release containing that result:
    https://github.com/math-comp/math-comp/pull/1649. *)

(** If [f] implies [g] for all elements in [xs], then the number of
    elements in [xs] satisfying [f] is less than or equal to the
    number of elements satisfying [g]. *)
Lemma sub_count_seq :
  forall {X : eqType} (f g : pred X) (xs : seq X),
    {in xs, forall x, f x -> g x} ->
    count f xs <= count g xs.
Proof.
  move=> X f g xs LE; rewrite -!size_filter -!sum1_size !big_filter.
  rewrite big_seq_cond [leqRHS]big_seq_cond big_mkcond [leqRHS]big_mkcond.
  apply leq_sum => t _; destruct (_ \in _) eqn:IN, (f t) eqn:FT, (g t) eqn:GT => //.
  by move: (LE _ IN); rewrite FT GT => FA.
Qed.

(** TODO: MathComp's [eq_bigmax_seq] subsumes this lemma (merged PR #1652).
    Replace it after adopting the next MathComp release containing that result:
    https://github.com/math-comp/math-comp/pull/1652. *)

(** The maximum of a nonempty sequence belongs to the sequence. *)
Lemma bigmax_mem :
  forall xs : seq nat, xs <> [::] -> (\max_(x <- xs) x) \in xs.
Proof.
  elim=> [//|a xs IH] _; rewrite big_cons.
  case: xs IH => [|b xs IH]; first by rewrite big_nil maxn0 mem_head.
  case: (leqP a (\max_(x <- b :: xs) x)) => LE.
  - by rewrite in_cons IH // orbT.
  - by rewrite mem_head.
Qed.

(** This local corollary is kept alongside [bigmax_mem] because its proof
    uses that lemma. Adapt the proof when replacing [bigmax_mem] with
    MathComp's [eq_bigmax_seq]. *)

(** A nonempty sequence whose elements all equal [k] has maximum [k]. *)
Lemma bigmax_of_uniform_seq :
  forall k xs,
    size xs > 0 ->
    (forall x, x \in xs -> x = k) ->
    (\max_(x <- xs) x) = k.
Proof.
  move=> k xs POS ALL; apply: ALL; apply: bigmax_mem.
  by case: xs POS.
Qed.
