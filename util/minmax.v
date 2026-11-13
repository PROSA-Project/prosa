From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
Require Export prosa.util.notation prosa.util.tactics prosa.util.list prosa.util.setoid.

(** * Additional Lemmas about [\max]. *)

(** For a positive [n], the maximum of any subset of [{0, …, n-1}]
    is smaller than [n], including when the subset is empty. *)
Lemma bigmax_ltn_ord :
  forall (n : nat) (P : pred nat),
    n > 0 ->
    \max_(i < n | P i) i < n.
Proof.
  move=> [|n] P // _.
  by rewrite ltnS; apply/bigmax_leqP => i _; exact: leq_ord.
Qed.

(** Given a predicate [P] and an ordinal [i0 ∈ {0, …, n-1}] satisfying
    [P], we show that the maximum of [{i ∈ {0, …, n-1} | P i}]
    also satisfies [P]. *)
Lemma bigmax_pred :
  forall (n : nat) (P : pred nat) (i0 : 'I_n),
    P i0 ->
    P (\max_(i < n | P i) i).
Proof.
  move=> n P i0 Pi0.
  rewrite (bigmax_eq_arg i0 Pi0).
  by case: arg_maxnP.
Qed.

(** Additionally, we observe that, if two predicates yield different maxima,
    then there must exist a witness that satisfies only one of the
    predicates. *)
Lemma bigmax_witness_diff {T : eqType} :
  forall {xs : seq T} {P1 P2 F},
    \max_(x <- xs | P1 x) F x < \max_(x <- xs | P2 x) F x ->
    exists x, x \in xs /\ ~~ P1 x /\ P2 x.
Proof.
  move=> xs P1 P2 F LT.
  case: (boolP (has (fun x => ~~ P1 x && P2 x) xs))
    => [/hasP [x IN /andP [NPx Px]]|/hasPn NONE]; first by exists x.
  exfalso; move: LT; rewrite ltnNge => /negP; apply.
  apply/bigmax_leqP_seq => x IN Px.
  apply: leq_bigmax_seq => //.
  by move: (NONE x IN); rewrite Px andbT negbK.
Qed.

(** TODO: MathComp's [le_bigmax2_seq] covers this lemma (proposed PR #1672).
    Replace it after adopting the next MathComp release containing that result:
    https://github.com/math-comp/math-comp/pull/1672. *)

(** Given two functions [F1] and [F2], a predicate [P], and sequence
    [xs], we show that if [F1 x <= F2 x] for any [x \in xs] such that
    [P x], then [max] of [{F1 x | ∀ x ∈ xs, P x}] is bounded by the
    [max] of [{F2 x | ∀ x ∈ xs, P x}]. *)
Lemma leq_big_max :
  forall {X : eqType} (F1 F2 : X -> nat) (P : pred X) (xs : seq X),
    (forall x, x \in xs -> P x -> F1 x <= F2 x) ->
    \max_(x <- xs | P x) F1 x <= \max_(x <- xs | P x) F2 x.
Proof.
  move=> X F1 F2 P xs ALL; apply/bigmax_leqP_seq => x IN Px.
  apply: (leq_trans (ALL x IN Px)).
  by apply: leq_bigmax_seq.
Qed.

(** TODO: Replace this lemma with MathComp's [eq_bigmax_seq] after adopting
    the next release containing that result (PR #1652):
    https://github.com/math-comp/math-comp/pull/1652 *)

(** Furthermore, we observe that, if there is any element that satisfies the
    predicate, then there exists a witness for the computed maximum. *)
Lemma bigmax_witness {T : eqType} :
  forall {xs : seq T} {P} F,
    has P xs ->
    exists x, x \in xs /\ P x /\ (F x = \max_(x <- xs | P x) F x).
Proof.
  move=> xs P F HAS.
  have NE : [seq F x | x <- xs & P x] <> [::]
    by apply/eqP; rewrite -size_eq0 size_map size_filter -lt0n -has_count.
  move: (bigmax_mem _ NE).
  rewrite big_map big_filter => /mapP [x IN MAX].
  move: IN; rewrite mem_filter => /andP [Px IN].
  by exists x; repeat split=> //; rewrite MAX.
Qed.
