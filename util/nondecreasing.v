From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
Require Export prosa.util.epsilon.
Require Export prosa.util.tactics.
Require Export prosa.util.list.

(** * Non-Decreasing Sequence and Distances *)
(** In this file we prove properties of sorted sequences and the distances
    between consecutive elements. *)

(** TODO: All lemmas in this file unrelated to distances are being contributed
    to MathComp. With the next MathComp release containing these results,
    replace their uses with upstream lemmas, delete the local lemmas, and
    rename this file to [distances.v]. *)

Section NondecreasingSequence.

  (** First, let's introduce the notion of the nth element of a sequence. *)
  Notation "xs [| n |]" := (nth 0 xs n) (at level 30).

  (** A sequence is non-decreasing if its elements are sorted with [leq]. *)
  Definition nondecreasing_sequence (xs : seq nat) := sorted leq xs.

  (** The distances between neighboring elements are their natural-number
      differences. [pairmap] applies subtraction to each consecutive pair,
      starting with the first element and the tail of the sequence.
      For example, [distances [:: 1; 10; 10; 17; 20; 41]] yields
      [[:: 9; 0; 7; 3; 21]]. Empty and singleton sequences have no distances. *)
  Definition distances (xs : seq nat) :=
    pairmap (fun x y => y - x) (head 0 xs) (behead xs).

  (** * Properties of Non-Decreasing Sequence *)
  (** In this section we prove a few lemmas about non-decreasing sequences. *)

  (** No element can lie strictly between two neighboring elements
      and still belong to the list. *)
  Lemma antidensity_of_nondecreasing_seq :
    forall (xs : seq nat) (x : nat) (n : nat),
      nondecreasing_sequence xs ->
      xs[|n|] < x < xs[|n.+1|] ->
      ~~ (x \in xs).
  Proof.
    move=> xs x n SORT /andP [LOW HIGH]; apply/negP=> /(nthP 0) [i i_lt EQ].
    subst x.
    have [N|BAD] := ltnP n.+1 (size xs); last first.
    { by move: HIGH; rewrite [nth 0 xs n.+1]nth_default //. }
    have [LE|GT] := leqP i n.
    - by move: (sorted_leq_nth leq_trans leqnn 0 SORT i n i_lt (ltnW N) LE);
        rewrite leqNgt LOW.
    - by move: (sorted_leq_nth leq_trans leqnn 0 SORT n.+1 i N i_lt GT);
        rewrite leqNgt HIGH.
  Qed.

  (** Note that the last element of a non-decreasing sequence is the max element. *)
  Lemma last_is_max_in_nondecreasing_seq :
    forall (xs : seq nat) (x : nat),
      nondecreasing_sequence xs ->
      (x \in xs) ->
      x <= last 0 xs.
  Proof.
    move=> [ |a xs] x SORT // /(nthP 0) [i LT <-].
    rewrite -nth_last.
    by apply: (sorted_leq_nth leq_trans leqnn 0 SORT); rewrite ?inE /= // -ltnS.
  Qed.

  (** * Properties of [Undup] of Non-Decreasing Sequence *)
  (** We compare elements of a non-decreasing sequence before and after [undup]. *)

  (** Counting from the end, each element of [undup xs] is bounded by
      the corresponding element of the non-decreasing sequence [xs].
      Here [n = 0] selects the last element; indices past the beginning
      saturate at zero. *)
  Lemma undup_nth_le :
    forall xs n,
      nondecreasing_sequence xs ->
      undup xs [| size (undup xs) - n.+1 |]
        <= xs [| size xs - n.+1 |].
  Proof.
    elim=> [ |a [ |b xs] IH] n SORT //.
    move: (SORT) => /andP [AB _].
    move: AB; rewrite leq_eqVlt => /orP [/eqP EQ|LT].
    - subst b; rewrite undup_cons_duplicate.
      apply: leq_trans (IH n (path_sorted SORT)) _.
      rewrite /= !subSS.
      case: n => [ |n]; first by rewrite !subn0 !nth_cons.
      rewrite subSS subnS.
      by case: (size xs - n) => [ |m].
    - rewrite [undup (a :: b :: xs)]/undup ifN.
      + rewrite in_cons negb_or neq_ltn LT /=.
        apply/negP=> IN.
        by move: (allP (order_path_min leq_trans (path_sorted SORT)) _ IN);
          rewrite leqNgt LT.
      + rewrite /= subSS.
        case: (posnP (size (undup (b :: xs)) - n)) => [ZERO|POS].
        * rewrite ZERO /=.
          by apply: (sorted_leq_nth leq_trans leqnn 0 SORT
            0 (size [:: a, b & xs] - n.+1)); rewrite ?inE ?ltn_subrL //=.
        * rewrite [in X in X <= _]nth_cons POS [in X in _ <= X]nth_cons
            (leq_trans POS (leq_sub2r n (size_undup (b :: xs)))).
          rewrite -!subnS.
          exact: IH n (path_sorted SORT).
  Qed.


  (** * Properties of Distances *)
  (** In this section we prove a few lemmas about function [distances]. *)

  (** We begin with a simple lemma that helps us unfold [distances]
      of lists with two consecutive cons [x0::x1::xs]. *)
  Lemma distances_unfold_2cons :
    forall x0 x1 xs,
      distances (x0::x1::xs) = (x1 - x0) :: distances (x1::xs).
  Proof. by []. Qed.

  (** Note that the distances-function has the expected behavior indeed. I.e. an element
      on the position [n] of the distance-sequence is equal to the difference between
      elements on positions [n+1] and [n]. *)
  Lemma function_of_distances_is_correct :
    forall (xs : seq nat) (n : nat),
      (distances xs)[|n|] = xs[|n.+1|] - xs[|n|].
  Proof.
    move=> [ |x xs] n; first by case: n.
    rewrite /distances /=.
    have [LT|GE] := ltnP n (size xs).
    - by rewrite (nth_pairmap 0 0) //.
    - by rewrite (nth_default 0 GE) sub0n nth_default ?size_pairmap.
  Qed.

  (** The sequence of distances has length [(size xs).-1], including
      when [xs] is empty. *)
  Lemma size_of_seq_of_distances :
    forall (xs : seq nat),
      size (distances xs) = (size xs).-1.
  Proof.
    by move=> xs; rewrite /distances size_pairmap size_behead.
  Qed.

  (** We prove that the difference between any two neighboring elements is
      bounded by the max element of the distances-sequence. *)
  Lemma distance_between_neighboring_elements_le_max_distance_in_seq :
    forall (xs : seq nat) (n : nat),
      xs[|n.+1|] - xs[|n|] <= (\max_(x <- distances xs) x).
  Proof.
    move=> xs n.
    rewrite -function_of_distances_is_correct.
    have [LT|GE] := ltnP n (size (distances xs)).
    - by apply: leq_bigmax_seq; [exact: mem_nth | done].
    - by rewrite nth_default.
  Qed.


  (** We prove that [index_iota 0 n] produces a sequence of numbers
      which are always one unit apart from each other. *)
  Lemma distances_of_iota_ε :
    forall n x, x \in distances (index_iota 0 n) -> x = ε.
  Proof.
    move=> n x /(nthP 0) [i LT <-].
    move: LT; rewrite size_of_seq_of_distances /index_iota subn0 size_iota ltn_predRL => LT.
    by rewrite function_of_distances_is_correct !nth_iota ?add0n ?subSnn //; exact: ltnW LT.
  Qed.

  (** * Properties of Distances of Non-Decreasing Sequence *)
  (** In this section, we prove a few basic lemmas about distances of non-decreasing sequences. *)

  (** First we show that the max distance between elements of any nontrivial
      sequence (i.e., a sequence that contains at least two distinct elements)
      is positive. *)
  Lemma max_distance_in_nontrivial_seq_is_positive :
    forall (xs : seq nat),
      nondecreasing_sequence xs ->
      (exists x y, x \in xs /\ y \in xs /\ x <> y) ->
      0 < (\max_(x <- distances xs) x).
  Proof.
    elim => [ |a xs IH] SORT; first by move=> [x [y [INx _]]].
    case: xs IH SORT => [ |b xs] IH SORT [x [y [INx [INy NEQ]]]].
    { move: INx INy; rewrite !in_cons !orbF => /eqP EQx /eqP EQy.
      by subst x y; exfalso; apply: NEQ. }
    have /andP [AB _] := SORT.
    rewrite distances_unfold_2cons big_cons /= leq_max.
    move: AB; rewrite leq_eqVlt => /orP [/eqP EQ|LT].
    - subst b; apply/orP; right; apply: IH; first exact: path_sorted SORT.
      exists x, y; split; first by move: INx; rewrite !in_cons orbA orbb.
      split=> //; by move: INy; rewrite !in_cons orbA orbb.
    - apply/orP; left; by rewrite subn_gt0.
  Qed.

  (** Given a non-decreasing sequence [xs] with length [n], we show that the difference
      between the last element of [xs] and the last element of the distances-sequence
      of [xs] is equal to [xs[n-2]]. *)
  Lemma last_seq_minus_last_distance_seq :
    forall (xs : seq nat),
      nondecreasing_sequence xs ->
      last 0 xs - last 0 (distances xs) = xs [| (size xs).-2 |].
  Proof.
    move=> [ |a [ |b xs]] SORT //; first by rewrite subn0.
    rewrite -!nth_last size_of_seq_of_distances function_of_distances_is_correct /=.
    apply: subKn.
    by apply: (sorted_leq_nth leq_trans leqnn 0 SORT
        (size [:: a, b & xs]).-2 (size [:: a, b & xs]).-1); rewrite ?inE /=.
  Qed.

  (** The max element of the distances-sequence of a sequence [xs]
      is bounded by the last element of [xs]. Since all elements of
      [xs] are non-negative, they all lie within the interval [0, last xs]. *)
  Lemma max_distance_in_seq_le_last_element_of_seq :
    forall (xs : seq nat),
      nondecreasing_sequence xs ->
      (\max_(x <- distances xs) x) <= last 0 xs.
  Proof.
    elim => [ |a [ |b xs] IH] SORT; rewrite ?big_nil //.
    rewrite distances_unfold_2cons big_cons /= geq_max.
    apply/andP; split.
    - apply: leq_trans (leq_subr a b) _.
      by apply: last_is_max_in_nondecreasing_seq SORT _; rewrite !in_cons eqxx orbT.
    - exact: IH (path_sorted SORT).
  Qed.

  (** Let [xs] be a non-decreasing sequence. We prove that
      distances of sequence [[seq ρ <- index_iota 0 k.+1 | ρ \in xs]]
      coincide with sequence [[seq x <- distances xs | 0 < x]]]. *)
  Lemma distances_iota_filtered :
    forall xs k,
      (forall x, x \in xs -> x <= k) ->
      nondecreasing_sequence xs ->
      distances [seq ρ <- index_iota 0 k.+1 | ρ \in xs] = [seq x <- distances xs | 0 < x].
  Proof.
    elim=> [ |a [ |b xs] IH] k Bound SORT.
    - by rewrite filter_pred0.
    - by rewrite index_iota_filter_singl; first (rewrite ltnS; apply: Bound; rewrite in_cons eqxx).
    - have LEa: a <= k by apply: Bound; rewrite in_cons eqxx.
      have LEb: b <= k by apply: Bound; rewrite !in_cons eqxx orbT.
      have M2: forall y, y \in b :: xs -> y <= k.
      { move=> y IN; apply: Bound; by rewrite in_cons IN orbT. }
      have M3: forall y, y \in xs -> b <= y
        by apply/allP; exact: order_path_min leq_trans (path_sorted SORT).
      have /andP [AB _] := SORT.
      move: AB; rewrite leq_eqVlt => /orP [/eqP EQ|LT].
      + subst b; rewrite distances_unfold_2cons subnn [RHS]/= range_filter_2cons.
        by apply: IH; [exact: M2|exact: path_sorted SORT].
      + have M4: forall y, y \in b :: xs -> a < y.
        { move=> y; rewrite in_cons => /orP [/eqP -> //|IN].
          exact: leq_trans LT (M3 _ IN). }
        rewrite distances_unfold_2cons [RHS]/= subn_gt0 LT [RHS]/=.
        rewrite range_iota_filter_step // rem_lt_id //.
        rewrite -(IH k) //; first exact: path_sorted SORT.
        by rewrite {1}range_iota_filter_step // distances_unfold_2cons {1}range_iota_filter_step //.
  Qed.

  (** Let [xs] again be a non-decreasing sequence. We prove that
      distances of sequence [undup xs] coincide with
      sequence of positive distances of [xs]. *)
  Lemma distances_positive_undup :
    forall xs,
      nondecreasing_sequence xs ->
      [seq d <- distances xs | 0 < d] = distances (undup xs).
  Proof.
    move=> xs SORT.
    rewrite -(distances_iota_filtered _ ((\max_(x <- xs) x))); [by move=> x IN; apply: leq_bigmax_seq|exact: SORT| ].
    congr (distances _).
    apply: (irr_sorted_eq ltn_trans ltnn).
    - by apply: (sorted_filter ltn_trans); apply: iota_ltn_sorted.
    - by rewrite ltn_sorted_uniq_leq undup_uniq (undup_sorted leq_trans SORT).
    - move=> x; rewrite mem_filter mem_index_iota leq0n /= mem_undup.
      case IN: (x \in xs) => //=.
      by rewrite ltnS; apply: leq_bigmax_seq.
  Qed.

  (** Consider two sequences [xs] and [ys] of equal length, with [ys]
      non-decreasing. If the first element and all neighboring differences
      of [xs] are bounded by those of [ys], then [xs] is dominated by [ys]. *)
  Lemma domination_of_distances_implies_domination_of_seq :
    forall (xs ys : seq nat),
      head 0 xs <= head 0 ys ->
      size xs = size ys ->
      nondecreasing_sequence ys ->
      (forall n, (distances xs)[|n|] <= (distances ys)[|n|]) ->
      (forall n, xs[|n|] <= ys[|n|]).
  Proof.
    move=> xs ys HEAD EQ SORT LE; elim=> [ |n IH]; first exact: HEAD.
    have [N|GE] := ltnP n.+1 (size xs).
    - move: (LE n); rewrite !function_of_distances_is_correct.
      rewrite EQ in N.
      move: (sorted_leq_nth leq_trans leqnn 0 SORT n n.+1 (ltnW N) N (leqnSn n)).
      by lia.
    - by rewrite !nth_default // -EQ.
  Qed.

End NondecreasingSequence.
