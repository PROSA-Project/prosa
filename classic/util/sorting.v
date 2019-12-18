Require Import prosa.classic.util.tactics prosa.classic.util.induction prosa.classic.util.list.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(** * Sorting *)
(** In this modeule we prove a few lemmas about sorted sequences. *)
Section Sorting.

  Section SortedImplLeIdx.
    
    (* Consider an arbitrary type T... *)
    Variable T: eqType.

    (* ... and some binary relation leT (≺) on it. *)
    Variable leT: rel T.
    Notation "x ≺ y" := (leT x y) (at level 30).
    Let sorted xs := sorted leT xs.
    
    (* Next, let xs be a sequence of elements of type T. *)
    Variable xs: seq T.
    
    (* Since Coq requires all functions to be total, we 
       need to specify a default value for cases when 
       an index exceeds the size of the sequence. *)
    Variable default: T.
    Let nth := nth default.

    (* Next, let's introduce a notation for the nth element of a sequence. *)
    Notation "xs [| n |]" := (nth xs n) (at level 10).
    
    (* We prove that, given the fact that sequence xs is sorted, 
       the i'th element of xs is ≺ than the i+1'th element. *)
    Lemma sort_ordered:
      forall (idx: nat),
        sorted xs ->
        idx < (size xs).-1 ->
        xs[|idx|] ≺ xs[|idx.+1|].
    Proof.
      intros idx SORT LT.
      induction xs; first by rewrite /= ltn0 in LT.
      simpl in SORT, LT; move: SORT => /pathP SORT.
        by simpl; apply SORT.
    Qed.

    (* Next we prove that the prefix of a sorted sequence is also sorted. *)
    Lemma sorted_rcons_prefix:
      forall x,
        sorted (rcons xs x) ->
        sorted xs.
    Proof.
      intros x SORT; destruct xs; simpl; first by ins.
      rewrite rcons_cons /= rcons_path in SORT.
        by move: SORT => /andP [PATH _].
    Qed.

    (* Let's assume that relation leT (≺) is transitive. *)
    Hypothesis H_leT_is_transitive: transitive leT.
    
    (* Given the fact that sequence xs is sorted, we prove that 
       the last elements of the sequence is the max. element. *) 
    Lemma order_sorted_rcons:
      forall (x lst: T),
        sorted (rcons xs lst) ->
        x \in xs ->
        x ≺ lst.
    Proof.
      intros x last SORT IN.
      induction xs as [ | a xs']; [ | clear xs; rename xs' into xs]; first by rewrite in_nil in IN.
      simpl in SORT; move: IN; rewrite in_cons; move => /orP IN.
      destruct IN as [HEAD | TAIL];
        last by apply IHxs'; [by apply path_sorted in SORT| by ins].
      move: HEAD => /eqP HEAD; subst a.
      apply order_path_min in SORT; last by ins.
      move: SORT => /allP SORT.
        by apply SORT; rewrite mem_rcons in_cons; apply/orP; left.
    Qed.

    (* Next, we prove that for sorted sequence xs and for any
       two indices i1 and i2, i1 < i2 implies xs[|i1|] ≺ xs[|i2|]. *) 
    Lemma sorted_lt_idx_implies_rel:
      forall  i1 i2,
        sorted xs ->
        i1 < i2 ->
        i2 < size xs ->
        xs[|i1|] ≺ xs [|i2|].
    Proof.
      intros i1 i2 SORT LE LEsize.
      generalize dependent i2; rewrite leq_as_delta.
      intros delta LT.
      destruct xs as [ | a xs']; [ | clear xs; rename xs' into xs]; first by rewrite ltn0 in LT.
      simpl in SORT.
      induction delta;
        first by rewrite /= addn0 ltnS in LT; rewrite /= -addnE addn0; apply/pathP.
      {
        rewrite /transitive (H_leT_is_transitive (nth (a :: xs) (i1.+1 + delta))) //;
                first by apply IHdelta, leq_ltn_trans with (n := i1.+1 + delta.+1); [rewrite leq_add2l| ].
        rewrite -[delta.+1]addn1 addnA addn1.
        move: SORT => /pathP SORT; apply SORT.
          by rewrite /= -[delta.+1]addn1 addnA addn1 ltnS in LT.
      }
    Qed.

    (* Finally, assuming that (1) xs is sorted and contains
       no duplicates, (2) ≺ is antisymmetric and transitive,
       we prove that x[|i1|] ≺ x[|i2|] implies i1 ≤ i2. *)
    Lemma sorted_rel_implies_le_idx:
      forall i1 i2,
        uniq xs ->
        antisymmetric_over_list leT xs ->
        sorted xs ->
        xs[|i1|] ≺ xs[|i2|] ->
        i1 < size xs ->
        i2 < size xs ->
        i1 <= i2.
    Proof.
      intros i1 i2 UNIQ ANTI SORT REL SIZE1 SIZE2.
      generalize dependent i2.
      induction i1; first by done.
      {
        intros i2 REL SIZE2.
        feed IHi1; first by apply ltn_trans with (n := i1.+1).
        apply leq_trans with (n := i1.+1); first by done.
        rewrite ltn_neqAle; apply/andP; split.
        {
          apply/eqP; red; intro BUG; subst.
          assert (REL': leT (nth xs i2) (nth xs i2.+1)).
            by apply sorted_lt_idx_implies_rel; rewrite // ltnSn.
            rewrite /antisymmetric_over_list in ANTI.
            exploit (ANTI (nth xs i2) (nth xs i2.+1)); rewrite ?mem_nth //.
            move => /eqP EQ; rewrite nth_uniq in EQ; try (by done).
              by rewrite -[_ == _]negbK in EQ; move: EQ => /negP EQ; apply EQ; apply/eqP.
        }
        {
          apply IHi1; last by done.
          rewrite /transitive (H_leT_is_transitive (nth xs i1.+1)) //.
            by apply sorted_lt_idx_implies_rel; try (by done); apply ltnSn.
        }
      }
    Qed.

  End SortedImplLeIdx.

  (* Let F be a function from some type to natural numbers. Then for a 
     sequence xs, the fact that [∀ i: F(xs[i]) ≤ F(xs[i+1])] implies that 
     [forall i k: F(xs[i]) ≤ F(xs[i + k])]. *) 
  Lemma prev_le_next:
    forall {T: Type} (F: T -> nat) (xs: seq T) (def: T) (i k: nat),
      (forall i, i < (size xs).-1 -> F (nth def xs i) <= F (nth def xs i.+1)) ->
      (i + k <= (size xs).-1) ->
      F (nth def xs i) <= F (nth def xs (i+k)).
  Proof.
    intros T F r x i k ALL SIZE.
    generalize dependent i. generalize dependent k.
    induction k; intros; first by rewrite addn0 leqnn.
    specialize (IHk i.+1); exploit IHk; [by rewrite addSnnS | intro LE].
    apply leq_trans with (n := F (nth x r (i.+1)));
      last by rewrite -addSnnS.
    apply ALL, leq_trans with (n := i + k.+1); last by ins.
      by rewrite addnS ltnS leq_addr.
  Qed.
  
End Sorting.