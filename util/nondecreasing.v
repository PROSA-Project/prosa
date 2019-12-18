Require Export prosa.util.epsilon.
Require Export prosa.util.nat.
Require Export prosa.util.list.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Non-Decreasing Sequence and Distances *)
(** In this file we introduce the notion of a non-decreasing sequence. *)
Section NondecreasingSequence.

  (** First, let's introduce the notion of the nth element of a sequence. *)
  Notation "xs [| n |]" := (nth 0 xs n) (at level 30).
  
  (** In this section we provide the notion of a non-decreasing sequence. *)
  Section Definitions. 
    
    (** We say that a sequence [xs] is non-decreasing iff for any two indices [n1] and [n2] 
       such that [n1 <= n2 < size [xs]] condition [[xs][n1] <= [xs][n2]] holds. *)
    Definition nondecreasing_sequence (xs : seq nat) :=
      forall n1 n2,
        n1 <= n2 < size xs ->
        xs[|n1|] <= xs[|n2|].
    
    (** Similarly, we define an increasing sequence. *)
    Definition increasing_sequence (xs : seq nat) :=
      forall n1 n2,
        n1 < n2 < size xs ->
        xs[|n1|] < xs[|n2|].

    (** For a non-decreasing sequence we define the notion of 
        distances between neighboring elements of the sequence. *)
    (** Example:
        Consider the following sequence of natural numbers: [xs] = [:: 1; 10; 10; 17; 20; 41]. 
        Then [drop 1 xs] is equal to [:: 10; 10; 17; 20; 41].
        Then [zip xs (drop 1 xs)] is equal to [:: (1,10); (10,10); (10,17); (17,20); (20,41)]
        And after the mapping [map (fun '(x1, x2) => x2 - x1)] we end up with [:: 9; 0; 7; 3; 21]. *)
    Definition distances (xs : seq nat) :=
      map (fun '(x1, x2) => x2 - x1) (zip xs (drop 1 xs)).

  End Definitions.
 
  (** * Properties of Increasing Sequence *) 
  (** In this section we prove a few lemmas about increasing sequences. *)
  Section IncreasingSequence.

    (** Note that a filtered iota sequence is an increasing sequence. *)
    Lemma iota_is_increasing_sequence:
      forall a b P,
        increasing_sequence [seq x <- index_iota a b | P x].
    Proof.
      clear; intros ? ? ?.
      have EX : exists k, b - a <= k.
      { exists (b-a); now simpl. } destruct EX as [k BO].
      revert a b P BO; induction k.
      { move => a b P BO n1 n2.
        move: BO; rewrite leqn0; move => /eqP BO.
        rewrite /index_iota BO; simpl.
          by move => /andP [_ F].
      } 
      { move => a b P BO n1 n2 /andP [GE LT].
        case: (leqP b a) => [N|N].
        - move: N; rewrite -subn_eq0; move => /eqP EQ.
          rewrite /index_iota EQ //= in LT.
        - rewrite index_iota_lt_step; last by done.
          simpl; destruct (P a) eqn:PA.
          + destruct n1, n2; try done; simpl.
            * apply iota_filter_gt; first by done.
              rewrite index_iota_lt_step // //= PA //= in LT.
            * apply IHk; try ssromega.
              apply/andP; split; first by done.
              rewrite index_iota_lt_step // //= PA //= in LT.
          + apply IHk; try ssromega.
            apply/andP; split; first by done.
            rewrite index_iota_lt_step // //= PA //= in LT.
      } 
    Qed.

    (** We prove that any increasing sequence is also a non-decreasing
        sequence. *)
    Lemma increasing_implies_nondecreasing:
      forall xs,
        increasing_sequence xs ->
        nondecreasing_sequence xs.
    Proof.
      intros ? INC.
      intros n1 n2.
      move => /andP; rewrite leq_eqVlt; move => [/orP [/eqP EQ| LT1] LT2].
      - by subst.
      - by apply ltnW; apply INC; apply/andP; split.
    Qed.

  End IncreasingSequence.
  
  (** * Properties of Non-Decreasing Sequence *) 
  (** In this section we prove a few lemmas about non-decreasing sequences. *)
  Section NonDecreasingSequence.

    (** First we prove that if [0 ∈ xs], then 
        [0] is the first element of [xs]. *) 
    Lemma nondec_seq_zero_first:
      forall xs,
        (0 \in xs) -> 
        nondecreasing_sequence xs -> 
        first0 xs = 0.
    Proof.
      destruct xs as [ | x xs]; first by done.
      destruct x as [ | x]; first by done.
      rewrite in_cons; move => /orP [/eqP EQ | IN] ND; first by done.
      exfalso.
      have NTH := nth_index 0 IN.
      specialize (ND 0 (index 0 xs).+1).
      feed ND.      
      { apply/andP; split; first by done.      
          by simpl; rewrite ltnS index_mem. }
        by simpl in ND; rewrite NTH in ND.
    Qed.
    
    (** If [x1::x2::xs] is a non-decreasing sequence, then either 
        [x1 = x2] or [x1 < x2]. *)
    Lemma nondecreasing_sequence_2cons_leVeq:
      forall x1 x2 xs, 
        nondecreasing_sequence (x1 :: x2 :: xs) ->
        x1 = x2 \/ x1 < x2.
    Proof.
      intros ? ? ? ND.
      destruct (ltngtP x1 x2) as [LT | GT | EQ]; auto.
      move_neq_down GT.
        by specialize (ND 0 1); apply ND.
    Qed.
    
    (** We prove that if [x::xs] is a non-decreasing sequence,
        then [xs] also is a non-decreasing sequence. *)
    Lemma nondecreasing_sequence_cons:
      forall x xs, 
        nondecreasing_sequence (x :: xs) ->
        nondecreasing_sequence xs.
    Proof.
      intros ? ? ND.
      move => n1 n2 /andP [LT1 LT2].
      specialize (ND n1.+1 n2.+1).
      apply ND.
      apply/andP; split.
      - by rewrite ltnS.
      - by simpl; rewrite ltnS. 
    Qed.

    (** Let [xs] be a non-decreasing sequence, 
        then for [x] s.t. [∀ y ∈ xs, x ≤ y] 
        [x::xs] is a non-decreasing sequence. *)
    Lemma nondecreasing_sequence_add_min: 
      forall x xs,
        (forall y, y \in xs -> x <= y) -> 
        nondecreasing_sequence xs ->
        nondecreasing_sequence (x :: xs).
    Proof.
      intros x xs MIN ND [ |n1] [ | n2]; try done.
      - move => /andP [_ S]; simpl.
        apply leq_trans with (xs [| 0 |]).
        + apply MIN; apply mem_nth.
          simpl in *. rewrite ltnS in S.
            by apply leq_ltn_trans with n2.
        + apply ND; apply/andP; split; auto.
      - simpl; rewrite !ltnS.
          by apply ND.
    Qed.

    (** We prove that if [x::xs] is a non-decreasing sequence,
        then [x::x::xs] also is a non-decreasing sequence. *)
    Lemma nondecreasing_sequence_cons_double:
      forall x xs, 
        nondecreasing_sequence (x :: xs) ->
        nondecreasing_sequence (x :: x :: xs).
    Proof.
      intros ? ? ND.
      move => [ | n1] [ | n2] /andP [LT1 LT2]; try done.
      - specialize (ND 0 n2); simpl in ND.
        apply ND.
          by simpl in LT2; rewrite ltnS in LT2.
      - apply ND.
        apply/andP; split.
        + by rewrite ltnS in LT1.
        + by simpl in LT2; rewrite ltnS in LT2.
    Qed.
    
    (** We prove that if [x::xs] is a non-decreasing sequence,
        then [x] is a minimal element of [xs]. *)
    Lemma nondecreasing_sequence_cons_min:
      forall x xs, 
        nondecreasing_sequence (x :: xs) ->
        (forall y, y \in xs -> x <= y).
    Proof.
      intros ? ? ND ? IN.
      have IDX := nth_index 0 IN.
      specialize (ND 0 (index y xs).+1).
      move: (IN) => IDL; rewrite -index_mem in IDL.
      feed ND.
      { apply/andP; split; first by done.
          by simpl; rewrite ltnS.
      }
      eapply leq_trans; first by apply ND.
        by simpl; rewrite IDX.
    Qed.

    (** We also prove a similar lemma for strict minimum. *)
    Corollary nondecreasing_sequence_cons_smin:
      forall x1 x2 xs,
        x1 < x2 -> 
        nondecreasing_sequence (x1 :: x2 :: xs) ->
        (forall y, y \in x2 :: xs -> x1 < y).
    Proof.
      intros ? ? ? LT ND ? IN.
      eapply leq_trans; first by apply LT.
      apply nondecreasing_sequence_cons in ND.
      eapply nondecreasing_sequence_cons_min; last by apply IN.
        by apply nondecreasing_sequence_cons_double.
    Qed.
    
    (** Next, we prove that no element can lie strictly between two 
        neighboring elements and still belong to the list. *)
    Lemma antidensity_of_nondecreasing_seq:
      forall (xs : seq nat) (x : nat) (n : nat),
        nondecreasing_sequence xs ->
        xs[|n|] < x < xs[|n.+1|] ->
        ~~ (x \in xs).
    Proof.
      intros ? ? ? STR ?; apply/negP; intros ?. 
      move: H0 => /nthP.  intros GG.
      specialize (GG 0). 
      move: GG => [ind LE HHH].
      subst x; rename ind into x.                 
      destruct (n.+1 < size xs) eqn:Bt; last first.
      { move: Bt => /negP /negP; rewrite -leqNgt; move => Bt.
        apply nth_default with (x0 := 0) in Bt. 
        rewrite Bt in H; by move: H => /andP [_ T]. }
      have B1: n.+1 < size xs; first by done. clear Bt.
      have B2: n < size xs; first by apply leq_ltn_trans with n.+1.          
      have GT: n < x.
      { move: H => /andP [T _].
        rewrite ltnNge; apply/negP; intros CONTR.
        specialize (STR x n).
        feed STR. by apply/andP; split.
          by move: STR; rewrite leqNgt; move => /negP STR; apply: STR.
      }
      have LT: x < n.+1.
      { clear GT.
        move: H => /andP [_ T].
        rewrite ltnNge; apply/negP; intros CONTR.
        move: CONTR; rewrite leq_eqVlt; move => /orP [/eqP EQ | CONTR].
        { by subst; rewrite ltnn in T. }
        specialize (STR n.+1 x).
        feed STR. by apply/andP; split; [ apply ltnW | done].
          by move: STR; rewrite leqNgt; move => /negP STR; apply: STR.
      }
        by move: LT; rewrite ltnNge; move => /negP LT; apply: LT.
    Qed.
    
    (** Alternatively, consider an arbitrary natural number x that is 
       bounded by the first and the last element of a sequence [xs]. Then 
       there is an index n such that [xs[n] <= x < x[n+1]]. *)
    Lemma belonging_to_segment_of_seq_is_total:
      forall (xs : seq nat) (x : nat), 
        2 <= size xs -> 
        first0 xs <= x < last0 xs ->
        exists n,
          n.+1 < size xs /\
          xs[|n|] <= x < xs[|n.+1|].
    Proof.
      intros ? ? SIZE LAST.
      have EX: exists n, size xs <= n by exists (size xs). move: EX => [n LE].
      destruct n; first by destruct xs.
      destruct n; first by destruct xs; last destruct xs. 
      generalize dependent xs.
      induction n; intros.
      { by destruct xs; [ | destruct xs; [ | destruct xs; [exists 0 | ] ] ]. }
      { destruct xs; [ | destruct xs; [ | ]]; try by done. 
        destruct xs.
        { by exists 0; simpl in *. }
        destruct (leqP n1 x) as [NEQ|NEQ]; last first.
        { exists 0; split; auto. move: LAST => /andP [LAST _]. by apply/andP; split. } 
        { specialize (IHn [:: n1, n2 & xs]).
          feed_n 3 IHn.
          { by done. } 
          { move: LAST => /andP [LAST1 LAST2].
            apply/andP; split; first by done.
            apply leq_trans with (last0 [:: n0, n1, n2 & xs]); first by done.
              by rewrite /last0 !last_cons.
          }
          { by rewrite -(ltn_add2r 1) !addn1. }
          move: IHn => [idx [SI /andP [G L]]].
          exists idx.+1; split.
          - by simpl in *; rewrite -addn1 -[in X in _ <= X]addn1 leq_add2r.
          - by apply/andP; split.
        }
      }
    Qed.

    (** Note that the last element of a non-decreasing sequence is the max element. *)
    Lemma last_is_max_in_nondecreasing_seq:
      forall (xs : seq nat) (x : nat),
        nondecreasing_sequence xs ->
        (x \in xs) -> 
        x <= last0 xs.
    Proof.
      clear; intros ? ? STR IN. 
      have NEQ: forall x y, x = y \/ x != y.
      { clear. intros.
        destruct (x == y) eqn:EQ.
        - by left; apply/eqP.
        - by right.
      }
      move: (NEQ _ x (last0 xs)); clear NEQ; move => [EQ|NEQ].
      { by subst x. }
      move: IN => /nthP EX.
      specialize (EX 0). 
      move: EX => [id SIZE EQ].
      rewrite /last0 -nth_last -EQ; subst x.      
      rewrite -addn1 in SIZE.
      apply STR; apply/andP.
      have POS: 0 < size xs.
      { by apply leq_trans with (id + 1); [rewrite addn1| done]. }
      split.
      - by rewrite -(leq_add2r 1) !addn1 prednK // -addn1.
      - by rewrite prednK.
    Qed.
    
  End NonDecreasingSequence.

  (** * Properties of [Undup] of Non-Decreasing Sequence *)
  (** In this section we prove a few lemmas about [undup] of non-decreasing sequences. *)
  Section Undup.

    (** First we prove that [undup x::x::xs] is equal to [undup x::xs]. *)
    Remark nodup_sort_2cons_eq:
      forall {X : eqType} (x : X) (xs : seq X),
        undup (x::x::xs) = undup (x::xs).
    Proof.
      intros; rewrite {2 3}[cons] lock //= -lock.
      rewrite in_cons eq_refl; simpl.
        by destruct (x \in xs).
    Qed.

    (** For non-decreasing sequences we show that the fact that 
        [x1 < x2] implies that [undup x1::x2::xs = x1::undup x2::xs]. *)
    Lemma nodup_sort_2cons_lt:
      forall x1 x2 xs,
        x1 < x2 ->
        nondecreasing_sequence (x1::x2::xs) -> 
        undup (x1::x2::xs) = x1 :: undup (x2::xs).
    Proof.
      intros; rewrite {2 3 4}[cons] lock //= -lock.
      rewrite in_cons.
      have -> : (x1 == x2) = false.
      { by apply/eqP/eqP; rewrite neq_ltn; rewrite H. }
      rewrite [cons]lock //= -lock.
      have -> : (x1 \in xs) = false; last by done.    
      apply/eqP; rewrite eqbF_neg.
      apply nondecreasing_sequence_cons in H0.
      apply/negP; intros ?; eauto 2.
      eapply nondecreasing_sequence_cons_min in H0; eauto 2.
        by move_neq_down H.
    Qed.

    (** Next we show that function [undup] doesn't change 
        the last element of a sequence. *)
    Lemma last0_undup:
      forall xs,
        nondecreasing_sequence xs -> 
        last0 (undup xs) = last0 xs.
    Proof.
      induction xs as [ | x1 xs]; first by done.
      intros ND; destruct xs as [ |x2 xs]; first by done.
      destruct (nondecreasing_sequence_2cons_leVeq _ _ _ ND) as [EQ|LT].
      + subst; rename x2 into x.
        rewrite nodup_sort_2cons_eq IHxs.
        rewrite [in X in _ = X]last0_cons //.
        eapply nondecreasing_sequence_cons; eauto 2.
      + rewrite nodup_sort_2cons_lt // last0_cons.
        rewrite IHxs //; eauto using nondecreasing_sequence_cons.
          by intros ?; apply undup_nil in H.
    Qed.

    (** Non-decreasing sequence remains non-decreasing after application of [undup]. *)
    Lemma nondecreasing_sequence_undup:
      forall xs,
        nondecreasing_sequence xs -> 
        nondecreasing_sequence (undup xs).
    Proof.
      intros ?.
      have EX: exists len, size xs <= len.
      { exists (size xs); now simpl. } destruct EX as [n BO].
      revert xs BO; induction n.   
      - by intros xs; rewrite leqn0 size_eq0; move => /eqP EQ; subst xs.
      - intros [ |x1 [ | x2 xs]]; try done. 
        intros Size NonDec.        
        destruct (nondecreasing_sequence_2cons_leVeq _ _ _ NonDec) as [EQ|LT].
        * subst; rename x2 into x.
            by rewrite nodup_sort_2cons_eq; apply IHn; eauto using nondecreasing_sequence_cons.
        * rewrite nodup_sort_2cons_lt //.
          apply nondecreasing_sequence_add_min.
          intros ? ?.
          eapply nondecreasing_sequence_cons_min with (y := y) in NonDec; auto.
          rewrite -mem_undup; eauto using nondecreasing_sequence_cons.
            by apply IHn; eauto using nondecreasing_sequence_cons.
    Qed.
    
    (** We also show that the penultimate element of a sequence [undup xs] 
        is bounded by the penultimate element of sequence [xs]. *)
    Lemma undup_nth_le:
      forall xs,
        nondecreasing_sequence xs -> 
        undup xs [| (size (undup xs)).-2 |] <= xs [| (size xs).-2 |].
    Proof.
      Opaque undup.
      intros ?.
      have EX: exists len, size xs <= len.
      { exists (size xs); now simpl. } destruct EX as [n BO].
      revert xs BO; induction n.   
      - by intros xs; rewrite leqn0 size_eq0; move => /eqP EQ; subst xs.
      - intros [ |x1 [ | x2 xs]]; try done. 
        intros Size NonDec.          
        destruct (nondecreasing_sequence_2cons_leVeq _ _ _ NonDec) as [EQ|LT].
        * subst; rename x2 into x.        
          rewrite nodup_sort_2cons_eq //.
          eapply leq_trans. apply IHn. by done. eapply nondecreasing_sequence_cons; eauto.
          destruct xs as [ | x1 xs]; first by done. 
            by rewrite [in X in _ <= X]nth0_cons //. 
        * rewrite nodup_sort_2cons_lt //; simpl.
          case (posnP (size (undup (x2 :: xs))).-1) as [Z|POS].
          -- rewrite Z; simpl.
             apply leq_trans with ([:: x1, x2 & xs] [|0|]); first by done.
               by apply NonDec; apply/andP; split; simpl.
          -- rewrite nth0_cons //.
             eapply leq_trans; first apply IHn; eauto using nondecreasing_sequence_cons.
             destruct xs.
             ++ by exfalso. 
             ++ destruct xs; simpl in *; auto.
                Transparent undup.
    Qed.
    
  End Undup.


  (** * Properties of Distances *)
  (** In this section we prove a few lemmas about function [distances]. *)
  Section Distances.

    (** We begin with a simple lemma that helps us unfold [distances]
        of lists with two consecutive cons [x0::x1::xs]. *)
    Lemma distances_unfold_2cons:
      forall x0 x1 xs, 
        distances (x0::x1::xs) = (x1 - x0) :: distances (x1::xs).
    Proof. by intros; unfold distances; simpl; rewrite drop0. Qed.  

    (** Similarly, we prove a lemma stating that two consecutive
        appends to a sequence in [distances] function ([distances(xs
        ++ [:: a; b])]) can be rewritten as [distances(xs ++ [:: a])
        ++ [:: b - a]]. *)
    Lemma distances_unfold_2app_last:
      forall (a b : nat) (xs : seq nat),
        distances (xs ++ [:: a; b])
        = distances (xs ++ [:: a]) ++ [:: b - a].
    Proof.
      clear; intros.
      have EX: exists n, size xs <= n. exists (size xs); by done. destruct EX as [n LE].
      revert xs LE; induction n; intros.
      - by move: LE; rewrite leqn0 size_eq0; move => /eqP LE; subst.
      - destruct xs as [ | x0]; first by unfold distances.
        destruct xs as [ | x1]; first by unfold distances.
        have -> : distances ([:: x0, x1 & xs] ++ [:: a; b]) =  x1 - x0 :: distances ((x1 :: xs) ++ [:: a; b]).
        { by simpl; rewrite distances_unfold_2cons. }
        rewrite IHn; last by simpl in *; rewrite -(leq_add2r 1) !addn1.
        have -> : distances ([:: x0, x1 & xs] ++ [:: a]) = x1 - x0 :: distances ((x1 :: xs) ++ [:: a]).
        { by simpl; rewrite distances_unfold_2cons. }
          by done.
    Qed.

    (** We also prove a lemma stating that _one_ append to a sequence
        in the [distances] function ([distances(xs ++ [:: x])]) can
        be rewritten as [distances xs ++ [:: x - last0 xs]]. *)
    Lemma distances_unfold_1app_last:
      forall x xs,
        size xs >= 1 ->
        distances (xs ++ [:: x]) = distances xs ++ [:: x - last0 xs].
    Proof.
      clear. intros x xs POS.
      have EX: exists n, size xs <= n. exists (size xs); by done. destruct EX as [n LE].
      revert x xs LE POS; induction n; intros.
      - by move: LE; rewrite leqn0 size_eq0; move => /eqP LE; subst.
      - move: LE; rewrite leq_eqVlt; move => /orP [/eqP LEN' | LE]; last first.
        + by rewrite ltnS in LE; apply IHn.
        + destruct (seq_elim_last _ _ LEN') as [x__new [xs__l [EQ2 LEN]]].
          subst xs; clear LEN' POS; rename xs__l into xs.
          rewrite -catA.
          rewrite distances_unfold_2app_last.                
          destruct xs; first by done. 
          rewrite IHn.
          * by rewrite /last0 last_cat. 
          * by rewrite LEN.
          * by done.
    Qed.

    (** We prove that the difference between any two neighboring elements is
       bounded by the max element of the distances-sequence. *)
    Lemma distance_between_neighboring_elements_le_max_distance_in_seq:
      forall (xs : seq nat) (n : nat),
        xs[|n.+1|] - xs[|n|] <= max0 (distances xs).
    Proof.
      clear; intros xs id.
      apply leq_trans with (distances xs [| id |]).
      rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      have EX: exists n, size xs <= n. { by exists (size xs). } move: EX => [n LE].
      generalize dependent xs; generalize dependent id.
      induction n. 
      { intros.
        move: LE; rewrite leqn0 size_eq0; move => /eqP EQ; subst.
          by rewrite !nth_default.
      }
      { intros. 
        move: LE; rewrite leq_eqVlt; move => /orP [/eqP EQ|LT]; last first.
        { by apply IHn; rewrite ltnS in LT. }
        destruct xs; first by done.
        destruct xs; first by destruct id; [simpl |rewrite !nth_default]. 
        have Fact: distances [:: n0, n1 & xs] = (n1 - n0) :: distances [:: n1 & xs].
        { by rewrite /distances; simpl; rewrite drop0. } 
        rewrite Fact; clear Fact.
        destruct id; first by done.
        simpl.
        rewrite -IHn. simpl. by done.
          by move: EQ => /eqP; simpl; rewrite eqSS; move => /eqP EQ; rewrite -EQ.
      }
      { have Lem: forall x xs, x \in xs -> x <= max0 xs.
        { clear; intros.
          generalize dependent x.
          induction xs; first by done.
          intros ? IN; rewrite max0_cons leq_max; apply/orP.
          move: IN; rewrite in_cons; move => /orP [/eqP EQ| IN].
          - by left; subst.
          - by right; apply IHxs.
        }
        destruct (size (distances xs) <= id) eqn:SIZE.
        { by rewrite nth_default. }
        { apply Lem; rewrite mem_nth //.
          move: SIZE => /negP /negP.
            by rewrite ltnNge.
        } 
      }              
    Qed.

    (** Note that the distances-function has the expected behavior indeed. I.e. an element 
       on the position [n] of the distance-sequence is equal to the difference between
       elements on positions [n+1] and [n]. *)
    Lemma function_of_distances_is_correct:
      forall (xs : seq nat) (n : nat),
        (distances xs)[|n|] = xs[|n.+1|] - xs[|n|].
    Proof.
      intros xs.
      have EX: exists len, size xs <= len.
      { by exists (size xs). } move: EX => [len LE].
      generalize dependent xs.
      induction len; intros.
      { move: LE; rewrite leqn0 size_eq0; move => /eqP EQ; subst.
        unfold distances. simpl.
          by destruct n; simpl.
      } 
      move: LE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LE]; last by apply IHlen.
      destruct xs as [ | x1 xs]; first by done.
      destruct xs as [ | x2 xs].
      { by destruct n as [ | [ | ]]. }
      destruct n; first by done. 
      have F: distances [:: x1, x2 & xs] [|n.+1|] = distances [::x2 & xs] [| n |].
      { have EQ': distances [:: x1, x2 & xs] = (x2 - x1) :: distances [::x2 & xs].
        { by unfold distances; simpl; rewrite drop0. } 
          by rewrite EQ'.
      }
      have F2: [:: x1, x2 & xs] [|n.+2|] - [:: x1, x2 & xs] [|n.+1|] = [:: x2 & xs] [|n.+1|] - [:: x2 & xs] [|n|]; first by done.
      rewrite F F2. 
      apply IHlen.
      move: EQ => /eqP; simpl; rewrite eqSS; move => /eqP EQ.
        by rewrite -EQ. 
    Qed.

    (** We show that the size of a distances-sequence is one less 
       than the size of the original sequence. *)
    Lemma size_of_seq_of_distances:
      forall (xs : seq nat),
        2 <= size xs ->
        size xs = size (distances xs) + 1.
    Proof.
      clear.
      intros xs.
      have EX: exists len, size xs <= len.
      { exists (size xs). by done. } 
      move: EX => [len LE].
      generalize dependent xs.
      induction len.
      { intros.
        move: LE; rewrite leqn0 size_eq0; move => /eqP EQ; subst.
          by done.
      }
      intros ? ? SIZE.
      move: LE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LE]; last first.
      { by apply IHlen. }
      destruct xs as [ | x1 xs]; first by inversion EQ.
      destruct xs as [ | x2 xs]; first by inversion SIZE.
      destruct xs as [ | x3 xs]; first by done.
      clear SIZE.
      have F1: size [:: x1, x2, x3 & xs] = size [:: x2, x3 & xs] + 1.
      { by rewrite addn1. } 
      have F2: size (distances [:: x1, x2, x3 & xs]) = size (distances [:: x2, x3 & xs]) + 1.
      { by rewrite addn1. }
      rewrite F1 F2; clear F1 F2.
      apply/eqP; rewrite eqn_add2r; apply/eqP.
      apply IHlen; last by done.
      move: EQ => /eqP. simpl. rewrite eqSS; move => /eqP EQ.
        by rewrite -EQ.
    Qed.

    (** We prove that [index_iota 0 n] produces a sequence of numbers
        with which are always one unit apart each other. *)
    Lemma distances_of_iota_ε:
      forall n x, x \in distances (index_iota 0 n) -> x = ε.
    Proof.
      clear; intros n x IN.
      induction n.
      - by unfold index_iota, distances in IN.
      - destruct n; first by unfold distances, index_iota in IN. 
        rewrite -addn1 /index_iota subn0 iota_add in IN .
        rewrite add0n in IN. 
        rewrite distances_unfold_1app_last in IN; last by rewrite size_iota. 
        move: IN; rewrite mem_cat; move => /orP [IN|IN].
        + by apply IHn; rewrite /index_iota subn0; simpl.
        + by move: IN;
            rewrite -addn1 iota_add /last0 last_cat add0n addn1 // subSnn in_cons;
            move => /orP [/eqP EQ|F]; subst.
    Qed.
    
  End Distances.

  (** * Properties of Distances of Non-Decreasing Sequence *)
  (** In this section, we prove a few basic lemmas about distances of non-decreasing sequences. *)
  Section DistancesOfNonDecreasingSequence.
    
    (** First we show that the max distance between elements of any nontrivial sequence
       (i.e. a sequence that contains at leas two distinct elements) is positive. *)
    Lemma max_distance_in_nontrivial_seq_is_positive:
      forall (xs : seq nat),
        nondecreasing_sequence xs ->
        (exists x y, x \in xs /\ y \in xs /\ x <> y) -> 
        0 < max0 (distances xs).
    Proof.
      move => xs SIZE SMI. move: SMI => [x [y [INx [INy NEQ]]]].
      move: INx INy => /nthP INx /nthP INy. specialize (INx 0); specialize (INy 0).
      move: INx INy => [indx SIZEx EQx] [indy SIZEy EQy].
      have L: forall (x y indx indy : nat),
          indx < size xs -> indy < size xs ->
          nondecreasing_sequence xs ->
          x < y -> xs [|indx|] = x -> xs [|indy|] = y ->
          0 < max0 (distances xs).
      { clear; intros x y indx indy SIZEx SIZEy SIZE LT EQx EQy.
        have LTind: indx < indy. 
        { rewrite ltnNge; apply/negP; intros CONTR.
          subst x y; move: LT; rewrite ltnNge; move => /negP T; apply: T.
            by apply SIZE; apply/andP. } 
        have EQ: exists Δ, indy = indx + Δ. exists (indy - indx); ssromega. move: EQ => [Δ EQ]; subst indy.
        have F: exists ind, indx <= ind < indx + Δ /\ xs[|ind|] < xs[|ind.+1|].
        { subst x y; clear SIZEx SIZEy; revert xs indx LTind SIZE LT.
          induction Δ; intros; first by ssromega.
          destruct (posnP Δ) as [ZERO|POS].
          { by subst Δ; exists indx; split; [rewrite addn1; apply/andP | rewrite addn1 in LT]; auto. }
          have ALT: xs[|indx + Δ|] == xs[|indx + Δ.+1|] \/ xs[|indx + Δ|] < xs[|indx + Δ.+1|].
          { apply/orP; rewrite -leq_eqVlt addnS.
            apply SIZE; apply/andP; split; first by done.
            rewrite ltnNge; apply/negP; intros CONTR.
            move: LT; rewrite ltnNge; move => /negP LT; apply: LT.
              by rewrite nth_default ?addnS. }                    
          move: ALT => [/eqP EQ|LT'].
          - edestruct (IHΔ) as [ind [B UP]]; eauto 5 using addn1, leq_add2l.
            exists ind; split; last by done.
            move: B => /andP [B1 B2]; apply/andP; split; first by done.
              by rewrite addnS ltnS ltnW. 
          - exists (indx + Δ); split; last by rewrite -addnS.
              by apply/andP; split; [rewrite leq_addr | rewrite addnS].  }
        move: F => [ind [/andP [B1 B2] UP]].
        apply leq_trans with (xs [|ind.+1|] - xs [|ind|]).
        - by rewrite subn_gt0.
        - by apply distance_between_neighboring_elements_le_max_distance_in_seq.
      }
      move: NEQ => /eqP; rewrite neq_ltn; move => /orP [LT|LT].
      - eapply L with (indx := indx) (x := x) (y := y); eauto.
      - eapply L with (indx := indy) (indy := indx) (x := y) (y := x); eauto. 
    Qed.  

    (** Given a non-decreasing sequence [xs] with length n, we show that the difference 
       between the last element of [xs] and the last element of the distances-sequence 
       of [xs] is equal to [xs[n-2]]. *)
    Lemma last_seq_minus_last_distance_seq:
      forall (xs : seq nat),
        nondecreasing_sequence xs ->
        last0 xs - last0 (distances xs) = xs [| (size xs).-2 |].
    Proof.
      clear.
      intros xs SIS.
      destruct xs as [ | x1 xs]. by done.
      destruct xs as [ | x2 xs]. by rewrite subn0.
      rewrite {2}/last0 -[in X in _ - X]nth_last function_of_distances_is_correct prednK;
        last by done.
      set [:: x1, x2 & xs] as X.
      rewrite /last0 -nth_last.
      rewrite size_of_seq_of_distances; last by done.
      rewrite !addn1.
      rewrite -pred_Sn.
      rewrite subKn; first by done.
      unfold X.
      unfold nondecreasing_sequence in *.
      apply SIS.
      apply/andP; split.
      simpl; by done.
      rewrite [in X in _ < X]size_of_seq_of_distances; last by done.
        by rewrite addn1.
    Qed.

    (** The max element of the distances-sequence of a sequence [xs] is bounded 
       by the last element of [xs]. Note that all elements of [xs] are positive.
       Thus they all lie within the interval [0, last xs]. *)
    Lemma max_distance_in_seq_le_last_element_of_seq:
      forall (xs : seq nat),
        nondecreasing_sequence xs ->
        max0 (distances xs) <= last0 xs. 
    Proof. 
      intros.
      have SIZE: size xs < 2 \/ 2 <= size xs.
      { by destruct (size xs) as [ | n]; last destruct n; auto. } 
      move: SIZE => [LT | SIZE2].
      { by destruct xs; last destruct xs. } 
      apply leq_trans with (last0 xs - first0 xs); last by apply leq_subr.
      have F: forall xs c, (forall x, x \in xs -> x <= c) -> max0 xs <= c.
      { clear; intros.
        induction xs; first by done.
        rewrite max0_cons geq_max; apply/andP; split.
        + by apply H; rewrite in_cons; apply/orP; left.
        + by apply IHxs; intros; apply H; rewrite in_cons; apply/orP; right.
      }
      apply F; clear F; intros d IN. 
      move: IN => /nthP T; specialize (T 0); move: T => [idx IN DIST].
      rewrite function_of_distances_is_correct in DIST.
      rewrite -DIST.
      rewrite leq_sub //.
      { destruct (xs [|idx.+1|] == last0 xs) eqn:EQ.
        - by rewrite leq_eqVlt; apply/orP; left.
        - rewrite /last0 -nth_last. apply H. 
          rewrite -(ltn_add2r 1) addn1 -size_of_seq_of_distances in IN; last by done.
          move: IN; rewrite leq_eqVlt; move => /orP [/eqP KK|KK].
          move: EQ; rewrite /last0 -nth_last -{1}KK -[_.+2.-1]pred_Sn; move => /eqP; by done.
          apply/andP; split; first rewrite -(ltn_add2r 1) !addn1 prednK //.
          + by apply ltn_trans with idx.+2.
          + by apply ltnW.
          + by rewrite prednK //; apply ltn_trans with idx.+2.
      }
      { destruct (first0 xs == xs [|idx|]) eqn:EQ.
        - by rewrite leq_eqVlt; apply/orP; left.
        - rewrite /first0 -nth0. apply H.
          rewrite -(ltn_add2r 1) addn1 -size_of_seq_of_distances in IN; last by done.
          destruct idx; first by move: EQ; rewrite /first0 -nth0; move => /eqP.
          apply/andP; split; first by done.
            by apply ltn_trans with idx.+2.
      }
    Qed.

    (** Let [xs] be a non-decreasing sequence. We prove that 
        distances of sequence [[seq ρ <- index_iota 0 k.+1 | ρ \in xs]] 
        coincide with sequence [[seq x <- distances xs | 0 < x]]]. *)
    Lemma distances_iota_filtered:
      forall xs k,
        (forall x, x \in xs -> x <= k) -> 
        nondecreasing_sequence xs -> 
        distances [seq ρ <- index_iota 0 k.+1 | ρ \in xs] = [seq x <- distances xs | 0 < x]. 
    Proof.
      intros xs.
      have EX: exists len, size xs <= len.
      { exists (size xs); now simpl. } destruct EX as [n BO].
      revert xs BO; induction n.
      { intros ? Len k Bound NonDec.
        move: Len; rewrite leqn0 size_eq0; move => /eqP T; subst.
          by rewrite filter_pred0.
      }
      { intros ? Len k Bound NonDec.
        destruct xs as [ |x1 [ |x2 xs]].
        - by rewrite filter_pred0.
        - by rewrite index_iota_filter_singl; last (rewrite ltnS; apply Bound; rewrite in_cons; apply/orP; left).
        - have LEx1: x1 <= k. by apply Bound; rewrite in_cons eq_refl.
          have LEx2: x2 <= k. by apply Bound; rewrite !in_cons eq_refl orbT.
          have M1: forall y : nat, y \in x2 :: xs -> x1 <= y. by apply nondecreasing_sequence_cons_min.
          have M2: forall x : nat, x \in x2 :: xs -> x <= k. by intros; apply Bound; rewrite in_cons; apply/orP; right.
          have M3: forall y : nat, y \in xs -> x2 <= y
              by apply nondecreasing_sequence_cons in NonDec; apply nondecreasing_sequence_cons_min.
          destruct (nondecreasing_sequence_2cons_leVeq _ _ _ NonDec).
          + subst; rewrite distances_unfold_2cons.
            replace ((@filter nat (fun x : nat => leq (S O) x) (@cons nat (subn x2 x2) (distances (@cons nat x2 xs)))))
              with ([seq x <- distances (x2 :: xs) | 0 < x]); last by rewrite subnn. 
            rewrite range_filter_2cons.
              by apply IHn; eauto 2 using nondecreasing_sequence_cons.
          + have M4: forall y : nat, y \in x2 :: xs -> x1 < y. by apply nondecreasing_sequence_cons_smin.
            rewrite distances_unfold_2cons.
            rewrite range_iota_filter_step // rem_lt_id //. 
            replace ((@filter nat (fun x : nat => leq (S O) x) (@cons nat (subn x2 x1) (distances (@cons nat x2 xs)))))
              with (x2 - x1 :: [seq x <- distances (x2 :: xs) | 0 < x]); last first.
            { simpl; replace (0 < x2 - x1) with true; first by done.
                by apply/eqP; rewrite eq_sym; rewrite eqb_id subn_gt0. }
            rewrite -(IHn _ _ k) //; last eapply nondecreasing_sequence_cons; eauto 2.
            rewrite {1}range_iota_filter_step //. rewrite distances_unfold_2cons. rewrite {1}range_iota_filter_step //. 
      }
    Qed.

    (** Let [xs] again be a non-decreasing sequence. We prove that 
        distances of sequence [undup xs] coincide with 
        sequence of positive distances of [xs]. *)
    Lemma distances_positive_undup:
      forall xs,
        nondecreasing_sequence xs -> 
        [seq d <- distances xs | 0 < d] = distances (undup xs).
    Proof.
      intros ? NonDec.
      rewrite -(distances_iota_filtered _ (max0 xs)); [ | by apply in_max0_le | by done].
      have T: forall {X Y : Type} (x y : X) (f : X -> Y), x = y -> f x = f y.
      { by intros; subst. } apply T; clear T.
      have EX: exists len, size xs <= len.
      { exists (size xs); now simpl. } destruct EX as [n BO].
      revert xs NonDec BO; induction n.
      - intros xs _; rewrite leqn0 size_eq0; move => /eqP EQ; subst xs.
          by rewrite filter_pred0.
      - intros [ |x1 [ | x2 xs]].
        + by rewrite filter_pred0.
        + by rewrite index_iota_filter_singl ?L02 //; apply/andP; split; [ done | destruct x1].  
        + intros NonDec Size.        
          destruct (nondecreasing_sequence_2cons_leVeq _ _ _ NonDec) as [EQ|LT].
          * subst; rename x2 into x.
            rewrite nodup_sort_2cons_eq range_filter_2cons max0_2cons_eq.
              by apply IHn; [ eapply nondecreasing_sequence_cons; eauto | by done]. 
          * rewrite nodup_sort_2cons_lt // max0_2cons_le; last by rewrite ltnW.
            rewrite index_iota_filter_step; [ | | by apply nondecreasing_sequence_cons_min]; last first.
            { apply/andP; split; first by done.
              eapply leq_trans; first by eassumption.
              rewrite ltnW // ltnS; apply in_max0_le.
                by rewrite in_cons eq_refl.
            }
            rewrite rem_lt_id //; last by apply nondecreasing_sequence_cons_smin.
            rewrite IHn //; eauto using nondecreasing_sequence_cons.
    Qed.

  
    (** Consider two non-decreasing sequences [xs] and [ys] and assume that 
       (1) first element of [xs] is at most the first element of [ys] and 
       (2) distances-sequences of [xs] is dominated by distances-sequence of 
       [ys]. Then [xs] is dominated by [ys].  *)
    Lemma domination_of_distances_implies_domination_of_seq:
      forall (xs ys : seq nat),
        first0 xs <= first0 ys ->
        2 <= size xs ->
        2 <= size ys ->
        size xs = size ys -> 
        nondecreasing_sequence xs ->
        nondecreasing_sequence ys ->
        (forall n, (distances xs)[|n|] <= (distances ys)[|n|]) ->
        (forall n, xs[|n|] <= ys[|n|]).
    Proof.
      intros xs ys.
      have EX: exists len, size xs <= len /\ size ys <= len.
      { exists (maxn (size xs) (size ys)).
          by split; rewrite leq_max; apply/orP; [left | right].
      } move: EX => [len [LE1 LE2]]. 
      generalize dependent xs; generalize dependent ys. 
      induction len.
      { intros; move: LE1 LE2; rewrite !leqn0 !size_eq0; move => /eqP E1 /eqP E2.
          by subst.
      }
      { intros ? LycSIZE ? LxSIZE FLE Sxs Sys SIZEEQ STRxs STRys LE n.
        destruct xs as [ | x1 xs], ys as [ | y1 ys]; try by done.
        destruct xs as [ | x2 xs], ys as [ | y2 ys]; try by done.
        have F: x2 <= y2.
        { specialize (STRxs 0 1); feed STRxs; first by done.
          specialize (STRys 0 1); feed STRys; first by done.
          specialize (LE 0); simpl in LE, FLE.
          rewrite leqNgt; apply/negP; intros NEQ.
          move: LE; rewrite leqNgt; move => /negP LE; apply: LE.
          rewrite -(ltn_add2r x1) subnK // subh1 // -(ltn_add2r y1) subnK.
          - by eapply leq_ltn_trans; [erewrite leq_add2l | erewrite ltn_add2r].
          - by apply leq_trans with y2; auto using leq_addr.
        }
        destruct xs as [ | x3 xs], ys as [ | y3 ys]; try by done. 
        { by destruct n; [ | destruct n]. }
        destruct n; first by done. 
        simpl; apply IHlen; try done. 
        - by apply/eqP; rewrite -(eqn_add2r 1) !addn1; apply/eqP.
        - move => m1 m2 /andP [B1 B2].
          apply (STRxs m1.+1 m2.+1); apply/andP; split.
          + by rewrite ltnS.
          + by rewrite -(ltn_add2r 1) !addn1 in B2. 
        - move => m1 m2 /andP [B1 B2].
          apply (STRys m1.+1 m2.+1); apply/andP; split.
          + by rewrite ltnS.
          + by rewrite -(ltn_add2r 1) !addn1 in B2. 
        - intros. specialize (LE n0.+1). simpl in LE. by done.
      }
    Qed.

  End DistancesOfNonDecreasingSequence.

End NondecreasingSequence.