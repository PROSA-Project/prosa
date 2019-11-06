Require Import rt.classic.util.all.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Non-decreasing sequence *)
(** In this module we introduce the notion of a non-decreasing sequence
     that will be used to describe preemption points in models with limited preemptions. *)
Module NondecreasingSequence.

  (* First, let's introduce the notion of the nth element of a sequence. *)
  Notation "xs [| n |]" := (nth 0 xs n) (at level 30).
  
  (* In this section we provide the notion of a non-decreasing sequence. *)
  Section Definitions. 
    
    (* We say that a sequence xs is non-decincreasing iff for any two indices n1 and n2 
       such that [n1 <= n2 < size xs] the following condition holds: xs[n1] <= xs[n2]. *)
    Definition nondecreasing_sequence (xs: seq nat) :=
      forall n1 n2,
        n1 <= n2 < size xs ->
        nth 0 xs n1 <= nth 0 xs n2.

    (* For a non-decreasing sequence we define the notion of 
       distances between neighboring elements of the sequence. *)
    (* Example:
       Consider the following sequence of natural numbers: xs = [:: 1; 10; 10; 17; 20; 41]. 
       Then [drop 1 xs] is equal to [:: 10; 10; 17; 20; 41].
       Then [zip xs (drop 1 xs)] is equal to [:: (1,10); (10,10); (10,17); (17,20); (20,41)]
       And after the mapping [map (fun '(x1, x2) => x2 - x1)] we end up with [:: 9; 0; 7; 3; 21]. *)
    Definition distances (xs: seq nat) :=
      map (fun '(x1, x2) => x2 - x1) (zip xs (drop 1 xs)).

    (* Next, we define some common operations on lists. 
       Namely max, first, and last. *)
    Definition max := foldl maxn 0.
    Definition first := head 0.
    Definition last := last 0.

  End Definitions.
  
  (* In this section, we prove a few basic lemmas about nondecreasing sequences. *)
  Section Lemmas.
 
    (* Next, we prove that no element can lie strictly between two 
       neighboring elements and still belong to the list. *)
    Lemma antidensity_of_nondecreasing_seq:
      forall (xs: seq nat) (x: nat) (n: nat),
        nondecreasing_sequence xs ->
        xs [| n |] < x < xs [| n.+1 |] ->
        ~~ (x \in xs).
    Proof.
      clear.
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

    (* Alternatively, consider an arbitrary natural number x that is 
       bounded by the first and the last element of a sequence xs. Then 
       there is an index n such that xs[n] <= x < x[n+1]. *)
    Lemma belonging_to_segment_of_seq_is_total:
      forall (xs: seq nat) (x: nat), 
        2 <= size xs -> 
        first xs <= x < last xs ->
        exists n,
          n.+1 < size xs /\
          xs[|n|] <= x < xs[|n.+1|].
    Proof.
      clear; intros ? ? SIZE LAST.
      have EX: exists n, size xs <= n.
      { by exists (size xs). } move: EX => [n LE].
      destruct n.
      { intros; destruct xs; by done. }
      destruct n.
      { intros.
        destruct xs; first by done.
          by destruct xs. 
      }
      generalize dependent xs.
      induction n. 
      { intros.
        destruct xs; first by done.
        destruct xs; first by done.
        destruct xs; last by done.
        clear LE SIZE.
          by exists 0; unfold last in *; simpl in *.
      }
      { intros.
        destruct xs; first by done.
        destruct xs; first by done.
        destruct xs.
        { by exists 0; unfold last in *; simpl in *. }
        destruct (x >= n1) eqn: NEQ.
        { specialize (IHn [:: n1, n2 & xs]).
          feed_n 3 IHn.
          { by done. } 
          { move: LAST => /andP [LAST1 LAST2].
            apply/andP; split; first by done.
            apply leq_trans with (last [:: n0, n1, n2 & xs]); first by done.
              by rewrite /last !last_cons.
          }
          { by rewrite -(ltn_add2r 1) !addn1. }
          move: IHn => [idx [SI /andP [G L]]].
          exists idx.+1; split.
          - by simpl in *; rewrite -addn1 -[in X in _ <= X]addn1 leq_add2r.
          - by apply/andP; split.
        }
        { clear IHn SIZE LE; simpl in *.
          exists 0; split; first by done.
          move: NEQ => /negP /negP; rewrite -ltnNge; move => NEQ.
          move: LAST => /andP [LAST _].
            by apply/andP; split.
        }
      }
    Qed.

    (* We prove that the difference between any two neighboring elements is
       bounded by the max element of the distances-sequence. *)
    Lemma distance_between_neighboring_elements_le_max_distance_in_seq:
      forall (xs: seq nat) (n: nat),
        xs[|n.+1|] - xs[|n|] <= max (distances xs).
    Proof.
      clear; intros xs id.
      apply leq_trans with (distances xs [| id |]).
      rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      have EX: exists n, size xs <= n.
      { by exists (size xs). } move: EX => [n LE].
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
      { 
        have Lem: forall x xs, x \in xs -> x <= max xs.
        { clear; intros.
          generalize dependent x.
          induction xs.
          { by done. }
          { intros ? IN; rewrite /max seq_max_cons leq_max; apply/orP.
            move: IN; rewrite in_cons; move => /orP [/eqP EQ| IN].
            - by left; subst.
            - by right; apply IHxs.
          }
        }
        destruct (size (distances xs) <= id) eqn:SIZE.
        { by rewrite nth_default. }
        { apply Lem; rewrite mem_nth //.
          move: SIZE => /negP /negP.
            by rewrite ltnNge.
        } 
      }              
    Qed.

    (* As a corollary, the max distance between elements of any nontrivial sequence
       (i.e. a sequence that contains at leas two distinct elements) is positive. *)
    Corollary max_distance_in_nontrivial_seq_is_positive:
      forall (xs: seq nat),
        nondecreasing_sequence xs ->
        (exists x y, x \in xs /\ y \in xs /\ x <> y) -> 
        0 < max (distances xs).
    Proof.
      clear. 
      intros xs SIZE SMI. 
      move: SMI => [x [y [INx [INy NEQ]]]].
      move: INx INy => /nthP INx /nthP INy.
      specialize (INx 0); specialize (INy 0).
      move: INx INy => [indx SIZEx EQx] [indy SIZEy EQy]. 
      move: NEQ => /eqP; rewrite neq_ltn; move => /orP [LT|LT].
      { have LTind: indx < indy. 
        { rewrite ltnNge; apply/negP; intros CONTR.
          specialize (SIZE indy indx).
          feed SIZE; first by apply/andP; split.
          subst x y.
            by move: SIZE; rewrite leqNgt; move => /negP T; apply: T.
        } 
        have EQ: exists Δ, indy = indx + Δ.
        { exists (indy - indx). by rewrite subnKC; last apply ltnW. }
        move: EQ => [Δ EQ]; subst indy.
        have F: exists ind, indx <= ind < indx + Δ /\ xs[|ind|] < xs[|ind.+1|].
        { subst x y.
          clear SIZEx SIZEy.
          generalize dependent xs.
          generalize dependent indx.
          induction Δ.
          { intros.
            exfalso.
              by move: LT; rewrite addn0 ltnn.
          }
          intros.
          have ALT: Δ = 0 \/ Δ > 0.
          { by destruct Δ; auto. }
          move: ALT => [ZERO | POS].
          { subst Δ.
            exists indx; split; last by rewrite addn1 in LT.
              by rewrite addn1; apply/andP; split.
          }
          have ALT: xs[|indx + Δ|] == xs[|indx + Δ.+1|] \/ xs[|indx + Δ|] < xs[|indx + Δ.+1|].
          { rewrite addnS.
            have NEQ: xs [|indx + Δ|] <= xs [|(indx + Δ).+1|].
            apply SIZE; apply/andP; split; first by done.
            rewrite ltnNge; apply/negP; intros CONTR.
            move: LT; rewrite ltnNge; move => /negP LT; apply: LT.
            have EQ: xs [|indx + Δ.+1|] = 0.
            { by rewrite nth_default ?addnS. }
              by rewrite EQ; clear EQ.
              by apply/orP; rewrite -leq_eqVlt.
          }                    
          move: ALT => [/eqP EQ|LT'].
          { specialize (IHΔ indx).
            feed IHΔ; first by rewrite -addn1 leq_add2l.
            rewrite -EQ in LT.
            specialize (IHΔ xs SIZE LT).
            move: IHΔ => [ind [/andP [B1 B2] UP]].
            exists ind; split; last by done.
            apply/andP; split; first by done.
              by rewrite addnS ltnS ltnW. 
          }
          { exists (indx + Δ); split.
            - apply/andP; split; first by rewrite leq_addr.
                by rewrite addnS.
            - by rewrite -addnS.
          }
        }
        move: F => [ind [/andP [B1 B2] UP]].
        apply leq_trans with (xs [|ind.+1|] - xs [|ind|]).
        - by rewrite subn_gt0.
        - by apply distance_between_neighboring_elements_le_max_distance_in_seq.
      }
      { have LTind: indy < indx. 
        { rewrite ltnNge; apply/negP; intros CONTR.
          specialize (SIZE indx indy).
          feed SIZE; first by apply/andP; split.
          subst x y.
            by move: SIZE; rewrite leqNgt; move => /negP T; apply: T.
        } 
        have EQ: exists Δ, indx = indy + Δ.
        { exists (indx - indy). by rewrite subnKC; last apply ltnW. }
        move: EQ => [Δ EQ]; subst indx.
        have F: exists ind, indy <= ind < indy + Δ /\ xs[|ind|] < xs[|ind.+1|].
        { subst x y.
          clear SIZEx SIZEy.
          generalize dependent xs.
          generalize dependent indy.
          induction Δ.
          { intros.
            exfalso.
              by move: LT; rewrite addn0 ltnn.
          }
          intros.
          have ALT: Δ = 0 \/ Δ > 0.
          { by destruct Δ; auto. }
          move: ALT => [ZERO | POS].
          { subst Δ.
            exists indy; split; last by rewrite addn1 in LT.
              by rewrite addn1; apply/andP; split.
          }
          have ALT: xs[|indy + Δ|] == xs[|indy + Δ.+1|] \/ xs[|indy + Δ|] < xs[|indy + Δ.+1|].
          { rewrite addnS.
            have NEQ: xs [|indy + Δ|] <= xs [|(indy + Δ).+1|].
            apply SIZE; apply/andP; split; first by done.
            rewrite ltnNge; apply/negP; intros CONTR.
            move: LT; rewrite ltnNge; move => /negP LT; apply: LT.
            have EQ: xs [|indy + Δ.+1|] = 0.
            { by rewrite nth_default ?addnS. }
              by rewrite EQ; clear EQ.
              by apply/orP; rewrite -leq_eqVlt.
          }
          move: ALT => [/eqP EQ|LT'].
          { specialize (IHΔ indy).
            feed IHΔ; first by rewrite -addn1 leq_add2l.
            rewrite -EQ in LT.
            specialize (IHΔ xs SIZE LT).
            move: IHΔ => [ind [/andP [B1 B2] UP]].
            exists ind; split; last by done.
            apply/andP; split; first by done.
              by rewrite addnS ltnS ltnW. 
          }
          { exists (indy + Δ); split.
            - apply/andP; split; first by rewrite leq_addr.
                by rewrite addnS.
            - by rewrite -addnS.
          }
        }
        move: F => [ind [/andP [B1 B2] UP]].
        apply leq_trans with (xs [|ind.+1|] - xs [|ind|]).
        - by rewrite subn_gt0.
        - by apply distance_between_neighboring_elements_le_max_distance_in_seq.
      }
    Qed.
    
    (* Note that the distances-function has the expected behavior indeed. I.e. an element 
       on the n-th position of the distance-sequence is equal to the difference between
       n+1-th and n-th elements. *)
    Lemma function_of_distances_is_correct:
      forall (xs: seq nat) (n: nat),
        (distances xs)[|n|] = xs[|n.+1|] - xs[|n|].
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
        unfold distances. simpl.
          by destruct n; simpl.
      } 
      intros.
      move: LE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LE]; last first.
      { by apply IHlen. }
      destruct xs as [ | x1 xs]. inversion EQ.
      destruct xs as [ | x2 xs].
      { clear EQ.
        destruct n. by simpl.
        destruct n; by simpl.
      }
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

    (* We show that the size of a distances-sequence is one less 
       than the size of the original sequence. *)
    Lemma size_of_seq_of_distances:
      forall (xs: seq nat),
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
      apply IHlen.
      { move: EQ => /eqP. simpl. rewrite eqSS; move => /eqP EQ.
          by rewrite -EQ.
      }
        by done.
    Qed. 

    (* Note that the last element of a nondecreasing sequence is the max element. *)
    Lemma last_is_max_in_nondecreasing_seq:
      forall (xs: seq nat) (x: nat),
        nondecreasing_sequence xs ->
        (x \in xs) -> 
        x <= last xs.
    Proof.
      clear; intros ? ? STR IN. 
      have NEQ: forall x y, x = y \/ x != y.
      { clear. intros.
        destruct (x == y) eqn:EQ.
        - by left; apply/eqP.
        - by right.
      }
      move: (NEQ _ x (last xs)); clear NEQ; move => [EQ|NEQ].
      { by subst x. }
      move: IN => /nthP EX.
      specialize (EX 0). 
      move: EX => [id SIZE EQ].
      rewrite /last -nth_last -EQ; subst x.      
      rewrite -addn1 in SIZE.
      apply STR; apply/andP.
      have POS: 0 < size xs.
      { by apply leq_trans with (id + 1); [rewrite addn1| done]. }
      split.
      - by rewrite -(leq_add2r 1) !addn1 prednK // -addn1.
      - by rewrite prednK.
    Qed.     

    (* Given a nondecreasing sequence xs with length n, we show that the difference 
       between the last element of xs and the last element of the distances-sequence 
       of xs is equal to the (n-2)'th element of xs. *)
    Lemma last_seq_minus_last_distance_seq:
      forall (xs: seq nat),
        nondecreasing_sequence xs ->
        last xs - last (distances xs) = xs [| (size xs).-2 |].
    Proof.
      clear.
      intros xs SIS.
      destruct xs as [ | x1 xs]. unfold last, seq.last. simpl. by done.
      destruct xs as [ | x2 xs]. unfold last, seq.last. simpl. by rewrite subn0.
      rewrite {2}/last -[in X in _ - X]nth_last function_of_distances_is_correct prednK; last by done.
      set [:: x1, x2 & xs] as X.
      rewrite /last -nth_last.
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

    (* Note that the last element is at most the max element. *)
    Lemma last_of_seq_le_max_of_seq:
      forall (xs: seq nat),
        last xs <= max xs.
    Proof.
      clear.
      intros xs.
      have EX: exists len, size xs <= len.
      { exists (size xs). by done. } 
      move: EX => [len LE].
      generalize dependent xs.
      induction len.
      { by intros; move: LE; rewrite leqn0 size_eq0; move => /eqP EQ; subst. }
      intros ? SIZE.
      move: SIZE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LE]; last first.
      { by apply IHlen. }
      destruct xs as [ | x1 xs]; first by inversion EQ.
      destruct xs as [ | x2 xs]. by rewrite /last /max leq_max; apply/orP; right.
      have F1: last [:: x1, x2 & xs] = last [:: x2 & xs].
      { by unfold last; simpl. }
      rewrite F1 /max seq_max_cons; clear F1.
      rewrite leq_max; apply/orP; right.
      apply IHlen.
      move: EQ => /eqP; simpl; rewrite eqSS; move => /eqP EQ.
        by subst.
    Qed.

    (* If any n'th element of a sequence xs is less-than-or-equal-to n'th 
       element of ys, then max of xs is less-than-or-equal-to max of ys. *)
    Lemma max_of_dominating_seq:
      forall (xs ys: seq nat),
        (forall n, xs[|n|] <= ys[|n|]) ->
        max xs <= max ys.
    Proof.
      clear.
      intros xs ys.
      have EX: exists len, size xs <= len /\ size ys <= len.
      { exists (maxn (size xs) (size ys)).
          by split; rewrite leq_max; apply/orP; [left | right].
      }
      move: EX => [len [LE1 LE2]].
      generalize dependent xs.
      generalize dependent ys.
      induction len.
      { intros. 
        move: LE1 LE2; rewrite !leqn0 !size_eq0; move => /eqP E1 /eqP E2.
        subst. by done.
      }
      {
        intros. 
        destruct xs, ys; try done.
        { have L: forall xs, (forall n, xs [| n |] = 0) -> max xs = 0.
          { clear. intros.
            induction xs; first by done.
            rewrite /max seq_max_cons.
            apply/eqP; rewrite eqn_leq; apply/andP; split; last by done.
            rewrite geq_max; apply/andP; split.
            - by specialize (H 0); simpl in H; rewrite H.
            - rewrite leqn0; apply/eqP; apply: IHxs.
              intros.
              specialize (H n.+1).
                by simpl in *.
          }
          rewrite L; first by done. 
          intros.
          specialize (H n0).
            by destruct n0; simpl in *; apply/eqP; rewrite -leqn0.
        }
        {  rewrite /max !seq_max_cons.
           rewrite geq_max; apply/andP; split.
           + rewrite leq_max; apply/orP; left.
               by specialize (H 0); simpl in H.
           + rewrite leq_max; apply/orP; right.
             apply IHlen.
             rewrite ltnS in LE2; by done.
             rewrite ltnS in LE1; by done.
             intros.
             specialize (H n1.+1). 
               by simpl in H.
        }
      }
    Qed.

    (* The max element of the distances-sequence of a sequence xs is bounded 
       by the last element of xs. Note that all elements of xs are positive.
       Thus they all lie within the interval [0, last xs]. *)
    Lemma max_distance_in_seq_le_last_element_of_seq:
      forall (xs: seq nat),
        nondecreasing_sequence xs ->
        max (distances xs) <= last xs. 
    Proof. 
      clear.
      intros.
      have SIZE: size xs < 2 \/ 2 <= size xs.
      { destruct (size xs); auto.
        destruct (n); auto.
      }
      move: SIZE => [LT | SIZE2].
      { destruct xs.
        rewrite /distances /last /max; simpl; by done.
        destruct xs; last by done.
          by unfold max, distances, last; simpl.
      }
      apply leq_trans with (last xs - first xs); last by apply leq_subr.
      have F: forall xs c, (forall x, x \in xs -> x <= c) -> max xs <= c.
      { clear; intros.
        induction xs.
        - by done.
        - rewrite /max seq_max_cons geq_max; apply/andP; split.
          + by apply H; rewrite in_cons; apply/orP; left.
          + by apply IHxs; intros; apply H; rewrite in_cons; apply/orP; right.
      }
      apply F; clear F.
      intros.
      move: H0 => /nthP T; specialize (T 0).
      move: T => [ind IN DIST].
      rewrite function_of_distances_is_correct in DIST.
      rewrite -DIST.
      rewrite leq_sub //.
      { destruct (xs [|ind.+1|] == last xs) eqn:EQ.
        - by rewrite leq_eqVlt; apply/orP; left.
        - rewrite /last -nth_last. apply H. 
          rewrite -(ltn_add2r 1) addn1 -size_of_seq_of_distances in IN; last by done.
          move: IN; rewrite leq_eqVlt; move => /orP [/eqP KK|KK].
          move: EQ; rewrite /last -nth_last -{1}KK -[_.+2.-1]pred_Sn; move => /eqP; by done.
          apply/andP; split; first rewrite -(ltn_add2r 1) !addn1 prednK //.
          + by apply ltn_trans with ind.+2.
          + by apply ltnW.
          + by rewrite prednK //; apply ltn_trans with ind.+2.
      }
      { destruct (first xs == xs [|ind|]) eqn:EQ.
        - by rewrite leq_eqVlt; apply/orP; left.
        - rewrite /first -nth0. apply H.
          rewrite -(ltn_add2r 1) addn1 -size_of_seq_of_distances in IN; last by done.
          destruct ind; first by move: EQ; rewrite /first -nth0; move => /eqP.
          apply/andP; split; first by done.
            by apply ltn_trans with ind.+2.
      }
    Qed.

    (* Consider two nondecreasing sequences xs and ys and assume that 
       (1) first element of xs is at most the first element of ys and 
       (2) distances-sequences of xs is dominated by distances-sequence of 
       ys. Then xs is dominated by ys.  *)
    Lemma domination_of_distances_implies_domination_of_seq:
      forall (xs ys: seq nat),
        first xs <= first ys ->
        2 <= size xs ->
        2 <= size ys ->
        size xs = size ys -> 
        nondecreasing_sequence xs ->
        nondecreasing_sequence ys ->
        (forall n, (distances xs)[|n|] <= (distances ys)[|n|]) ->
        (forall n, xs[|n|] <= ys[|n|]).
    Proof.
      clear. 
      intros xs ys.
      have EX: exists len, size xs <= len /\ size ys <= len.
      { exists (maxn (size xs) (size ys)).
          by split; rewrite leq_max; apply/orP; [left | right].
      }
      move: EX => [len [LE1 LE2]]. 
      generalize dependent xs.
      generalize dependent ys. 
      induction len.
      { intros. 
        move: LE1 LE2; rewrite !leqn0 !size_eq0; move => /eqP E1 /eqP E2.
          by subst.
      }
      { intros ? LycSIZE ? LxSIZE FLE Sxs Sys SIZEEQ STRxs STRys LE n.
        destruct xs as [ | x1 xs], ys as [ | y1 ys]; try by done.
        destruct xs as [ | x2 xs], ys as [ | y2 ys]; try by done.
        clear Sxs Sys.
        have F: x2 <= y2.
        { specialize (STRxs 0 1); simpl in STRxs; feed STRxs; first by done.
          specialize (STRys 0 1); simpl in STRys; feed STRys; first by done.
          specialize (LE 0); simpl in LE, FLE.
          rewrite leqNgt; apply/negP; intros NEQ.
          move: LE; rewrite leqNgt; move => /negP LE; apply: LE.
          rewrite -(ltn_add2r x1).
          rewrite subnK //.
          rewrite subh1 //.
          rewrite -(ltn_add2r y1).
          rewrite subnK; last first.
          apply leq_trans with y2; [by done | by rewrite leq_addr].
          apply leq_ltn_trans with (y2 + y1).
          - by rewrite leq_add2l.
          - by rewrite ltn_add2r.
        }
        destruct xs as [ | x3 xs], ys as [ | y3 ys]; try by done. 
        { destruct n; simpl; first by done.
          destruct n; simpl; by done.
        }
        destruct n; first by simpl in *. 
        simpl; apply IHlen; try done.
        - by simpl in *; apply/eqP; rewrite -(eqn_add2r 1) !addn1; apply/eqP.
        - move => m1 m2 /andP [B1 B2].
          specialize (STRxs m1.+1 m2.+1).
          feed STRxs.
          apply/andP; split.
          + by rewrite ltnS.
          + by simpl in *; rewrite -(ltn_add2r 1) !addn1 in B2.
              by done.
        - move => m1 m2 /andP [B1 B2].
          specialize (STRys m1.+1 m2.+1).
          feed STRys.
          apply/andP; split.
          + by rewrite ltnS. 
          + by simpl in *; rewrite -(ltn_add2r 1) !addn1 in B2.
              by done.
        - intros. specialize (LE n0.+1). simpl in LE.
          unfold distances. simpl. by done.
      }
    Qed.

  End Lemmas.

End NondecreasingSequence.