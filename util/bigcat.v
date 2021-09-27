Require Export prosa.util.tactics prosa.util.notation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
Require Export prosa.util.tactics prosa.util.ssrlia prosa.util.list.

(** In this section, we introduce lemmas about the concatenation
    operation performed over arbitrary sequences. *)
Section BigCatNatLemmas.

  (** Consider any type [T] supporting equality comparisons... *)
  Variable T : eqType.

  (** ...and a function [f] that, given an index, yields a sequence. *)
  Variable f : nat -> seq T.
  
  (** In this section, we prove that the concatenation over sequences works as expected: 
      no element is lost during the concatenation, and no new element is introduced. *)
  Section BigCatNatElements.
    
    (** First, we show that the concatenation comprises all the elements of each sequence; 
        i.e. any element contained in one of the sequences will also be an element of the 
        result of the concatenation. *)
    Lemma mem_bigcat_nat :
      forall x m n j,
        m <= j < n ->
        x \in f j ->
        x \in \cat_(m <= i < n) (f i).
    Proof.
      intros x m n j LE IN; move: LE => /andP [LE LE0].
      rewrite -> big_cat_nat with (n := j); simpl; [| by ins | by apply ltnW].
      rewrite mem_cat; apply/orP; right.
      destruct n; first by rewrite ltn0 in LE0.
      rewrite big_nat_recl; last by ins.
      by rewrite mem_cat; apply/orP; left.
    Qed.
      
    (** Conversely, we prove that any element belonging to a concatenation of sequences 
        must come from one of the sequences. *)
    Lemma mem_bigcat_nat_exists :
      forall x m n,
        x \in \cat_(m <= i < n) (f i) ->
        exists i,
          x \in f i /\ m <= i < n.
    Proof.
      intros x m n IN.
      induction n; first by rewrite big_geq // in IN.
      destruct (leqP m n); last by rewrite big_geq ?in_nil // ltnW in IN.
      rewrite big_nat_recr // /= mem_cat in IN.
      move: IN => /orP [HEAD | TAIL].
      - apply IHn in HEAD; destruct HEAD; exists x0.
        move: H => [H /andP [H0 H1]].
        split; first by done.
        by apply/andP; split; last by apply ltnW.
      - exists n; split; first by done.
        by apply/andP; split; last apply ltnSn.
    Qed.

    (** We also restate lemma [mem_bigcat_nat] in terms of ordinals. *)
    Lemma mem_bigcat_ord :
      forall (x : T) (n : nat) (j : 'I_n) (f : 'I_n -> seq T),
        j < n ->
        x \in (f j) ->
        x \in \cat_(i < n) (f i).
    Proof.
      move=> x; elim=> [//|n IHn] j f' Hj Hx.
      rewrite big_ord_recr /= mem_cat; apply /orP.
      move: Hj; rewrite ltnS leq_eqVlt => /orP [/eqP Hj|Hj].
      - by right; rewrite (_ : ord_max = j); [|apply ord_inj].
      - left.
        apply (IHn (Ordinal Hj)); [by []|].
        by set j' := widen_ord _ _; have -> : j' = j; [apply ord_inj|].
    Qed.
      
  End BigCatNatElements.

  (** In this section, we show how we can preserve uniqueness of the elements 
      (i.e. the absence of a duplicate) over a concatenation of sequences. *)
  Section BigCatNatDistinctElements.

    (** Assume that there are no duplicates in each of the possible
        sequences to concatenate... *)
    Hypothesis H_uniq_seq : forall i, uniq (f i).

    (** ...and that there are no elements in common between the sequences. *)
    Hypothesis H_no_elements_in_common :
      forall x i1 i2, x \in f i1 -> x \in f i2 -> i1 = i2.
    
    (** We prove that the concatenation will yield a sequence with unique elements. *)
    Lemma bigcat_nat_uniq :
      forall n1 n2,
        uniq (\cat_(n1 <= i < n2) (f i)).
    Proof.
      intros n1 n2.
      case (leqP n1 n2) => [LE | GT]; last by rewrite big_geq // ltnW.
      rewrite -[n2](addKn n1).
      rewrite -addnBA //; set delta := n2 - n1.
      induction delta; first by rewrite addn0 big_geq.
      rewrite addnS big_nat_recr /=; last by apply leq_addr.
      rewrite cat_uniq; apply/andP; split; first by apply IHdelta.
      apply /andP; split; last by apply H_uniq_seq.
      rewrite -all_predC; apply/allP; intros x INx.
      simpl; apply/negP; unfold not; intro BUG.
      apply mem_bigcat_nat_exists in BUG.
      move: BUG => [i [IN /andP [_ LTi]]].
      apply H_no_elements_in_common with (i1 := i) in INx; last by done.
      by rewrite INx ltnn in LTi.
    Qed.

    (** Conversely, if the concatenation of the sequences has no duplicates, any
        element can only belong to a single sequence. *)
    Lemma bigcat_ord_uniq_reverse :
      forall (n : nat) (f : 'I_n -> seq T),
        uniq (\cat_(i < n) (f i)) ->
        (forall x i1 i2,
            x \in (f i1) -> x \in (f i2) -> i1 = i2).
    Proof.
      case=> [|n]; [by move=> f' Huniq x; case|].
      elim: n => [|n IHn] f' Huniq x i1 i2 Hi1 Hi2.
      { move: i1 i2 {Hi1 Hi2}; case; case=> [i1|//]; case; case=> [i2|//].
        apply f_equal, eq_irrelevance. }
      move: (leq_ord i1); rewrite leq_eqVlt => /orP [H'i1|H'i1].
      all: move: (leq_ord i2); rewrite leq_eqVlt => /orP [H'i2|H'i2].
      { by apply ord_inj; move: H'i1 H'i2 => /eqP -> /eqP ->. }
      { exfalso.
        move: Huniq; rewrite big_ord_recr cat_uniq => /andP [_ /andP [H _]].
        move: H; apply /negP; rewrite Bool.negb_involutive.
        apply /hasP; exists x => /=.
        { set o := ord_max; suff -> : o = i1; [by []|].
          by apply ord_inj; move: H'i1 => /eqP ->. }
        apply (mem_bigcat_ord _ _ (Ordinal H'i2)) => //.
        by set o := widen_ord _ _; suff -> : o = i2; [|apply ord_inj]. }
      { exfalso.
        move: Huniq; rewrite big_ord_recr cat_uniq => /andP [_ /andP [H _]].
        move: H; apply /negP; rewrite Bool.negb_involutive.
        apply /hasP; exists x => /=.
        { set o := ord_max; suff -> : o = i2; [by []|].
          by apply ord_inj; move: H'i2 => /eqP ->. }
        apply (mem_bigcat_ord _ _ (Ordinal H'i1)) => //.
        by set o := widen_ord _ _; suff -> : o = i1; [|apply ord_inj]. }
      move: Huniq; rewrite big_ord_recr cat_uniq => /andP [Huniq _].
      apply ord_inj; rewrite -(inordK H'i1) -(inordK H'i2); apply f_equal.
      apply (IHn _ Huniq x).
      { set i1' := widen_ord _ _; suff -> : i1' = i1; [by []|].
        by apply ord_inj; rewrite /= inordK. }
      set i2' := widen_ord _ _; suff -> : i2' = i2; [by []|].
      by apply ord_inj; rewrite /= inordK.
    Qed.

  End BigCatNatDistinctElements.

  (** We show that filtering a concatenated sequence by any predicate
      [P] is the same as concatenating the elements of the sequence
      that satisfy [P]. *) 
  Lemma bigcat_nat_filter_eq_filter_bigcat_nat :
    forall {X : Type} (F : nat -> seq X) (P : X -> bool) (t1 t2 : nat),
      [seq x <- \cat_(t1 <= t < t2) F t | P x] = \cat_(t1 <= t < t2)[seq x <- F t | P x].
  Proof.
    intros.
    specialize (leq_total t1 t2) => /orP [T1_LT | T2_LT].
    + have EX: exists Δ, t2 = t1 + Δ by simpl; exists (t2 - t1); ssrlia.
      move: EX => [Δ EQ]; subst t2.
      induction Δ.
      { by rewrite addn0 !big_geq => //. }
      { rewrite addnS !big_nat_recr => //=; try by rewrite leq_addr.
        rewrite filter_cat IHΔ => //.
        by ssrlia. }
    + by rewrite !big_geq => //.
  Qed.

  (** We show that the size of a concatenated sequence is the same as
      summation of sizes of each element of the sequence. *)
  Lemma size_big_nat : 
    forall {X : Type} (F : nat -> seq X) (t1 t2 : nat),
      \sum_(t1 <= t < t2) size (F t) =
      size (\cat_(t1 <= t < t2) F t).
  Proof.
    intros.
    specialize (leq_total t1 t2) => /orP [T1_LT | T2_LT].
    - have EX: exists Δ, t2 = t1 + Δ by simpl; exists (t2 - t1); ssrlia.
      move: EX => [Δ EQ]; subst t2.
      induction Δ.
      { by rewrite addn0 !big_geq => //. }
      { rewrite addnS !big_nat_recr => //=; try by rewrite leq_addr.
        by rewrite size_cat IHΔ => //; ssrlia. }         
    - by rewrite !big_geq => //.
  Qed.      
  
End BigCatNatLemmas.


(** In this section, we introduce a few lemmas about the concatenation
    operation performed over arbitrary sequences. *)
Section BigCatLemmas.

  (** Consider any two types [X] and [Y] supporting equality comparisons... *)
  Variable X Y : eqType.

  (** ...and a function [f] that, given an index [X], yields a sequence of [Y]. *)
  Variable f : X -> seq Y.

  (** First, we show that the concatenation comprises all the elements of each sequence; 
      i.e. any element contained in one of the sequences will also be an element of the 
      result of the concatenation. *)
  Lemma mem_bigcat :
      forall x y s, 
      x \in s ->
      y \in f x -> 
      y \in \cat_(x <- s) f x.
  Proof.
    move=> x y s INs INfx.
    induction s; first by done.
    rewrite big_cons mem_cat.
    move:INs; rewrite in_cons => /orP[/eqP HEAD | CONS].
    - by rewrite -HEAD; apply /orP; left.
    - by apply /orP; right; apply IHs.
  Qed.

  (** Conversely, we prove that any element belonging to a concatenation of sequences 
      must come from one of the sequences. *)
  Lemma mem_bigcat_exists :
    forall s y,
      y \in \cat_(x <- s) f x ->
      exists x, x \in s /\ y \in f x.
  Proof.
    induction s; first by rewrite big_nil.
    move=> y.
    rewrite big_cons mem_cat => /orP[HEAD | CONS].
    - exists a.
      by split => //; apply mem_head.
    - move: (IHs _ CONS) => [x [INs INfx]].
      exists x; split =>//.
      by rewrite in_cons; apply /orP; right.
  Qed.

  (** Next, we show that a map and filter operation can be done either 
      before or after a concatenation, leading to the same result. *)
  Lemma bigcat_filter_eq_filter_bigcat :
    forall xss P, 
      [seq x <- \cat_(xs <- xss) f xs | P x]  =        
      \cat_(xs <- xss) [seq x <- f xs | P x] .
  Proof.
    move=> xss P.
    induction xss.
    - by rewrite !big_nil.
    - by rewrite !big_cons filter_cat IHxss.
  Qed.

  (** In this section, we show how we can preserve uniqueness of the elements 
      (i.e. the absence of a duplicate) over a concatenation of sequences. *)
  Section BigCatDistinctElements.

    (** Assume that there are no duplicates in each of the possible
        sequences to concatenate... *)      
    Hypothesis H_uniq_f : forall x, uniq (f x).
    
    (** ...and that there are no elements in common between the sequences. *)
    Hypothesis H_no_elements_in_common :
      forall x y z,
        x \in f y -> x \in f z -> y = z.
    
    (** We prove that the concatenation will yield a sequence with unique elements. *)
    Lemma bigcat_uniq :
      forall xs,
        uniq xs ->
        uniq (\cat_(x <- xs) (f x)).
    Proof.
      induction xs; first by rewrite big_nil.
      rewrite cons_uniq => /andP [NINxs UNIQ].
      rewrite big_cons cat_uniq.
      apply /andP; split; first by apply H_uniq_f.
      apply /andP; split; last by apply IHxs.
      apply /hasPn=> x IN; apply /negP=> INfa.
      move: (mem_bigcat_exists _ _ IN) => [a' [INxs INfa']].
      move: (H_no_elements_in_common x a a' INfa INfa') => EQa.
      by move: NINxs; rewrite EQa => /negP CONTRA.
    Qed.

  End BigCatDistinctElements.

  (** In this section, we show some properties of the concatenation of 
      sequences in combination with a function [g] that cancels [f]. *)
  Section BigCatWithCancelFunctions.

    (** Consider a function [g]... *)
    Variable g : Y -> X.

    (** ... and assume that [g] can cancel [f] starting from an element of 
        the sequence [f x]. *)
    Hypothesis H_g_cancels_f : forall x y, y \in f x -> g y = x.

    (** First, we show that no element of a sequence [f x1] can be fed into 
        [g] and obtain an element [x2] which differs from [x1]. Hence, filtering 
        by this condition always leads to the empty sequence. *)
    Lemma seq_different_elements_nil :
      forall x1 x2,
        x1 != x2 ->
        [seq x <- f x1 | g x == x2] = [::].
    Proof.
      move => x1 x2 => /negP NEQ. 
      apply filter_in_pred0.
      move => y IN; apply/negP => /eqP EQ2.
      apply: NEQ; apply/eqP.
      move: (H_g_cancels_f _ _ IN) => EQ1.
      by rewrite -EQ1 -EQ2.
    Qed.

    (** Finally, assume we are given an element [y] which is contained in a 
        duplicate-free sequence [xs]. Then, [f] is applied to each element of 
        [xs], but only the elements for which [g] yields [y] are kept. In this 
        scenario, concatenating the resulting sequences will always lead to [f y]. *)
    Lemma bigcat_seq_uniqK :
      forall y xs,
        y \in xs ->
        uniq xs -> 
        \cat_(x <- xs) [seq x' <- f x | g x' == y] = f y. 
    Proof.
      move=> y xs IN UNI.
      induction xs as [ | x' xs]; first by done.
      move: IN; rewrite in_cons => /orP [/eqP EQ| IN].
      { subst; rewrite !big_cons.
        have -> :  [seq x <- f x' | g x == x'] = f x'.
        { apply/all_filterP/allP.
          intros y IN; apply/eqP.
          by apply H_g_cancels_f. }
        have ->: \cat_(j<-xs)[seq x <- f j | g x == x'] = [::]; last by rewrite cats0.
        rewrite big1_seq //; move => xs2 /andP [_ IN].
        have NEQ: xs2 != x'; last by rewrite seq_different_elements_nil.
        apply/neqP; intros EQ; subst x'.
        move: UNI; rewrite cons_uniq => /andP [NIN _].
        by move: NIN => /negP NIN; apply: NIN. }
      { rewrite big_cons IHxs //; last by move:UNI; rewrite cons_uniq=> /andP[_ ?].
        have NEQ: (x' != y); last by rewrite seq_different_elements_nil.
        apply/neqP; intros EQ; subst x'.
        move: UNI; rewrite cons_uniq => /andP [NIN _].
        by move: NIN => /negP NIN; apply: NIN. }
    Qed.
    
  End BigCatWithCancelFunctions.

End BigCatLemmas.

(** In this section, we show that the number of elements of the result
    of a nested mapping and concatenation operation is independent from 
    the order in which the concatenations are performed. *)
Section BigCatNestedCount.
  
  (** Consider any three types supporting equality comparisons... *)
  Variable X Y Z : eqType.

  (** ... a function [F] that, given two indices, yields a sequence... *)
  Variable F : X -> Y -> seq Z.

  (** and a predicate [P]. *)
  Variable P : pred Z.

  (** Assume that, given two sequences [xs] and [ys], their elements are fed to 
      [F] in a pair-wise fashion. The resulting lists are then concatenated. 
      The following lemma shows that, when the operation described above is performed, 
      the number of elements respecting [P] in the resulting list is the same, regardless 
      of the order in which [xs] and [ys] are combined. *)
  Lemma bigcat_count_exchange :
    forall xs ys,
      count P (\cat_(x <- xs) \cat_(y <- ys) F x y) =
      count P (\cat_(y <- ys) \cat_(x <- xs) F x y). 
  Proof.
    induction xs as [|x0 seqX IHxs]; induction ys as [|y0 seqY IHys]; intros.
    { by rewrite !big_nil. }
    { by rewrite big_cons count_cat -IHys !big_nil. } 
    { by rewrite big_cons count_cat IHxs !big_nil. } 
    { rewrite !big_cons !count_cat.
      apply/eqP; rewrite -!addnA eqn_add2l.
      rewrite IHxs -IHys !big_cons !count_cat.
      rewrite addnC -!addnA eqn_add2l addnC eqn_add2l.
      by rewrite IHxs. } 
  Qed.

End BigCatNestedCount.


