Require Export prosa.util.minmax.
Require Import prosa.classic.util.tactics prosa.classic.util.notation prosa.classic.util.sorting prosa.classic.util.nat prosa.classic.util.list.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Section MinMaxSeq.

  Section ArgGeneric.

    Context {T1 T2: eqType}.

    Variable rel: T2 -> T2 -> bool.
    Variable F: T1 -> T2.
    
    Fixpoint seq_argmin (l: seq T1) :=
      if l is x :: l' then
        if seq_argmin l' is Some y then
          if rel (F x) (F y) then Some x else Some y
        else Some x
      else None.

    Fixpoint seq_argmax (l: seq T1) :=
      if l is x :: l' then
        if seq_argmax l' is Some y then
          if rel (F y) (F x) then Some x else Some y
        else Some x
      else None.
    
    Section Lemmas.

      Lemma seq_argmin_exists:
        forall l x,
          x \in l ->
          seq_argmin l != None.
      Proof.
        induction l; first by done.
        intros x; rewrite in_cons.
        move => /orP [/eqP EQ | IN] /=;
          first by subst; destruct (seq_argmin l); first by case: ifP.
        by destruct (seq_argmin l); first by case: ifP.
      Qed.
        
      Lemma seq_argmin_in_seq:
        forall l x,
          seq_argmin l = Some x ->
          x \in l.
      Proof.
        induction l; simpl; first by done.
        intros x ARG.
        destruct (seq_argmin l);
          last by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        destruct (rel (F a) (F s));
          first by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        case: ARG => EQ; subst.
        by rewrite in_cons; apply/orP; right; apply IHl.
      Qed.

      Lemma seq_argmax_exists:
        forall l x,
          x \in l ->
          seq_argmax l != None.
      Proof.
        induction l; first by done.
        intros x; rewrite in_cons.
        move => /orP [/eqP EQ | IN] /=;
          first by subst; destruct (seq_argmax l); first by case: ifP.
        by destruct (seq_argmax l); first by case: ifP.
      Qed.
        
      Lemma seq_argmax_in_seq:
        forall l x,
          seq_argmax l = Some x ->
          x \in l.
      Proof.
        induction l; simpl; first by done.
        intros x ARG.
        destruct (seq_argmax l);
          last by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        destruct (rel (F s) (F a));
          first by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        case: ARG => EQ; subst.
        by rewrite in_cons; apply/orP; right; apply IHl.
      Qed.
      
      Section TotalOrder.

        Hypothesis H_transitive: transitive rel.
        
        Variable l: seq T1.
        Hypothesis H_total_over_list:
          forall x y,
            x \in l ->
            y \in l ->
            rel (F x) (F y) || rel (F y) (F x).

        Lemma seq_argmin_computes_min:
          forall x y,
            seq_argmin l = Some x ->
            y \in l ->
            rel (F x) (F y).
        Proof.
          rename H_transitive into TRANS, H_total_over_list into TOT, l into l'.
          induction l'; first by done.
          intros x y EQmin IN; simpl in EQmin.
          rewrite in_cons in IN.
          move: IN => /orP [/eqP EQ | IN].
          {
            subst; destruct (seq_argmin l') eqn:ARG; last first.
            {
              case: EQmin => EQ; subst.
              by exploit (TOT x x); try (by rewrite in_cons eq_refl); rewrite orbb.
            }
            {
              destruct (rel (F a) (F s)) eqn:REL; case: EQmin => EQ; subst;
                first by exploit (TOT x x); try (by rewrite in_cons eq_refl); rewrite orbb.
              exploit (TOT a x).
              - by rewrite in_cons eq_refl.
              - by rewrite in_cons; apply/orP; right; apply seq_argmin_in_seq.
              - by rewrite REL /=.
            }
          }
          { 
            destruct (seq_argmin l') eqn:ARG.
            {
              destruct (rel (F a) (F s)) eqn:REL; case: EQmin => EQ; subst; last first.
              {
                apply IHl'; [| by done | by done].
                by intros x0 y0 INx INy; apply TOT; rewrite in_cons; apply/orP; right.
              }
              {                
                apply TRANS with (y := F s); first by done.
                apply IHl'; [| by done | by done].
                by intros x0 y0 INx INy; apply TOT; rewrite in_cons; apply/orP; right.
              }
            }
            {
              case: EQmin => EQ; subst.
              by apply seq_argmin_exists in IN; rewrite ARG in IN.
            }
          }
        Qed.

        Lemma seq_argmax_computes_max:
          forall x y,
            seq_argmax l = Some x ->
            y \in l ->
            rel (F y) (F x).
        Proof.
          rename H_transitive into TRANS, H_total_over_list into TOT, l into l'.
          induction l'; first by done.
          intros x y EQmin IN; simpl in EQmin.
          rewrite in_cons in IN.
          move: IN => /orP [/eqP EQ | IN].
          {
            subst; destruct (seq_argmax l') eqn:ARG; last first.
            {
              case: EQmin => EQ; subst.
              by exploit (TOT x x); try (by rewrite in_cons eq_refl); rewrite orbb.
            }
            {
              destruct (rel (F s) (F a)) eqn:REL; case: EQmin => EQ; subst;
                first by exploit (TOT x x); try (by rewrite in_cons eq_refl); rewrite orbb.
              exploit (TOT a x).
              - by rewrite in_cons eq_refl.
              - by rewrite in_cons; apply/orP; right; apply seq_argmax_in_seq.
              - by rewrite REL orbF.
            }
          }
          { 
            destruct (seq_argmax l') eqn:ARG.
            {
              destruct (rel (F s) (F a)) eqn:REL; case: EQmin => EQ; subst; last first.
              {
                apply IHl'; [| by done | by done].
                by intros x0 y0 INx INy; apply TOT; rewrite in_cons; apply/orP; right.
              }
              {                
                apply TRANS with (y := F s); last by done.
                apply IHl'; [| by done | by done].
                by intros x0 y0 INx INy; apply TOT; rewrite in_cons; apply/orP; right.
              }
            }
            {
              case: EQmin => EQ; subst.
              by apply seq_argmax_exists in IN; rewrite ARG in IN.
            }
          }
        Qed.

      End TotalOrder.

    End Lemmas.

  End ArgGeneric.
  
  Section MinGeneric.

    Context {T: eqType}.
    Variable rel: rel T.
    
    Definition seq_min := seq_argmin rel id.
    Definition seq_max := seq_argmax rel id.

    Section Lemmas.

      Lemma seq_min_exists:
        forall l x,
          x \in l ->
          seq_min l != None.
      Proof.
        by apply seq_argmin_exists.
      Qed.
        
      Lemma seq_min_in_seq:
        forall l x,
          seq_min l = Some x ->
          x \in l.
      Proof.
        by apply seq_argmin_in_seq.
      Qed.

      Lemma seq_max_exists:
        forall l x,
          x \in l ->
          seq_max l != None.
      Proof.
        by apply seq_argmax_exists.
      Qed.
        
      Lemma seq_max_in_seq:
        forall l x,
          seq_max l = Some x ->
          x \in l.
      Proof.
        by apply seq_argmax_in_seq.
      Qed.
      
      Section TotalOrder.

        Hypothesis H_transitive: transitive rel.
        
        Variable l: seq T.
        Hypothesis H_total_over_list:
          forall x y,
            x \in l ->
            y \in l ->
            rel x y || rel y x.

        Lemma seq_min_computes_min:
          forall x y,
            seq_min l = Some x ->
            y \in l ->
            rel x y.
        Proof.
          by apply seq_argmin_computes_min.
        Qed.

        Lemma seq_max_computes_max:
          forall x y,
            seq_max l = Some x ->
            y \in l ->
            rel y x.
        Proof.
          by apply seq_argmax_computes_max.
        Qed.

      End TotalOrder.

    End Lemmas.
        
  End MinGeneric.

  Section ArgNat.
      
    Context {T: eqType}.

    Variable F: T -> nat.

    Definition seq_argmin_nat := seq_argmin leq F.
    Definition seq_argmax_nat := seq_argmax leq F.

    Section Lemmas.

      Lemma seq_argmin_nat_exists:
        forall l x,
          x \in l ->
          seq_argmin_nat l != None.
      Proof.
        by apply seq_argmin_exists.
      Qed.
        
      Lemma seq_argmin_nat_in_seq:
        forall l x,
          seq_argmin_nat l = Some x ->
          x \in l.
      Proof.
        by apply seq_argmin_in_seq.
      Qed.

      Lemma seq_argmax_nat_exists:
        forall l x,
          x \in l ->
          seq_argmax_nat l != None.
      Proof.
        by apply seq_argmax_exists.
      Qed.
        
      Lemma seq_argmax_nat_in_seq:
        forall l x,
          seq_argmax_nat l = Some x ->
          x \in l.
      Proof.
        by apply seq_argmax_in_seq.
      Qed.
      
      Section TotalOrder.

        Lemma seq_argmin_nat_computes_min:
          forall l x y,
            seq_argmin_nat l = Some x ->
            y \in l ->
            F x <= F y.
        Proof.
          intros l x y SOME IN.
          apply seq_argmin_computes_min with (l0 := l); try (by done).
          - by intros x1 x2 x3; apply leq_trans.
          - by intros x1 x2 IN1 IN2; apply leq_total.
        Qed.

        Lemma seq_argmax_nat_computes_max:
          forall l x y,
            seq_argmax_nat l = Some x ->
            y \in l ->
            F x >= F y.
        Proof.
          intros l x y SOME IN.
          apply seq_argmax_computes_max with (l0 := l); try (by done).
          - by intros x1 x2 x3; apply leq_trans.
          - by intros x1 x2 IN1 IN2; apply leq_total.
        Qed.

      End TotalOrder.

    End Lemmas.
        
  End ArgNat.
  
  Section MinNat.

    Definition seq_min_nat := seq_argmin leq id.
    Definition seq_max_nat := seq_argmax leq id.

    Section Lemmas.

      Lemma seq_min_nat_exists:
        forall l x,
          x \in l ->
          seq_min_nat l != None.
      Proof.
        by apply seq_argmin_exists.
      Qed.
        
      Lemma seq_min_nat_in_seq:
        forall l x,
          seq_min_nat l = Some x ->
          x \in l.
      Proof.
        by apply seq_argmin_in_seq.
      Qed.

      Lemma seq_max_nat_exists:
        forall l x,
          x \in l ->
          seq_max_nat l != None.
      Proof.
        by apply seq_argmax_exists.
      Qed.
        
      Lemma seq_max_nat_in_seq:
        forall l x,
          seq_max_nat l = Some x ->
          x \in l.
      Proof.
        by apply seq_argmax_in_seq.
      Qed.
      
      Section TotalOrder.

        Lemma seq_min_nat_computes_min:
          forall l x y,
            seq_min_nat l = Some x ->
            y \in l ->
            x <= y.
        Proof.
          intros l x y SOME IN.
          apply seq_min_computes_min with (l0 := l); try (by done).
          - by intros x1 x2 x3; apply leq_trans.
          - by intros x1 x2 IN1 IN2; apply leq_total.
        Qed.

        Lemma seq_max_nat_computes_max:
          forall l x y,
            seq_max_nat l = Some x ->
            y \in l ->
            x >= y.
        Proof.
          intros l x y SOME IN.
          apply seq_max_computes_max with (l0 := l); try (by done).
          - by intros x1 x2 x3; apply leq_trans.
          - by intros x1 x2 IN1 IN2; apply leq_total.
        Qed.

      End TotalOrder.

    End Lemmas.
        
  End MinNat.

  Section NatRange.
    
    Definition values_between (a b: nat) :=
      filter (fun x => x >= a) (map (@nat_of_ord _) (enum 'I_b)).

    Lemma mem_values_between a b:
      forall x, x \in values_between a b = (a <= x < b).
    Proof.
      intros x; rewrite mem_filter.
      apply/idP/idP.
      {
        move => /andP [GE IN].
        move: IN => /mapP [x' IN] EQ; subst.
        rewrite mem_enum in IN.
        by apply/andP; split.
      }
      {
        move => /andP [GE LT].
        rewrite GE andTb.
        apply/mapP; exists (Ordinal LT); last by done.
        by rewrite mem_enum.
      }
    Qed.

    Definition min_nat_cond P (a b: nat) :=
      seq_min_nat (filter P (values_between a b)).

    Definition max_nat_cond P (a b: nat) :=
      seq_max_nat (filter P (values_between a b)).

    Lemma min_nat_cond_exists:
      forall (P: nat -> bool) (a b: nat) x,
        a <= x < b ->
        P x ->
        min_nat_cond P a b != None.
    Proof.
      intros P a b x LE HOLDS.
      apply seq_argmin_exists with (x0 := x).
      by rewrite mem_filter mem_values_between HOLDS LE.
    Qed.
    
    Lemma min_nat_cond_in_seq:
      forall P a b x,
        min_nat_cond P a b = Some x ->
        a <= x < b /\ P x.
    Proof.
      intros P a b x SOME.
      apply seq_min_nat_in_seq in SOME.
      rewrite mem_filter in SOME; move: SOME => /andP [Px LE].
      by split; first by rewrite mem_values_between in LE.
    Qed.

    Lemma min_nat_cond_computes_min:
      forall P a b x,
        min_nat_cond P a b = Some x ->
        (forall y, a <= y < b -> P y -> x <= y).
    Proof.
      intros P a b x SOME y LE Py.
      apply seq_min_nat_computes_min with (y := y) in SOME; first by done.
      by rewrite mem_filter Py andTb mem_values_between.
    Qed.

    Lemma max_nat_cond_exists:
      forall (P: nat -> bool) (a b: nat) x,
        a <= x < b ->
        P x ->
        max_nat_cond P a b != None.
    Proof.
      intros P a b x LE HOLDS.
      apply seq_argmax_exists with (x0 := x).
      by rewrite mem_filter mem_values_between HOLDS LE.
    Qed.

    Lemma max_nat_cond_in_seq:
      forall P a b x,
        max_nat_cond P a b = Some x ->
        a <= x < b /\ P x.
    Proof.
      intros P a b x SOME.
      apply seq_max_nat_in_seq in SOME.
      rewrite mem_filter in SOME; move: SOME => /andP [Px LE].
      by split; first by rewrite mem_values_between in LE.
    Qed.

    Lemma max_nat_cond_computes_max:
      forall P a b x,
        max_nat_cond P a b = Some x ->
        (forall y, a <= y < b -> P y -> y <= x).
    Proof.
      intros P a b x SOME y LE Py.
      apply seq_max_nat_computes_max with (y := y) in SOME; first by done.
      by rewrite mem_filter Py andTb mem_values_between.
    Qed.
    
  End NatRange.

End MinMaxSeq.

Section Kmin.

    Context {T1 T2: eqType}.

    Variable rel: T2 -> T2 -> bool.
    Variable F: T1 -> T2.

    Fixpoint seq_argmin_k (l: seq T1) (k: nat) :=
      if k is S k' then
        if (seq_argmin rel F l) is Some min_x then
          let l_without_min := rem min_x l in
            min_x :: seq_argmin_k l_without_min k'
        else [::]
      else [::].

      Lemma seq_argmin_k_exists:
        forall k l x,
          k > 0 ->
          x \in l ->
          seq_argmin_k l k != [::].
      Proof.
        induction k; first by done.
        move => l x _ IN /=.
        destruct (seq_argmin rel F l) as [|] eqn:MIN; first by done.
        suff NOTNONE: seq_argmin rel F l != None by rewrite MIN in NOTNONE.
        by apply seq_argmin_exists with (x0 := x).
      Qed.
    
End Kmin.