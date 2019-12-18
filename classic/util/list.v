Require Export prosa.util.list.

Require Import prosa.classic.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Lemmas about lists without duplicates. *)
Section UniqList.

  Lemma idx_lt_rcons :
    forall {T: eqType} (l: seq T) i x0,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l < i.+1] =
        rcons [seq x <- l | index x l < i] (nth x0 l i).
  Proof.
    intros T l i x0 UNIQ LT.
    generalize dependent i.
    induction l as [| l' x] using last_ind; first by ins; rewrite ltn0 in LT.
    {
      intros i LT.
      rewrite size_rcons in LT.
      rewrite filter_rcons.
      rewrite -cats1 index_cat; desf; simpl in *;
        try (by rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN _]; rewrite Heq0 in NOTIN).
      {
        rewrite eq_refl addn0 in Heq.
        rewrite filter_cat /=.
        assert (EQ: i = size l'); first by apply/eqP; rewrite eqn_leq; apply/andP; split.
        rewrite index_cat Heq0 /= eq_refl addn0 EQ ltnn cats0.
        rewrite nth_cat ltnn subnn /=.
        f_equal; apply eq_in_filter; red; intros y INy.
        by rewrite index_cat INy ltnS index_size index_mem INy.
      }
      {
        rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
        rewrite eq_refl addn0 in Heq.
        apply negbT in Heq; rewrite -leqNgt in Heq.
        rewrite nth_cat Heq.
        rewrite filter_cat /= index_cat Heq0 /= eq_refl addn0.
        rewrite ltnS in LT; rewrite ltnNge LT /= cats0 cats1.
        apply eq_trans with (y := [seq x1 <- l' | index x1 l' < i.+1]);
          first by apply eq_in_filter; red; intros y INy; rewrite -cats1 index_cat INy.
        rewrite IHl //; f_equal; apply eq_in_filter; intros y INy.
        by rewrite -cats1 index_cat INy.
      }
    }
  Qed.
  
  Lemma filter_idx_lt_take :
    forall {T: eqType} (l: seq T) i,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l < i] = take i l.
  Proof.
    intros T l i UNIQ LT.
    generalize dependent l.
    induction i.
    {
      intros l UNIQ LT; destruct l as [| x0 l']; first by done.
      by apply eq_trans with (filter pred0 (x0 :: l'));
        [by apply eq_filter | by rewrite filter_pred0].
    }
    {
      intros l UNIQ LT.
      destruct (lastP l) as [| l' x]; first by rewrite ltn0 in LT.
      rewrite size_rcons ltnS in LT.
      rewrite (take_nth x); last by rewrite size_rcons; apply (leq_trans LT).
      rewrite -> idx_lt_rcons with (x0 := x); try (by done);
        last by rewrite size_rcons; apply (leq_trans LT).
      by f_equal; apply IHi; last by rewrite size_rcons; apply (leq_trans LT).
    }  
  Qed.

  Lemma filter_idx_le_takeS :
    forall {T: eqType} (l: seq T) i,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l <= i] = take i.+1 l.
  Proof.
    intros T l i UNIQ LT.
    induction l as [| x0 l]; first by done.
    simpl; rewrite eq_refl leq0n; f_equal.
    apply eq_trans with (y := [seq x <- l | index x l < i]).
    {
      apply eq_in_filter; red; intros x IN.
      desf; subst; last by done.
      by simpl in *; rewrite IN andFb in UNIQ.
    }
    simpl in *; desf.
    rewrite /= ltnS in LT.
    rewrite leq_eqVlt in LT; desf.
    {
      rewrite take_size.
      apply eq_trans with (y := filter predT l); last by rewrite filter_predT.
      by apply eq_in_filter; red; ins; rewrite index_mem.
    }
    by apply filter_idx_lt_take.
  Qed.

  Lemma mapP2 (T: Type) (T': eqType) (s: seq T) (f: T -> T') y:
    reflect (exists2 x, List.In x s & y = f x) (y \in map f s).
  Proof.
    elim: s => [|x s IHs]; first by right; case.
    rewrite /= in_cons eq_sym; case Hxy: (f x == y);
      first by left; exists x; [by left | by rewrite (eqP Hxy)].
    apply: (iffP IHs) => [[x' Hx' ->]|[x' Hx' Dy]];
      first by exists x'; [by right | by done].
    exists x'; last by done.
    by subst y; move: Hx' => [EQ | IN] //; subst; rewrite eq_refl in Hxy.
  Qed. 
  
End UniqList.


(* Additional lemmas about list zip. *)
Section Zip.
  
  Lemma zipP {T: eqType} (x0: T) (P: _ -> _ -> bool) (X Y: seq T):
    size X = size Y ->
    reflect (forall i, i < size (zip X Y) -> P (nth x0 X i) (nth x0 Y i))
            (all (fun p => P (fst p) (snd p)) (zip X Y)).
  Proof.
    intro SIZE; apply/introP.
    {
      move => /allP ALL i LT.
      apply (ALL (nth x0 X i,nth x0 Y i)).
      by rewrite -nth_zip; [by apply mem_nth | by done].
    }
    {
      rewrite -has_predC; unfold predC.
      move => /hasP HAS; simpl in *; destruct HAS as [x IN NOT].
      unfold not; intro BUG.
      exploit (BUG (index x (zip X Y))).
        by rewrite index_mem.
      have NTH := @nth_zip _ _ x0 x0 X Y (index x (zip X Y)) SIZE.
      destruct x as [x1 x2].
      rewrite {1}nth_index in NTH; last by done.
      clear BUG; intros BUG.
      inversion NTH as [[NTH0 NTH1]]; rewrite -NTH0 in NTH1.
      by rewrite -NTH0 -NTH1 in BUG; rewrite BUG in NOT.
    }
  Qed.

  Lemma mem_zip_exists :
    forall (T T': eqType) (x1: T) (x2: T') l1 l2 elem elem',
      size l1 = size l2 ->
      (x1, x2) \in zip l1 l2 ->
      exists idx,
        idx < size l1 /\
        idx < size l2 /\
        x1 = nth elem l1 idx /\
        x2 = nth elem' l2 idx.
  Proof.
    intros T T' x1 x2 l1 l2 elem elem' SIZE IN.
    assert (LT: index (x1, x2) (zip l1 l2) < size l1).
    {
      apply leq_trans with (n := size (zip l1 l2)); first by rewrite index_mem.
      by rewrite size_zip; apply geq_minl.
    }
    have NTH := @nth_index _ (elem,elem') (x1, x2) (zip l1 l2) IN.
    rewrite nth_zip in NTH; last by done.
    inversion NTH; rewrite H1 H0; rewrite H0 in H1.
    by exists (index (x1, x2) (zip l1 l2)); repeat split; try (by done); rewrite -?SIZE.
  Qed.

  Lemma mem_zip :
    forall (T T': eqType) (x1: T) (x2: T') l1 l2,
      size l1 = size l2 ->
      (x1, x2) \in zip l1 l2 ->
      x1 \in l1 /\ x2 \in l2.
  Proof.
    intros T T' x1 x2 l1 l2 SIZE IN.
    split.
    {
      rewrite -[l1](@unzip1_zip _ _ l1 l2); last by rewrite SIZE.
      by apply/mapP; exists (x1, x2).
    }
    {
      rewrite -[l2](@unzip2_zip _ _ l1 l2); last by rewrite SIZE.
      by apply/mapP; exists (x1, x2).
    }
  Qed.

  Lemma mem_zip_nseq_r :
    forall {T1 T2:eqType} (x: T1) (y: T2) n l,
      size l = n ->
      ((x, y) \in zip l (nseq n y)) = (x \in l).
  Proof.
    intros T1 T2 x y n l SIZE.
    apply/idP/idP.
    {
      intros IN.
      generalize dependent n.
      induction l.
      {
        intros n SIZE IN.
        by destruct n; simpl in IN; rewrite in_nil in IN.
      }
      {
        intros n SIZE; destruct n; first by ins.
        by intros MEM; apply mem_zip in MEM; [des | by rewrite size_nseq].
      }
    }
    {
      intros IN; generalize dependent n.
      induction l; first by rewrite in_nil in IN.
      intros n SIZE; destruct n; first by ins.
      rewrite in_cons in IN; move: IN => /orP [/eqP EQ | IN];
        first by rewrite in_cons; apply/orP; left; apply/eqP; f_equal.
      simpl in *; apply eq_add_S in SIZE.
      by rewrite in_cons; apply/orP; right; apply IHl.
    }
  Qed.

  Lemma mem_zip_nseq_l :
    forall {T1 T2:eqType} (x: T1) (y: T2) n l,
      size l = n ->
      ((x, y) \in zip (nseq n x) l) = (y \in l).
  Proof.
    intros T1 T2 x y n l SIZE.
    apply/idP/idP.
    {
      intros IN.
      generalize dependent n.
      induction l.
      {
        intros n SIZE IN.
        by destruct n; simpl in IN; rewrite in_nil in IN.
      }
      {
        intros n SIZE; destruct n; first by ins.
        by intros MEM; apply mem_zip in MEM; [des | by rewrite size_nseq].
      }
    }
    {
      intros IN; generalize dependent n.
      induction l; first by rewrite in_nil in IN.
      intros n SIZE; destruct n; first by ins.
      rewrite in_cons in IN; move: IN => /orP [/eqP EQ | IN];
        first by rewrite in_cons; apply/orP; left; apply/eqP; f_equal.
      simpl in *; apply eq_add_S in SIZE.
      by rewrite in_cons; apply/orP; right; apply IHl.
    }
  Qed.

  Lemma unzip1_pair:
    forall {T1 T2: eqType} (l: seq T1) (f: T1 -> T2),
      unzip1 [seq (x, f x) | x <- l] = l.
  Proof.
    intros T1 T2.
    induction l; first by done.
    by intros f; simpl; f_equal.
  Qed.

  Lemma unzip2_pair:
    forall {T1 T2: eqType} (l: seq T1) (f: T1 -> T2),
      unzip2 [seq (f x, x) | x <- l] = l.
  Proof.
    intros T1 T2.
    induction l; first by done.
    by intros f; simpl; f_equal.
  Qed.

  Lemma eq_unzip1:
    forall {T1 T2: eqType} (l1 l2: seq (T1 * T2)) x0,
      size l1 = size l2 ->
      (forall i, i < size l1 -> (fst (nth x0 l1 i)) = (fst (nth x0 l2 i))) ->
      unzip1 l1 = unzip1 l2.
  Proof.
    intros T1 T2.
    induction l1; simpl; first by destruct l2.
    intros l2 x0 SIZE ALL.
    destruct l2; first by done.
    simpl; f_equal; first by feed (ALL 0).
    case: SIZE => SIZE.
    apply IHl1 with (x0 := x0); first by done.
    intros i LTi.
    by feed (ALL i.+1);
      first by rewrite -[X in X < _]addn1 -[X in _ < X]addn1 ltn_add2r.
  Qed.

  Lemma eq_unzip2:
    forall {T1 T2: eqType} (l1 l2: seq (T1 * T2)) x0,
      size l1 = size l2 ->
      (forall i, i < size l1 -> (snd (nth x0 l1 i)) = (snd (nth x0 l2 i))) ->
      unzip2 l1 = unzip2 l2.
  Proof.
    intros T1 T2.
    induction l1; simpl; first by destruct l2.
    intros l2 x0 SIZE ALL.
    destruct l2; first by done.
    simpl; f_equal; first by feed (ALL 0).
    case: SIZE => SIZE.
    apply IHl1 with (x0 := x0); first by done.
    intros i LTi.
    by feed (ALL i.+1);
      first by rewrite -[X in X < _]addn1 -[X in _ < X]addn1 ltn_add2r.
  Qed.

End Zip.

(* Restate nth_error function from Coq library. *)
Fixpoint nth_or_none {T: Type} (l: seq T) (n:nat) {struct n} : option T :=
  match n, l with
  | 0, x :: _ => Some x
  | n.+1, _ :: l => nth_or_none l n
  | _, _ => None
end.

(* Lemmas about nth. *)
Section Nth.

  Context {T: eqType}.

  Lemma nth_in_or_default:
    forall (l: seq T) x0 i,
      (nth x0 l i) \in l \/ (nth x0 l i) = x0.
  Proof.
    intros l x0 i.
    generalize dependent i.
    induction l;
      first by right; destruct i.
    destruct i; simpl in *;
      first by left; rewrite in_cons eq_refl.
    by destruct (IHl i) as [IN | DEF];
      [by left; rewrite in_cons IN orbT | by rewrite DEF; right].
  Qed.

  Lemma nth_neq_default :
    forall (l: seq T) x0 i y,
      nth x0 l i = y ->
      y <> x0 ->
      y \in l.
  Proof.
    intros l x0 i y NTH NEQ.
    by destruct (nth_in_or_default l x0 i) as [IN | DEF];
      [by rewrite -NTH | by rewrite -NTH DEF in NEQ].
  Qed.

  Lemma nth_or_none_mem :
    forall (l: seq T) n x, nth_or_none l n = Some x -> x \in l.
  Proof.
    induction l; first by unfold nth_or_none; ins; destruct n; ins.
    {
      ins; destruct n.
      {
        inversion H; subst.
        by rewrite in_cons eq_refl orTb.
      }
      simpl in H; rewrite in_cons; apply/orP; right.
      by apply IHl with (n := n).
    }
  Qed. 
    
  Lemma nth_or_none_mem_exists :
    forall (l: seq T) x, x \in l -> exists n, nth_or_none l n = Some x.
  Proof.
    induction l; first by intros x IN; rewrite in_nil in IN.
    {
      intros x IN; rewrite in_cons in IN.
      move: IN => /orP [/eqP EQ | IN]; first by subst; exists 0.
      specialize (IHl x IN); des.
      by exists n.+1.
    }
  Qed.
  
  Lemma nth_or_none_size_none :
    forall (l: seq T) n,
      nth_or_none l n = None <-> n >= size l.
  Proof.
    induction l; first by split; destruct n. 
    by destruct n; simpl; [by split; last by rewrite ltn0 | by rewrite ltnS].
  Qed.

  Lemma nth_or_none_size_some :
    forall (l: seq T) n x,
      nth_or_none l n = Some x -> n < size l.
  Proof.
    induction l; first by destruct n. 
    by intros n x; destruct n; simpl; last by rewrite ltnS; apply IHl.
  Qed.
  
  Lemma nth_or_none_uniq :
    forall (l: seq T) i j x,
      uniq l ->
      nth_or_none l i = Some x ->
      nth_or_none l j = Some x ->
      i = j.
  Proof.
    intros l i j x UNIQ SOMEi SOMEj.
    {
      generalize dependent j.
      generalize dependent i.
      induction l;
        first by ins; destruct i, j; simpl in *; inversion SOMEi.
      intros i SOMEi j SOMEj.
      simpl in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
      feed IHl; first by done.
      destruct i, j; simpl in *; first by done.
      - by inversion SOMEi; subst; apply nth_or_none_mem in SOMEj; rewrite SOMEj in NOTIN. 
      - by inversion SOMEj; subst; apply nth_or_none_mem in SOMEi; rewrite SOMEi in NOTIN.
      - by f_equal; apply IHl.
    }
  Qed.

  Lemma nth_or_none_nth :
    forall (l: seq T) n x x0,
      nth_or_none l n = Some x ->
      nth x0 l n = x.
  Proof.
    induction l; first by destruct n.
    by intros n x x0 SOME; destruct n; simpl in *; [by inversion SOME | by apply IHl].
  Qed.

End Nth.

Section PartialMap.

  Lemma pmap_inj_in_uniq {T T': eqType} (s: seq T) (f: T -> option T') :
    {in s &, ssrfun.injective f} ->
    uniq s ->
    uniq (pmap f s).
  Proof.
    intros INJ UNIQ; red in INJ.
    induction s; first by done.
    simpl in *; unfold ssrfun.Option.apply.
    move: UNIQ => /andP [NOTIN UNIQ].
    feed IHs.
      by ins; apply INJ; try (by rewrite in_cons; apply/orP; right).
    specialize (IHs UNIQ).
    destruct (f a) eqn:F; simpl; last by done.
    rewrite IHs andbT mem_pmap -F.
    apply/mapP; move => [a' IN' EQ].
    exploit (INJ a a'); try (by done).
      by rewrite in_cons; apply/orP; left.
      by rewrite in_cons; apply/orP; right.
    by intros EQ'; subst; rewrite IN' in NOTIN.
  Qed.
  
  Lemma pmap_inj_uniq {T T': eqType} (s: seq T) (f: T -> option T') :
    ssrfun.injective f ->
    uniq s ->
    uniq (pmap f s).
  Proof.
    intros INJ UNIQ.
    apply pmap_inj_in_uniq; last by done.
    by red; ins; apply INJ.
  Qed.
  
End PartialMap.

(* Define a set_nth that does not grow the vector. *)
Program Definition set_nth_if_exists {T: Type} (l: seq T) n y :=
  if n < size l then
    set_nth _ l n y
  else l.

(* Define a function that replaces the first element that satisfies
   some predicate with using a mapping function f. *)
Fixpoint replace_first {T: Type} P f (l: seq T) :=
  if l is x0 :: l' then
    if P x0 then
      f x0 :: l'
    else x0 :: replace_first P f l'
  else [::].

(* Define a function that replaces the first element that satisfies
   some predicate with a constant. *)
Definition replace_first_const {T: Type} P y (l: seq T) :=
  replace_first P (fun x => y) l.

Definition set_pair_1nd {T1: Type} {T2: Type} (y: T2) (p: T1 * T2) :=
  (fst p, y).

Definition set_pair_2nd {T1: Type} {T2: Type} (y: T2) (p: T1 * T2) :=
  (fst p, y).
      
Section Replace.

  Context {T: eqType}.
  
  Lemma replace_first_size P f (l: seq T) :
    size (replace_first P f l) = size l.
  Proof.
    induction l; simpl; first by done.
    by destruct (P a); rewrite // /= IHl.
  Qed.

  Lemma replace_first_cases {P} {f} {l: seq T} {x}:
    x \in replace_first P f l ->
    x \in l \/ (exists y, x = f y /\ P y /\ y \in l).
  Proof.
    intros IN.
    induction l; simpl in *; first by rewrite IN; left.
    destruct (P a) eqn:HOLDS.
    {
      rewrite in_cons in IN; des;
        last by left; rewrite in_cons IN orbT.
      right; exists a; split; first by done.
      by split; last by rewrite in_cons eq_refl orTb.
    }
    {
      rewrite in_cons in IN; des;
        first by left; rewrite in_cons IN eq_refl orTb.
      specialize (IHl IN); des;
        first by left; rewrite in_cons IHl orbT.
      right; exists y; split; first by done.
      by split; last by rewrite in_cons IHl1 orbT.
    }
  Qed.

  Lemma replace_first_no_change {P} {f} {l: seq T} {x}:
    x \in l ->
    ~~ P x ->
    x \in replace_first P f l.
  Proof.
    intros IN NOT.
    induction l; simpl in *; first by rewrite in_nil in IN.
    destruct (P a) eqn:HOLDS.
    {
      rewrite in_cons in IN; des; last by rewrite in_cons IN orbT.
      by rewrite IN HOLDS in NOT.
    }
    {
      rewrite in_cons in IN; des; first by rewrite IN in_cons eq_refl orTb.
      by rewrite in_cons; apply/orP; right; apply IHl.
    }
  Qed.
  
  Lemma replace_first_idempotent {P} {f} {l: seq T} {x}:
    x \in l ->
    f x = x ->
    x \in replace_first P f l.
  Proof.
    intros IN IDEMP.
    induction l; simpl in *; first by rewrite in_nil in IN.
    destruct (P a) eqn:HOLDS.
    {
      rewrite in_cons in IN; des; last by rewrite in_cons IN orbT.
      by rewrite -IN -{1}IDEMP; rewrite in_cons eq_refl orTb.

    }
    {
      rewrite in_cons in IN; des; first by rewrite IN in_cons eq_refl orTb.
      by rewrite in_cons; apply/orP; right; apply IHl.
    }
  Qed.
  
  Lemma replace_first_new :
    forall P f (l: seq T) x1 x2,
    x1 \notin l ->
    x2 \notin l ->
    x1 \in replace_first P f l ->
    x2 \in replace_first P f l ->
    x1 = x2.
  Proof.
    intros P f l x1 x2 NOT1 NOT2 IN1 IN2.
    induction l; simpl in *; first by rewrite in_nil in IN1.
    {
      destruct (P a) eqn:HOLDS.
      {
        rewrite 2!in_cons in IN1 IN2.
        rewrite 2!in_cons 2!negb_or in NOT1 NOT2.
        move: NOT1 NOT2 => /andP [NEQ1 NOT1] /andP [NEQ2 NOT2].
        move: IN1 => /orP [/eqP F1 | IN1]; last by rewrite IN1 in NOT1.
        move: IN2 => /orP [/eqP F2 | IN2]; last by rewrite IN2 in NOT2.
        by rewrite F1 F2.
      }
      {
        rewrite 2!in_cons in IN1 IN2.
        rewrite 2!in_cons 2!negb_or in NOT1 NOT2.
        move: NOT1 NOT2 => /andP [NEQ1 NOT1] /andP [NEQ2 NOT2].
        move: IN1 => /orP [/eqP A1 | IN1]; first by rewrite A1 eq_refl in NEQ1.
        move: IN2 => /orP [/eqP A2 | IN2]; first by rewrite A2 eq_refl in NEQ2.
        by apply IHl.
      }
    }
  Qed.

  Lemma replace_first_previous P f {l: seq T} {x}:
    x \in l ->
      (x \in replace_first P f l) \/
      (P x /\ f x \in replace_first P f l).
  Proof.
    intros IN; induction l; simpl in *; first by rewrite in_nil in IN.
    destruct (P a) eqn:HOLDS.
    {
      rewrite in_cons in IN; des; subst.
      {
        right; rewrite HOLDS; split; first by done.
        by rewrite in_cons; apply/orP; left.
      }
      by rewrite in_cons IN; left; apply/orP; right.
    }
    {
      rewrite in_cons in IN; des; subst;
        first by left; rewrite in_cons eq_refl orTb.
      specialize (IHl IN); des;
        first by left; rewrite in_cons IHl orbT.
      right; rewrite IHl; split; first by done.
      by rewrite in_cons IHl0 orbT.
    }
  Qed.

  Lemma replace_first_failed P f {l: seq T}:
    (forall x, x \in l -> f x \notin replace_first P f l) ->
    (forall x, x \in l -> ~~ P x).
  Proof.
    intros NOTIN.
    induction l as [| a l']; simpl in *;
      first by intros x IN; rewrite in_nil in IN.
    intros x IN.
    destruct (P a) eqn:HOLDS.
    {
      exploit (NOTIN a); first by rewrite in_cons eq_refl orTb.
      by rewrite in_cons eq_refl orTb.
    }
    {
      rewrite in_cons in IN; move: IN => /orP [/eqP EQ | IN];
        first by subst; rewrite HOLDS.
      apply IHl'; last by done.
      intros y INy.
      exploit (NOTIN y); first by rewrite in_cons INy orbT.
      intros NOTINy.
      rewrite in_cons negb_or in NOTINy.
      by move: NOTINy => /andP [_ NOTINy].
    }
  Qed.
  
End Replace.

Definition pairs_to_function {T1: eqType} {T2: Type} y0 (l: seq (T1*T2)) :=
  fun x => nth y0 (unzip2 l) (index x (unzip1 l)).

Section Pairs.

  Lemma pairs_to_function_neq_default {T1: eqType} {T2: eqType} y0 (l: seq (T1*T2)) x y :
    pairs_to_function y0 l x = y ->
    y <> y0 ->
    (x,y) \in l.
  Proof.
    unfold pairs_to_function, unzip1, unzip2; intros PAIR NEQ.
    induction l; simpl in *; first by subst.
    destruct (fst a == x) eqn:FST; simpl in *.
    {
      move: FST => /eqP FST; subst.
      by rewrite in_cons; apply/orP; left; destruct a.
    }
    {
      by specialize (IHl PAIR); rewrite in_cons; apply/orP; right.
    }
  Qed.

  Lemma pairs_to_function_mem {T1: eqType} {T2: eqType} y0 (l: seq (T1*T2)) x y :
    uniq (unzip1 l) ->
    (x,y) \in l ->
    pairs_to_function y0 l x = y.
  Proof.
    unfold pairs_to_function, unzip1, unzip2; intros UNIQ IN.
    induction l as [| [x' y'] l']; simpl in *; first by rewrite in_nil in IN.
    {
      move: UNIQ => /andP [NOTIN UNIQ]; specialize (IHl' UNIQ).
      destruct (x' == x) eqn:FST; simpl in *.
      {
        move: FST => /eqP FST; subst.
        rewrite in_cons /= in IN.
        move: IN => /orP [/eqP EQ | IN];
          first by case: EQ => ->.
        exfalso; move: NOTIN => /negP NOTIN; apply NOTIN.
        by apply/mapP; exists (x,y).
      }
      {
        rewrite in_cons /= in IN.
        move: IN => /orP [/eqP EQ | IN];
          first by case: EQ => EQ1 EQ2; subst; rewrite eq_refl in FST.
        by apply IHl'.
      }
    }
  Qed.
    
End Pairs.

Section Order.

  Context {T: eqType}.
  Variable rel: T -> T -> bool.
  Variable l: seq T.
  
  Definition total_over_list :=
    forall x1 x2,
      x1 \in l ->
      x2 \in l ->
      (rel x1 x2 \/ rel x2 x1).
      
  Definition antisymmetric_over_list :=
    forall x1 x2,
      x1 \in l ->
      x2 \in l ->
      rel x1 x2 ->
      rel x2 x1 ->
      x1 = x2.

End Order.

(* In this section we prove some additional lemmas about sequences. *)
Section AdditionalLemmas.

  (* First, we prove that x ∈ xs implies that xs can be split 
     into two parts such that xs = xsl ++ [::x] ++ xsr. *)
  Lemma in_cat:
    forall {X : eqType} (x : X) (xs : list X),
      x \in xs -> exists xsl xsr, xs = xsl ++ [::x] ++ xsr.
  Proof.
    intros ? ? ? SUB.
    induction xs; first by done.
    move: SUB; rewrite in_cons; move => /orP [/eqP EQ|IN].
    - by subst; exists [::], xs.
    - feed IHxs; first by done.
      clear IN; move: IHxs => [xsl [xsr EQ]].
        by subst; exists (a::xsl), xsr.
  Qed.
  

  (* We define a local function max over lists using foldl and maxn. *)
  Let max := foldl maxn 0.
  
  (* We prove that max {x, xs} is equal to max {x, max xs}. *)
  Lemma seq_max_cons: forall x xs, max (x :: xs) = maxn x (max xs).
  Proof.
    have L: forall s x xs, foldl maxn s (x::xs) = maxn x (foldl maxn s xs).
    { clear; intros. 
      generalize dependent s; generalize dependent x.
      induction xs.
      { by intros; rewrite maxnC. }
      { intros; simpl in *.
          by rewrite maxnC IHxs [maxn s a]maxnC IHxs maxnA [maxn s x]maxnC.
      }
    }
      by intros; unfold max; apply L.
  Qed.

  (* We prove that for any two sequences xs and ys the fact that xs is a subsequence 
     of ys implies that the size of xs is at most the size of ys. *)
  Lemma subseq_leq_size:
    forall {X : eqType} (xs ys: seq X),
      uniq xs ->
      (forall x, x \in xs -> x \in ys) ->
      size xs <= size ys.
  Proof.
    clear; intros ? ? ? UNIQ SUB.
    have EXm: exists m, size ys <= m; first by exists (size ys).
    move: EXm => [m SIZEm].
    move: SIZEm UNIQ SUB; move: xs ys.
    induction m; intros.
    { move: SIZEm; rewrite leqn0 size_eq0; move => /eqP SIZEm; subst ys.
      destruct xs; first by done.
      specialize (SUB s).
        by feed SUB; [rewrite in_cons; apply/orP; left | done]. 
    }
    { destruct xs as [ | x xs]; first by done.
      move: (@in_cat _ x ys) => Lem.
      feed Lem; first by apply SUB; rewrite in_cons; apply/orP; left.
      move: Lem => [ysl [ysr EQ]]; subst ys.
      rewrite !size_cat; simpl; rewrite -addnC add1n addSn ltnS -size_cat.
      eapply IHm.
      - move: SIZEm; rewrite !size_cat; simpl; move => SIZE.
          by rewrite add1n addnS ltnS addnC in SIZE.
      - by move: UNIQ; rewrite cons_uniq; move => /andP [_ UNIQ].
      - intros a IN.
        destruct (a == x) eqn: EQ.
        { exfalso.
          move: EQ UNIQ; rewrite cons_uniq; move => /eqP EQ /andP [NIN UNIQ].
            by subst; move: NIN => /negP NIN; apply: NIN.
        }
        { specialize (SUB a).
          feed SUB; first by rewrite in_cons; apply/orP; right.
          clear IN; move: SUB; rewrite !mem_cat; move => /orP [IN| /orP [IN|IN]].
          - by apply/orP; right.
          - exfalso.
              by  move: IN; rewrite in_cons; move => /orP [IN|IN]; [rewrite IN in EQ | ].
          - by apply/orP; left.
        }
    }
  Qed.

End AdditionalLemmas.