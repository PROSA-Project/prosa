Require Export prosa.implementation.definitions.task.
Require Export prosa.implementation.facts.extrapolated_arrival_curve.
Require Export NArith.
From CoqEAL Require Export hrel param refinements binnat.
Export Refinements.Op.

(** * Refinements Library *)

(** This file contains a variety of support definitions and proofs for
    refinements. Refinements allow to convert unary-number definitions into
    binary-number ones. This is used for the sole purpose of performing
    computations involving large numbers, and can safely be ignored if this is
    of no interest to the reader. See Maida et al. (ECRTS 2022) for the
    motivation and further details, available at
    <<https://drops.dagstuhl.de/opus/volltexte/2022/16336/>>. *)

(** ** Brief Introduction *)

(** Consider the refinement [refines (Rnat ==> Rnat ==> Rnat)%rel maxn maxn_T.]
    This statements uses the relation [Rnat], which relates each unary number
    with its binary counterpart.

    Proving this statement shows that the [maxn] function is isomorphic to
    [maxn_T], i.e., given two unary numbers [(a,b)] and two binary numbers [(a',
    b')], [Rnat a b -> Rnat a' b' -> Rnat (maxn a b) (maxn_T a' b')].  In other
    words, if [a] is related to [a'] and [b] to [b'], then [maxn a b] is related
    to [maxn_T a' b')].  This statement is encoded in a succinct way via the [==>]
    notation.

    For more information, refer to
    <<https://hal.inria.fr/hal-01113453/document>>. *)

(** ** Auxiliary Definitions *)

(** First, we define a convenience function that translates a list of unary
    natural numbers to binary numbers... *)
Definition m_b2n b := map nat_of_bin b.
Definition m_n2b n := map bin_of_nat n.

(** ... and an analogous version that works on pairs. *)
Definition tmap {X Y : Type} (f : X -> Y) (t : X * X) := (f (fst t), f (snd t)).
Definition tb2tn t := tmap nat_of_bin t.
Definition tn2tb t := tmap bin_of_nat t.
Definition m_tb2tn xs := map tb2tn xs.
Definition m_tn2tb xs := map tn2tb xs.

(** * Basic Arithmetic *)

(** In the following, we encode refinements for a variety of basic arithmetic
    functions. *)

(** ** Definitions *)

(** We begin by defining a generic version of the functions we seek to
    refine. *)
Section Definitions.
    (** Consider a generic type T supporting basic arithmetic operations,
        neutral elements, and comparisons. *)
  Context {T : Type}.
  Context `{!zero_of T, !one_of T, !sub_of T, !add_of T, !mul_of T,
      !div_of T, !mod_of T, !eq_of T, !leq_of T, !lt_of T}.

    (** We redefine the predecessor function. Note that, although this
        definition uses common notation, the [%C] indicates that we
        refer to the generic type [T] defined above. *)
  Definition predn_T (n : T) := (n - 1)%C.

  (** Further, we redefine the maximum and minimum functions... *)
  Definition maxn_T (m n : T) := (if m < n then n else m)%C.
  Definition minn_T (m n : T) := (if m < n then m else n)%C.

  (** ... the "divides" function... *)
  Definition dvdn_T (d : T) (m : T) := (m %% d == 0)%C.

  (** ... and the division with ceiling function. *)
  Definition div_ceil_T (a : T) (b : T) :=
    if dvdn_T b a then (a %/ b)%C else (1 + a %/ b)%C.

End Definitions.

(** ** Refinements *)

(** We now establish the desired refinements. *)

(** First, we prove a refinement for the [b2n] function. *)
Global Instance refine_b2n :
  refines (unify (A:=N) ==> Rnat)%rel nat_of_bin id.
Proof.
  apply refines_abstr; move => n n' Rn.
  compute in Rn; destruct refines_key in Rn; subst.
  by apply trivial_refines.
Qed.

(** Second, we prove a refinement for the predecessor function. *)
Global Instance Rnat_pred :
  refines (Rnat ==> Rnat)%rel predn predn_T.
Proof.
  rewrite !refinesE => a a' Ra.
  rewrite -subn1 /predn_T.
  by apply: refinesP.
Qed.

(** Next, we prove a refinement for the "divides" function. *)
Global Instance refine_dvdn :
  refines (Rnat ==> Rnat ==> bool_R)%rel dvdn dvdn_T.
Proof.
  apply refines_abstr2; unfold "%|", dvdn_T; move=> x x' rx y y' ry.
  by exact: refines_apply.
Qed.

(** Next, we prove a refinement for the division with ceiling. *)
Global Instance refine_div_ceil :
  refines (Rnat ==> Rnat ==> Rnat)%rel div_ceil div_ceil_T.
Proof.
  apply refines_abstr2; unfold div_ceil, div_ceil_T.
  move => x x' Rx y y' Ry.
  have <-: y %| x = dvdn_T y' x'.
  { eapply refines_eq.
    apply refines_bool_eq; unfold "%|", dvdn_T.
    by refines_apply. }
  destruct (y %| x) eqn:B.
  { eapply refines_apply.
    refines_abstr.
    by exact Ry. }
  { eapply refines_apply.
    refines_abstr.
    eapply refines_apply.
    refines_abstr.
    by exact Ry. }
Qed.

(** Next, we prove a refinement for the minimum function. *)
Global Instance refine_minn :
  refines (Rnat ==> Rnat ==> Rnat)%rel minn minn_T.
Proof.
  intros *; rewrite refinesE => a a' Ra b b' Rb; unfold minn, minn_T.
  compute in Ra, Rb; subst.
  rename a' into a, b' into b.
  have <- : (a < b) = (a < b)%C; last by destruct (a < b).
  unfold lt_op, lt_N.
  destruct (a < b) eqn:EQ; symmetry; first by apply N.ltb_lt; apply /Rnat_ltP.
  apply N.ltb_ge.
  apply negbT in EQ; rewrite -leqNgt in EQ.
  apply /N.leb_spec0.
  by move: Rnat_leE => LE; unfold leq_op, leq_N in LE; rewrite LE.
Qed.

(** Finally, we prove a refinement for the maximum function. *)
Global Instance refine_maxn :
  refines (Rnat ==> Rnat ==> Rnat)%rel maxn maxn_T.
Proof.
  intros *; rewrite refinesE => a a' Ra b b' Rb; unfold maxn, maxn_T.
  compute in Ra, Rb; subst.
  rename a' into a, b' into b.
  have <- : (a < b) = (a < b)%C; last by destruct (a < b).
  unfold lt_op, lt_N.
  destruct (a < b) eqn:EQ; symmetry; first by apply N.ltb_lt; apply /Rnat_ltP.
  apply N.ltb_ge.
  apply negbT in EQ; rewrite -leqNgt in EQ.
  apply /N.leb_spec0.
  by move: Rnat_leE => LE; unfold leq_op, leq_N in LE; rewrite LE.
Qed.

(** ** Supporting Lemmas  *)

(** As the next step, we prove some helper lemmas used in refinements. We
    differentiate class instances from lemmas, as lemmas are applied manually,
    and not via the typeclass engine. *)

(** First, we prove that negating a positive, binary number results in [0]. *)
Lemma posBinNatNotZero:
  forall p, ~ (nat_of_bin (N.pos p)) = O.
Proof.
  rewrite -[0]bin_of_natK.
  intros p EQ.
  have BJ := @Bijective _ _ nat_of_bin bin_of_nat.
  feed_n 2 BJ.
  { by intros ?; rewrite bin_of_natE; apply nat_of_binK. }
  { by apply bin_of_natK. }
  apply bij_inj in BJ; apply BJ in EQ; clear BJ.
  by destruct p.
Qed.

(** Next, we prove that, if the successor of a unary number [b] corresponds to a
    positive binary number [p], then [b] corresponds to the predecessor of
    [p]. *)
Lemma eq_SnPos_to_nPred:
  forall b p, Rnat b.+1 (N.pos p) -> Rnat b (Pos.pred_N p).
Proof.
  move => b p.
  rewrite /Rnat /fun_hrel => EQ.
  rewrite -addn1 in EQ.
  apply /eqP; rewrite -(eqn_add2r 1) -EQ; apply /eqP.
  move: (nat_of_add_bin (Pos.pred_N p) 1%N) => EQadd1.
  by rewrite -EQadd1 N.add_1_r N.succ_pos_pred.
Qed.

(** Finally, we prove that if two unary numbers [a] and [b] have the same
    numeral as, respectively, two binary numbers [a'] and [b'], then [a<b] is
    rewritable into [a'<b']. *)
Lemma refine_ltn :
  forall a a' b b',
    Rnat a a' ->
    Rnat b b' ->
    bool_R (a < b) (a' < b')%C.
Proof.
  move=> a a' b b' Ra Rb.
  replace (@lt_op N lt_N a' b') with (@leq_op N leq_N (1 + a')%N b');
    first by apply refinesP; refines_apply.
  unfold leq_op, leq_N, lt_op, lt_N.
  apply /N.leb_spec0; case (a' <? b')%N eqn:LT.
  - by move: LT => /N.ltb_spec0 LT; rewrite N.add_1_l; apply N.le_succ_l.
  - rewrite N.add_1_l => CONTR; apply N.le_succ_l in CONTR.
    by move: LT => /negP LT; apply: LT; apply /N.ltb_spec0.
Qed.


(** * Functions on Lists *)

(** In the following, we encode refinements for a variety of functions related
    to lists. *)

(** ** Definitions *)

(** We begin by defining a generic version of the functions we want to
    refine. *)
Section Definitions.

  (** Consider a generic type T supporting basic arithmetic operations
        and comparisons *)
  Context {T : Type}.
  Context `{!zero_of T, !one_of T, !sub_of T, !add_of T, !mul_of T,
      !div_of T, !mod_of T, !eq_of T, !leq_of T, !lt_of T}.

  (** We redefine the [iota] function, ... *)
  Fixpoint iota_T (a : T) (b : nat): seq T :=
    match b with
    | 0 => [::]
    | S b' => a :: iota_T (a + 1)%C b'
    end.

  (** ... the size function, ... *)
  Fixpoint size_T {X : Type} (s : seq X): T :=
    match s with
    | [::] => 0%C
    | _ :: s' => (1 + size_T s')%C
    end.

  (** ... the forward-shift function, ... *)
  Definition shift_points_pos_T (xs : seq T) (s : T) : seq T :=
    map (fun x => s + x)%C xs.

  (** ... and the backwards-shift function. *)
  Definition shift_points_neg_T (xs : seq T) (s : T) : seq T :=
    let nonsmall := filter (fun x => s <= x)%C xs in
    map (fun x => x - s)%C nonsmall.

End Definitions.

(** ** Refinements *)

(** In the following, we establish the required refinements. *)

(** First, we prove a refinement for the [map] function. *)
Global Instance refine_map :
  forall {A A' B B': Type}
    (F : A -> B) (F' : A' -> B')
    (rA : A -> A' -> Type) (rB : B -> B' -> Type) xs xs',
    refines (list_R rA) xs xs' ->
    refines (rA ==> rB)%rel F F' ->
    refines (list_R rB)%rel (map F xs) (map F' xs').
Proof.
  intros * Rxs RF; rewrite refinesE.
  eapply map_R; last first.
  - by rewrite refinesE in Rxs; apply Rxs.
  - by intros x x' Rx; rewrite refinesE in RF; apply RF.
Qed.

(** Second, we prove a refinement for the [zip] function. *)
Global Instance refine_zip :
  refines (list_R Rnat ==> list_R Rnat ==> list_R (prod_R Rnat Rnat))%rel zip zip.
Proof. by rewrite refinesE => xs xs' Rxs ys ys' Rys; apply zip_R. Qed.

(** Next, we prove a refinement for the [all] function. *)
Global Instance refine_all :
  forall {A A' : Type} (rA : A -> A' -> Type),
    refines ((rA ==> bool_R) ==> list_R rA ==> bool_R)%rel all all.
Proof.
  intros.
  rewrite refinesE => P P' RP xs xs' Rxs.
  eapply all_R; last by apply Rxs.
  by intros x x' Rx; apply RP.
Qed.

(** Next, we prove a refinement for the [flatten] function. *)
Global Instance refine_flatten :
  forall {A A': Type} (rA : A -> A' -> Type),
    refines (list_R (list_R rA) ==> list_R rA)%rel flatten flatten.
Proof.
  by intros; rewrite refinesE => xss xss' Rxss; eapply flatten_R.
Qed.

(** Next, we prove a refinement for the [cons] function. *)
Global Instance refine_cons A C (rAC : A -> C -> Type) :
  refines (rAC ==> list_R rAC ==> list_R rAC)%rel cons cons.
Proof.
  by rewrite refinesE => h h' rh t t' rt; apply list_R_cons_R.
Qed.

(** Next, we prove a refinement for the [nil] function. *)
Global Instance refine_nil A C (rAC : A -> C -> Type) :
  refines (list_R rAC) nil nil.
Proof.
  by rewrite refinesE; apply list_R_nil_R.
Qed.

(** Next, we prove a refinement for the [last] function. *)
Global Instance refine_last :
  forall {A B : Type} (rA : A -> B -> Type),
    refines (rA ==> list_R rA ==> rA)%rel last last.
Proof.
  move=> A B rA; rewrite refinesE => d d' Rd xs xs' Rxs.
  elim: xs d d' Rd xs' Rxs => [|a xs IHxs] d d' Rd xs' Rxs.
  - by destruct xs'; last inversion Rxs.
  - case: xs' Rxs => [|b xs'] Rxs; first by inversion Rxs.
    exact: last_R.
Qed.

(** Next, we prove a refinement for the [size] function. *)
Global Instance refine_size A C (rAC : A -> C -> Type) :
  refines (list_R rAC ==> Rnat)%rel size size_T.
Proof.
  apply: refines_abstr => s s'; rewrite !refinesE.
  by elim=> [//|a a' Ra {}s {}s' Rs IHs] /=; apply: refinesP.
Qed.

(** Next, we prove a refinement for the [iota] function when applied
        to the successor of a number. *)
Lemma iotaTsuccN :
  forall (a : N) p,
    iota_T a (N.succ (Pos.pred_N p)) = a :: iota_T (succN a) (Pos.pred_N p).
Proof.
  move=> a p.
  destruct (N.succ (Pos.pred_N p)) as [|p0] eqn:EQ; first by move: (N.neq_succ_0 (Pos.pred_N p)).
  move: (posBinNatNotZero p0) => /eqP EQn0.
  destruct (nat_of_bin (N.pos p0)) as [|n] eqn:EQn; first by done.
  have -> : n = Pos.pred_N p; last by rewrite //= /succN /add_N /add_op N.add_comm.
  apply /eqP.
  rewrite -eqSS -EQn -EQ -addn1.
  move: (nat_of_add_bin (Pos.pred_N p) 1%N) => EQadd1; rewrite -EQadd1.
  by rewrite N.add_1_r.
Qed.

(** Next, we prove a refinement for the [iota] function. *)
Global Instance refine_iota :
  refines (Rnat ==> Rnat ==> list_R Rnat)%rel iota iota_T.
Proof.
  rewrite refinesE => a a' Ra b; move: a a' Ra; elim: b => [|b IHb] a a' Ra b' Rb.
  { destruct b'; first  by rewrite //=; apply list_R_nil_R.
    by compute in Rb; apply posBinNatNotZero in Rb. }
  { destruct b'; first  by compute in Rb; destruct b.
    have Rsa := Rnat_S.
    rewrite refinesE in Rsa; specialize (Rsa a a' Ra).
    specialize (IHb _ _ Rsa).
    rewrite //= -N.succ_pos_pred iotaTsuccN.
    apply list_R_cons_R; first by done.
    apply IHb; clear Rsa Ra IHb.
    by apply eq_SnPos_to_nPred. }
Qed.

(** Next, we prove a refinement for the [shift_points_pos] function. *)
Global Instance refine_shift_points_pos:
  refines (list_R Rnat ==> Rnat ==> list_R Rnat)%rel shift_points_pos shift_points_pos_T.
Proof.
  rewrite refinesE => xs xs' Rxs s s' Rs.
  unfold shift_points_pos, shift_points_pos_T.
  apply refinesP; eapply refine_map; first by rewrite refinesE; apply Rxs.
  rewrite refinesE => ? ? ?.
  by apply refinesP; tc.
Qed.

(** Next, we prove a refinement for the [shift_points_neg] function. *)
Global Instance refine_shift_points_neg:
  refines (list_R Rnat ==> Rnat ==> list_R Rnat)%rel shift_points_neg shift_points_neg_T.
Proof.
  rewrite refinesE => xs xs' Rxs s s' Rs.
  unfold shift_points_neg, shift_points_neg_T.
  apply refinesP; eapply refine_map.
  - rewrite refinesE; eapply filter_R; last by eassumption.
    by intros; apply refinesP; refines_apply.
  - rewrite refinesE => x x' Rx.
    by apply refinesP; refines_apply.
Qed.

(** Finally, we prove that the if the [nat_of_bin] function is applied to a
    list, the result is the original list translated to binary. *)
Global Instance refine_abstract :
  forall xs,
    refines (list_R Rnat)%rel (map nat_of_bin xs) xs | 0.
Proof.
  elim=> [|a xs IHxs]; first by rewrite refinesE; simpl; apply list_R_nil_R.
  rewrite //= refinesE; rewrite refinesE in IHxs.
  by apply list_R_cons_R; last by done.
Qed.

(** ** Supporting Lemmas  *)

(** As the last step, we prove some helper lemmas used in refinements.  Again,
    we differentiate class instances from lemmas, as lemmas are applied
    manually, not via the typeclass engine. *)

(** First, we prove a refinement for the [foldr] function. *)
Lemma refine_foldr_lemma :
  refines ((Rnat ==> Rnat ==> Rnat) ==> Rnat ==> list_R Rnat ==> Rnat)%rel foldr foldr.
Proof.
  rewrite refinesE => f f' Rf d d' Rd; elim=> [|x xs IHxs] xs' Rxs.
  { by destruct xs' as [ | x' xs']; [ done | inversion Rxs ]. }
  { destruct xs' as [ | x' xs']; first by inversion Rxs.
    inversion Rxs; subst.
    by simpl; apply Rf; [ done | apply IHxs]. }
Qed.

Section GenericLists.

  (** Now, consider two types [T1] and [T2], and two lists of the respective
      type. *)
  Context {T1 T2 : Type}.
  Variable (xs : seq T1) (xs' : seq T2).

  (** We prove a refinement for the [foldr] function when applied to a [map] and
      [filter] operation.  *)
  Lemma refine_foldr:
    forall (R : T1 -> bool) (R' : T2 -> bool) (F : T1 -> nat) (F' : T2 -> N),
    forall (rT : T1 -> T2 -> Type),
      refines ( list_R rT )%rel xs xs' ->
      refines ( rT ==> Rnat )%rel F F' ->
      refines ( rT ==> bool_R )%rel R R' ->
      refines Rnat (\sum_(x <- xs | R x) F x) (foldr +%C 0%C [seq F' x' | x' <- xs' & R' x']).
  Proof.
    move=> R R' F F' rT Rxs Rf Rr.
    have ->: \sum_(x <- xs | R x) F x = foldr addn 0 [seq F x | x <- xs & R x].
    { by rewrite foldrE big_map big_filter. }
    refines_apply.
    Unshelve.
    - by rewrite refinesE=> b b' Rb z z' Rz l l' Rl; eapply foldr_R; eauto.
    - by rewrite refinesE => g g' Rg l l' Rl; eapply map_R; eauto.
    - by rewrite refinesE => p p' Rp l l' Rl; eapply filter_R; eauto.
  Qed.

  (** Next, we prove a refinement for the [foldr] function when applied to a
      [map] operation. *)
  Lemma refine_uncond_foldr :
    forall (F : T1 -> nat) (F' : T2 -> N),
    forall (rT : T1 -> T2 -> Type),
      refines ( list_R rT )%rel xs xs' ->
      refines ( rT ==> Rnat )%rel F F' ->
      refines Rnat (\sum_(x <- xs) F x) (foldr +%C 0%C [seq F' x' | x' <- xs']).
  Proof.
    move=> F F' rT Rxs Rf.
    have ->: \sum_(x <- xs) F x = foldr addn 0 [seq F x | x <- xs] by rewrite foldrE big_map.
    refines_apply.
    by apply refine_foldr_lemma.
  Qed.

  (** Next, we prove a refinement for the [foldr] function when applied to a
      [max] operation over a list. In terms, the list is the result of a [map]
      and [filter] operation.  *)
  Lemma refine_foldr_max :
    forall (R : T1 -> bool) (R' : T2 -> bool)
      (F : T1 -> nat) (F' : T2 -> N),
    forall (rT : T1 -> T2 -> Type),
      refines ( list_R rT )%rel xs xs' ->
      refines ( rT ==> Rnat )%rel F F' ->
      refines ( rT ==> bool_R )%rel R R' ->
      refines Rnat (\max_(x <- xs | R x) F x) (foldr maxn_T 0%C [seq F' x' | x' <- xs' & R' x']).
  Proof.
    move=> R R' F F' rT Rxs Rf Rr.
    have ->: \max_(x <- xs | R x) F x = foldr maxn 0 [seq F x | x <- xs & R x]
                                         by rewrite foldrE big_map big_filter.
    refines_apply.
    Unshelve.
    - by rewrite refinesE=> b b' Rb z z' Rz l l' Rl; eapply foldr_R; eauto.
    - by rewrite refinesE => g g' Rg l l' Rl; eapply map_R; eauto.
    - by rewrite refinesE => p p' Rp l l' Rl; eapply filter_R; eauto.
  Qed.

End GenericLists.
