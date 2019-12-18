Require Import prosa.util.ssromega prosa.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** We define a few simple operations on 
    lists. Namely first, last, and max. *)
Definition max0 := foldl maxn 0.
Definition first0 := head 0.
Definition last0 := last 0.

(** Additional lemmas about last0. *)
Section Last0.

  (** Let [xs] be a non-empty sequence and [x] be an arbitrary element,
     then we prove that [last0 (x::xs) = last0 xs]. *) 
  Lemma last0_cons:
    forall x xs,
      xs <> [::] -> 
      last0 (x::xs) = last0 xs.
  Proof.
    induction xs; first by done.
    intros ?; by unfold last0. 
  Qed.

  (** Similarly, let [xs_r] be a non-empty sequence and [xs_l] be an sequence,
     we prove that [last0 (xs_l ++ xs_r) = last0 xs_r]. *)
  Lemma last0_cat:
    forall xs_l xs_r,
      xs_r <> [::] ->
      last0 (xs_l ++ xs_r) = last0 xs_r.
  Proof.
    clear; induction xs_l; intros ? NEQ.
    - by done.
    - simpl; rewrite last0_cons.
      apply IHxs_l; by done.
      intros C; apply: NEQ.
        by destruct xs_l.
  Qed.
  
  (** We also prove that [last0 xs = xs [| size xs -1 |] ]. *)
  Lemma last0_nth:
    forall xs,
      last0 xs = nth 0 xs (size xs).-1.
  Proof. by intros; rewrite nth_last. Qed.
  
  (** We prove that for any non-empty sequence [xs] there is a sequence [xsh]
      such that [xsh ++ [::last0 x] = [xs]]. *)
  Lemma last0_ex_cat:
    forall x xs,
      xs <> [::] ->
      last0 xs = x ->
      exists xsh, xsh ++ [::x] = xs.
  Proof.
    clear; intros ? ? NEQ LAST.
    induction xs; first by done.
    destruct xs.
    - exists [::]; by compute in LAST; subst a.
    - feed_n 2 IHxs; try by done.
      destruct IHxs as [xsh EQ].
      exists (a::xsh).
        by simpl; rewrite EQ.
  Qed.
  
  (** We prove that if [x] is the last element of a sequence [xs] and
      [x] satisfies a predicate, then [x] remains the last element in
      the filtered sequence. *)
  Lemma last0_filter:
    forall x xs (P : nat -> bool),
      xs <> [::] ->
      last0 xs = x ->
      P x ->
      last0 [seq x <- xs | P x] = x.
  Proof.
    clear; intros ? ? ? NEQ LAST PX.
    destruct (last0_ex_cat x xs NEQ LAST) as [xsh EQ]; subst xs.
    rewrite filter_cat last0_cat.
    all:rewrite //= PX //=.
  Qed.
  
End Last0.

(** Additional lemmas about max0. *)
Section Max0.
  
  (** We prove that [max0 (x::xs)] is equal to [max {x, max0 xs}]. *)
  Lemma max0_cons: forall x xs, max0 (x :: xs) = maxn x (max0 xs).
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

  (** Next, we prove that if all the numbers of a seq [xs] are equal to
     a constant [k], then [max0 xs = k]. *)
  Lemma max0_of_uniform_set:
    forall k xs,
      size xs > 0 ->
      (forall x, x \in xs -> x = k) ->
      max0 xs = k.
  Proof.
    clear; intros ? ? SIZE ALL.
    induction xs; first by done.
    destruct xs. unfold max0; simpl; rewrite max0n; apply ALL. by rewrite in_cons; apply/orP; left.
    rewrite max0_cons.
    rewrite IHxs.
    - by rewrite [a]ALL; [ rewrite maxnn | rewrite in_cons; apply/orP; left].
    - by done.
    - intros; apply ALL.
      move: H; rewrite in_cons; move => /orP [/eqP EQ | IN].
      + by subst x; rewrite !in_cons; apply/orP; right; apply/orP; left.
      + by rewrite !in_cons; apply/orP; right; apply/orP; right.
  Qed.

  (** We prove that no element in a sequence [xs] is greater than [max0 xs]. *)
  Lemma in_max0_le:
    forall xs x, x \in xs -> x <= max0 xs.
  Proof.
    induction xs; first by intros ?.
    intros x; rewrite in_cons; move => /orP [/eqP EQ | IN]; subst.
    - by rewrite !max0_cons leq_maxl.
    - apply leq_trans with (max0 xs); first eauto.
      rewrite max0_cons.
        by apply leq_maxr.
  Qed.

  (** We prove that for a non-empty sequence [xs], [max0 xs ∈ xs]. *)
  Lemma max0_in_seq:
    forall xs,
      xs <> [::] ->
      max0 xs \in xs.
  Proof.
    clear; induction xs; first by done.
    intros _; destruct xs.
    - destruct a; simpl. by done. by rewrite /max0 //= max0n in_cons eq_refl.
    - rewrite max0_cons.
      move: (leq_total a (max0 (n::xs))) => /orP [LE|LE].
      + rewrite maxnE subnKC // in_cons; apply/orP; right. apply IHxs. by done.
      + rewrite maxnE. move: LE; rewrite -subn_eq0; move => /eqP EQ; rewrite EQ addn0.
          by rewrite in_cons; apply/orP; left.
  Qed.

  (** Next we prove that one can remove duplicating element from the
      head of a sequence. *)
  Lemma max0_2cons_eq:
    forall x xs, 
      max0 (x::x::xs) = max0 (x::xs).
  Proof.
    intros; rewrite !max0_cons.
      by rewrite maxnA maxnn. 
  Qed.

  (** We prove that one can remove the first element of a sequence if 
      it is not greater than the second element of this sequence. *)
  Lemma max0_2cons_le:
    forall x1 x2 xs,
      x1 <= x2 -> 
      max0 (x1::x2::xs) = max0 (x2::xs).
  Proof.
    intros; rewrite !max0_cons.
    rewrite maxnA.
    rewrite [maxn x1 x2]maxnE subnKC //.
  Qed.

  (** We prove that [max0] of a sequence [xs] 
      is equal to [max0] of sequence [xs] without 0s. *)
  Lemma max0_rem0:
    forall xs, 
      max0 ([seq x <- xs | 0 < x]) = max0 xs.
  Proof.
    induction xs; first by done.
    simpl; destruct a; simpl.
    - by rewrite max0_cons max0n.
    - by rewrite !max0_cons IHxs.
  Qed.
  
  (** Note that the last element is at most the max element. *)
  Lemma last_of_seq_le_max_of_seq:
    forall xs, last0 xs <= max0 xs.
  Proof.
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
    destruct xs as [ | x2 xs]. by rewrite /max leq_max; apply/orP; right.
    have F1: last0 [:: x1, x2 & xs] = last0 [:: x2 & xs] by done. 
    rewrite F1 max0_cons; clear F1.
    rewrite leq_max; apply/orP; right.
    apply IHlen.
    move: EQ => /eqP; simpl; rewrite eqSS; move => /eqP EQ.
      by subst.
  Qed.

  (** Let's introduce the notion of the nth element of a sequence. *)
  Notation "xs [| n |]" := (nth 0 xs n) (at level 30).
  
  (** If any element of a sequence [xs] is less-than-or-equal-to
      the corresponding element of a sequence [ys], then max of 
      [xs] is less-than-or-equal-to max of [ys]. *)
  Lemma max_of_dominating_seq:
    forall (xs ys : seq nat),
      (forall n, xs[|n|] <= ys[|n|]) ->
      max0 xs <= max0 ys.
  Proof.
    intros xs ys.
    have EX: exists len, size xs <= len /\ size ys <= len.
    { exists (maxn (size xs) (size ys)).
        by split; rewrite leq_max; apply/orP; [left | right].
    }
    move: EX => [len [LE1 LE2]].
    generalize dependent xs; generalize dependent ys.
    induction len; intros.
    { by move: LE1 LE2; rewrite !leqn0 !size_eq0; move => /eqP E1 /eqP E2; subst. }
    { destruct xs, ys; try done.
      { have L: forall xs, (forall n, xs [| n |] = 0) -> max0 xs = 0.
        { clear; intros.
          induction xs; first by done.
          rewrite max0_cons.
          apply/eqP; rewrite eqn_leq; apply/andP; split; last by done.
          rewrite geq_max; apply/andP; split.
          - by specialize (H 0); simpl in H; rewrite H.
          - rewrite leqn0; apply/eqP; apply: IHxs. 
              by intros; specialize (H n.+1); simpl in H.
        }
        rewrite L; first by done. 
        intros; specialize (H n0).
          by destruct n0; simpl in *; apply/eqP; rewrite -leqn0.
      }
      { rewrite !max0_cons.
        rewrite geq_max; apply/andP; split.
        + rewrite leq_max; apply/orP; left.
            by specialize (H 0); simpl in H.
        + rewrite leq_max; apply/orP; right.
          apply IHlen; try (by rewrite ltnS in LE1, LE2).
            by intros; specialize (H n1.+1); simpl in H.
      }
    }
  Qed.

End Max0.

(* Additional lemmas about rem for lists. *)
Section RemList.
  
  (* We prove that if [x] lies in [xs] excluding [y], then [x] also lies in [xs]. *)
  Lemma rem_in:
    forall (T: eqType) (x y: T) (xs: seq T),
      x \in rem y xs -> x \in xs.
  Proof.
    clear; intros.
    induction xs; simpl in H.
    { by rewrite in_nil in H. }
    { rewrite in_cons; apply/orP.
      destruct (a == y) eqn:EQ. 
      { by move: EQ => /eqP EQ; subst a; right. }
      { move: H; rewrite in_cons; move => /orP [/eqP H | H].
        - by subst a; left.
        - by right; apply IHxs.
      }
    }
  Qed.

  (* We prove that if we remove an element [x] for which [P x] from 
     a filter, then the size of the filter decreases by [1]. *)
  Lemma filter_size_rem: 
    forall (T: eqType) (x:T) (xs: seq T) (P: T -> bool), 
      (x \in xs) ->
      P x ->
      size [seq y <- xs | P y] = size [seq y <- rem x xs | P y] + 1.
  Proof.
    clear; intros.
    induction xs; first by inversion H.
    move: H; rewrite in_cons; move => /orP [/eqP H | H]; subst.
    { by simpl; rewrite H0 -[X in X = _]addn1 eq_refl. }
    { specialize (IHxs H); simpl in *. 
      case EQab: (a == x); simpl.
      { move: EQab => /eqP EQab; subst.
          by rewrite H0 addn1. }
      { case Pa: (P a); simpl.
        - by rewrite IHxs !addn1.
        - by rewrite IHxs.
      }
    }
  Qed.

End RemList.

(* Additional lemmas about sequences. *)
Section AdditionalLemmas.

  (* First, we show that if [n > 0], then [nth (x::xs) n = nth xs (n-1)]. *)
  Lemma nth0_cons:
    forall x xs n,
      n > 0 ->
      nth 0 (x :: xs) n = nth 0 xs n.-1.
  Proof. by intros; destruct n. Qed.

  (* We prove that a sequence [xs] of size [n.+1] can be destructed
     into a sequence [xs_l] of size [n] and an element [x] such that
     [x = xs ++ [::x]]. *)
  Lemma seq_elim_last:
    forall {X : Type} (n : nat) (xs : seq X),
      size xs = n.+1 ->
      exists x xs__c, xs = xs__c ++ [:: x] /\ size xs__c = n.
  Proof.
    intros ? ? ? SIZE.
    revert xs SIZE; induction n; intros.
    - destruct xs; first by done.
      destruct xs; last by done.
      exists x, [::]; split; by done.
    - destruct xs; first by done.
      specialize (IHn xs).
      feed IHn; first by simpl in SIZE; apply eq_add_S in SIZE. 
      destruct IHn as [x__n [xs__n [EQ__n SIZE__n]]].
      subst xs.
      exists x__n, (x :: xs__n); split; first by done.
      simpl in SIZE; apply eq_add_S in SIZE.
      rewrite size_cat in SIZE; simpl in SIZE; rewrite addn1 in SIZE; apply eq_add_S in SIZE.
        by apply eq_S.
  Qed.
  
  (* Next, we prove that [x ∈ xs] implies that [xs] can be split 
     into two parts such that [xs = xsl ++ [::x] ++ [xsr]]. *)
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

  (* We prove that for any two sequences [xs] and [ys] the fact that [xs] is a sub-sequence 
     of [ys] implies that the size of [xs] is at most the size of [ys]. *)
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

  (* We prove that if no element of a sequence [xs] satisfies
     a predicate [P], then [filter P xs] is equal to an empty
     sequence. *)
  Lemma filter_in_pred0:
    forall {X : eqType} (xs : seq X) P,
      (forall x, x \in xs -> ~~ P x) -> 
      filter P xs = [::].
  Proof.
    intros X xs P F.
    induction xs.
    - by done.
    - simpl; rewrite IHxs; last first.
      + intros; apply F.
          by rewrite in_cons; apply/orP; right.
      + destruct (P a) eqn:EQ; last by done.
        move: EQ => /eqP; rewrite eqb_id -[P a]Bool.negb_involutive; move => /negP T.
        exfalso; apply: T.
          by apply F; apply/orP; left.
  Qed.

End AdditionalLemmas.

(** Function [rem] from [ssreflect] removes only the first occurrence of
    an element in a sequence.  We define function [rem_all] which
    removes all occurrences of an element in a sequence. *)
Fixpoint rem_all {X : eqType} (x : X) (xs : seq X) :=
  match xs with
  | [::] => [::]
  | a :: xs => 
    if a == x then rem_all x xs else a :: rem_all x xs
  end.

(** Additional lemmas about [rem_all] for lists. *)
Section RemAllList.

  (** First we prove that [x ∉ rem_all x xs]. *)
  Lemma nin_rem_all:
    forall {X : eqType} (x : X) (xs : seq X), 
      ~ (x \in rem_all x xs).
  Proof.
    intros ? ? ? IN.
    induction xs.
    - by simpl in IN. 
    - apply IHxs.
      simpl in IN.
      destruct (a == x) eqn:EQ; first by done. 
      move: IN; rewrite in_cons; move => /orP [/eqP EQ2 | IN]; last by done.
      subst; exfalso.
        by rewrite eq_refl in EQ.
  Qed.

  (** Next we show that [rem_all x xs ⊆ xs].  *)
  Lemma in_rem_all:
    forall {X : eqType} (a x : X) (xs : seq X), 
      a \in rem_all x xs -> a \in xs.
  Proof.
    intros X a x xs IN.
    induction xs.
    - by done.
    - simpl in IN.
      destruct (a0 == x) eqn:EQ.
      + by rewrite in_cons; apply/orP; right; eauto.
      + move: IN; rewrite in_cons; move => /orP [EQ2|IN].
        * by rewrite in_cons; apply/orP; left.
        * by rewrite in_cons; apply/orP; right; auto.
  Qed.

  (** If an element [x1] is smaller than any element of
      a sequence [xs], then [rem_all x xs = xs]. *)
  Lemma rem_lt_id:
    forall x xs, 
      (forall y, y \in xs -> x < y) ->
      rem_all x xs = xs.
  Proof.
    intros ? ? MIN; induction xs.
    - by simpl.
    - simpl.
      have -> : (a == x) = false.
      { apply/eqP/eqP; rewrite neq_ltn; apply/orP; right.
          by apply MIN; rewrite in_cons; apply/orP; left.
      }
      rewrite IHxs //.
      intros; apply: MIN.
        by rewrite in_cons; apply/orP; right.
  Qed.

End RemAllList.

(** To have a more intuitive naming, we introduce the definition of
    [range a b] which is equal to [index_iota a b.+1]. *)
Definition range (a b : nat) := index_iota a b.+1.

(** Additional lemmas about [index_iota] and [range] for lists. *)
Section IotaRange.
  
  (** First we prove that [index_iota a b = a :: index_iota a.+1 b]
      for [a < b]. *)
  Remark index_iota_lt_step:
    forall a b,
      a < b -> 
      index_iota a b = a :: index_iota a.+1 b.
  Proof.
    intros ? ? LT; unfold index_iota.
    destruct b; first by done.
    rewrite ltnS in LT.
      by rewrite subSn //. 
  Qed.

  (** We prove that one can remove duplicating element from the
      head of a sequence by which [range] is filtered. *)
  Lemma range_filter_2cons:
    forall x xs k, 
      [seq ρ <- range 0 k | ρ \in x :: x :: xs] =
      [seq ρ <- range 0 k | ρ \in x :: xs].
  Proof.
    intros.
    apply eq_filter; intros ?.
    repeat rewrite in_cons.
      by destruct (x0 == x), (x0 \in xs).
  Qed.

  (** Consider [a], [b], and [x] s.t. [a ≤ x < b], 
      then filter of [iota_index a b] with predicate
      [(? == x)] yields [::x]. *)
  Lemma index_iota_filter_eqx:
    forall x a b,
      a <= x < b -> 
      [seq ρ <- index_iota a b | ρ == x] = [::x].
  Proof.
    intros ? ? ?.
    have EX : exists k, b - a <= k.
    { exists (b-a); now simpl. } destruct EX as [k BO].
    revert x a b BO.
    induction k.
    { move => x a b BO /andP [GE LT]; exfalso.
      move: BO; rewrite leqn0 subn_eq0; move => BO.
        by ssromega.
    } 
    { move => x a b BO /andP [GE LT].
      destruct a.
      { destruct b; first by done.
        rewrite index_iota_lt_step //; simpl.
        destruct (0 == x) eqn:EQ.
        - move: EQ => /eqP EQ; subst x.
          rewrite filter_in_pred0 //.
            by intros x; rewrite mem_index_iota -lt0n; move => /andP [T1 _]. 
        - by apply IHk; ssromega. 
      }
      rewrite index_iota_lt_step; last by ssromega.
      simpl; destruct (a.+1 == x) eqn:EQ. 
      - move: EQ => /eqP EQ; subst x.
        rewrite filter_in_pred0 //.
        intros x; rewrite mem_index_iota; move => /andP [T1 _].
          by rewrite neq_ltn; apply/orP; right.
      - by rewrite IHk //; ssromega. 
    } 
  Qed.
  
  (** As a corollary we prove that filter of [iota_index a b] 
      with predicate [(_ ∈ [::x])] yields [::x]. *)
  Corollary index_iota_filter_singl:
    forall x a b,
      a <= x < b -> 
      [seq ρ <- index_iota a b | ρ \in [:: x]] = [::x].
  Proof.
    intros ? ? ? NEQ.
    rewrite -{2}(index_iota_filter_eqx _ a b) //.
    apply eq_filter; intros ?.
      by repeat rewrite in_cons; rewrite in_nil Bool.orb_false_r.
  Qed.

  (** Next we prove that if an element [x] is not in a sequence [xs],
      then [iota_index a b] filtered with predicate [(_ ∈ xs)] is
      equal to [iota_index a b] filtered with predicate [(_ ∈ rem_all
      x xs)]. *)
  Lemma index_iota_filter_inxs:
    forall a b x xs,
      x < a -> 
      [seq ρ <- index_iota a b | ρ \in xs] =
      [seq ρ <- index_iota a b | ρ \in rem_all x xs].
  Proof.
    intros a b x xs LT.
    apply eq_in_filter.
    intros y; rewrite mem_index_iota; move => /andP [LE GT].
    induction xs as [ | y' xs]; first by done.
    rewrite in_cons IHxs; simpl; clear IHxs.
    destruct (y == y') eqn:EQ1, (y' == x) eqn:EQ2; auto.
    - exfalso.
      move: EQ1 EQ2 => /eqP EQ1 /eqP EQ2; subst.
        by ssromega.
    - move: EQ1 => /eqP EQ1; subst.
        by rewrite in_cons eq_refl.
    - by rewrite in_cons EQ1.
  Qed.    

  (** We prove that if an element [x] is a min of a sequence [xs],
      then [iota_index a b] filtered with predicate [(_ ∈ x::xs)] is
      equal to [x :: iota_index a b] filtered with predicate [(_ ∈
      rem_all x xs)]. *)
  Lemma index_iota_filter_step:
    forall x xs a b,
      a <= x < b ->
      (forall y, y \in xs -> x <= y) ->
      [seq ρ <- index_iota a b | ρ \in x :: xs] =
      x :: [seq ρ <- index_iota a b | ρ \in rem_all x xs].
  Proof.
    intros x xs a b B MIN. 
    have EX : exists k, b - a <= k.
    { exists (b-a); now simpl. } destruct EX as [k BO].
    revert x xs a b B MIN BO.
    induction k; move => x xs a b /andP [LE GT] MIN BO.
    - by move_neq_down BO; ssromega.
    - move: LE; rewrite leq_eqVlt; move => /orP [/eqP EQ|LT].
      + subst.
        rewrite index_iota_lt_step //.
        replace ([seq ρ <- x :: index_iota x.+1 b | ρ \in x :: xs])
          with (x :: [seq ρ <- index_iota x.+1 b | ρ \in x :: xs]); last first.
        { simpl; replace (@in_mem nat x (@mem nat (seq_predType nat_eqType) (x::xs))) with true.
          all: by auto; rewrite in_cons eq_refl.
        }
        rewrite (index_iota_filter_inxs _ _ x) //; simpl.
        rewrite eq_refl.
        replace (@in_mem nat x (@mem nat (seq_predType nat_eqType) (@rem_all nat_eqType x xs))) with false; last first.
        apply/eqP; rewrite eq_sym eqbF_neg. apply/negP; apply nin_rem_all.
        reflexivity.
      + rewrite index_iota_lt_step //; last by ssromega.
        replace ([seq ρ <- a :: index_iota a.+1 b | ρ \in x :: xs])
          with ([seq ρ <- index_iota a.+1 b | ρ \in x :: xs]); last first.
        { simpl; replace (@in_mem nat a (@mem nat (seq_predType nat_eqType) (@cons nat x xs))) with false; first by done.
          apply/eqP; rewrite eq_sym eqbF_neg.
          apply/negP; rewrite in_cons; intros C; move: C => /orP [/eqP C|C].
          - by subst; rewrite ltnn in LT.
          - by move_neq_down LT; apply MIN.
        }
        replace ([seq ρ <- a :: index_iota a.+1 b | ρ \in rem_all x xs])
          with ([seq ρ <- index_iota a.+1 b | ρ \in rem_all x xs]); last first.
        { simpl; replace (@in_mem nat a (@mem nat (seq_predType nat_eqType) (@rem_all nat_eqType x xs))) with false; first by done.
          apply/eqP; rewrite eq_sym eqbF_neg; apply/negP; intros C.
          apply in_rem_all in C.
            by move_neq_down LT; apply MIN.
        } 
          by rewrite IHk //; ssromega.
  Qed.

  (** For convenience, we define a special case of
      lemma [index_iota_filter_step] for [a = 0] and [b = k.+1]. *)
  Corollary range_iota_filter_step:
    forall x xs k,
      x <= k ->
      (forall y, y \in xs -> x <= y) ->
      [seq ρ <- range 0 k | ρ \in x :: xs] =
      x :: [seq ρ <- range 0 k | ρ \in rem_all x xs].
  Proof.
    intros x xs k LE MIN.
      by apply index_iota_filter_step; auto.
  Qed.

  (** We prove that if [x < a], then [x < (filter P (index_iota a
      b))[idx]] for any predicate [P]. *)
  Lemma iota_filter_gt:
    forall x a b idx P,
      x < a ->
      idx < size ([seq x <- index_iota a b | P x]) -> 
      x < nth 0 [seq x <- index_iota a b | P x] idx.
  Proof. 
    clear; intros ? ? ? ? ?.
    have EX : exists k, b - a <= k.
    { exists (b-a); now simpl. } destruct EX as [k BO].
    revert x a b idx P BO; induction k.
    - move => x a b idx P BO LT1 LT2.
      move: BO; rewrite leqn0; move => /eqP BO.
        by rewrite /index_iota BO in LT2; simpl in LT2.
    - move => x a b idx P BO LT1 LT2.
      case: (leqP b a) => [N|N].
      + move: N; rewrite -subn_eq0; move => /eqP EQ.
          by rewrite /index_iota EQ //= in LT2.
      + rewrite index_iota_lt_step; last by done.
        simpl in *; destruct (P a) eqn:PA.
        * destruct idx; simpl; first by done.
          apply IHk; try ssromega.
            by rewrite index_iota_lt_step // //= PA //= in LT2.
        * apply IHk; try ssromega.
            by rewrite index_iota_lt_step // //= PA //= in LT2.
  Qed.
  
End IotaRange. 
