From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.
Require Export mathcomp.zify.zify.

Require Import prosa.util.tactics.
Require Export prosa.util.supremum.

(** We define a few simple operations on lists that return zero for
    empty lists: [max0], [first0], and [last0]. *)
Definition max0 := foldl maxn 0.
Definition first0 := head 0.
Definition last0 := last 0.

(** Additional lemmas about [last0]. *)
Section Last0.

  (** Let [xs] be a non-empty sequence and [x] be an arbitrary element,
      then we prove that [last0 (x::xs) = last0 xs]. *)
  Lemma last0_cons :
    forall x xs,
      xs <> [::] ->
      last0 (x::xs) = last0 xs.
  Proof. by move=> x; elim. Qed.

  (** Similarly, let [xs_r] be a non-empty sequence and [xs_l] be any sequence,
      we prove that [last0 (xs_l ++ xs_r) = last0 xs_r]. *)
  Lemma last0_cat :
    forall xs_l xs_r,
      xs_r <> [::] ->
      last0 (xs_l ++ xs_r) = last0 xs_r.
  Proof.
    elim=> [//|xs xs_l IHxs_l] n NEQ.
    simpl; rewrite last0_cons.
    - by apply IHxs_l.
    - by intros C; apply: NEQ; destruct xs_l.
  Qed.

  (** We also prove that [last0 xs = xs [| size xs -1 |] ]. *)
  Lemma last0_nth :
    forall xs,
      last0 xs = nth 0 xs (size xs).-1.
  Proof. by intros; rewrite nth_last. Qed.

  (** We prove that for any non-empty sequence [xs] there is a sequence [xsh]
      such that [xsh ++ [::last0 x] = [xs]]. *)
  Lemma last0_ex_cat :
    forall x xs,
      xs <> [::] ->
      last0 xs = x ->
      exists xsh, xsh ++ [::x] = xs.
  Proof.
    move=> x; elim=> [//|a xs IHxs] NEQ LAST.
    destruct xs.
    - by exists [::]; move: LAST; rewrite /last0 /= => ->.
    - feed_n 2 IHxs; try by done.
      destruct IHxs as [xsh EQ].
      by exists (a::xsh); rewrite //= EQ.
  Qed.

  (** We prove that if [x] is the last element of a sequence [xs] and
      [x] satisfies a predicate, then [x] remains the last element in
      the filtered sequence. *)
  Lemma last0_filter :
    forall x xs (P : nat -> bool),
      xs <> [::] ->
      last0 xs = x ->
      P x ->
      last0 [seq x <- xs | P x] = x.
  Proof.
    clear; intros x xs P NEQ LAST PX.
    destruct (last0_ex_cat x xs NEQ LAST) as [xsh EQ]; subst xs.
    rewrite filter_cat last0_cat.
    all:rewrite //= PX //=.
  Qed.

End Last0.

(** Additional lemmas about [max0]. *)
Section Max0.

  (** First we prove that [max0 (x::xs)] is equal to [max {x, max0 xs}]. *)
  Lemma max0_cons : forall x xs, max0 (x :: xs) = maxn x (max0 xs).
  Proof. by move=> x xs; rewrite /max0 !foldlE /= !big_cons maxnCA. Qed.

  (** Next, we prove that if all the numbers of a seq [xs] are equal
      to a constant [k], then [max0 xs = k]. *)
  Lemma max0_of_uniform_set :
    forall k xs,
      size xs > 0 ->
      (forall x, x \in xs -> x = k) ->
      max0 xs = k.
  Proof.
    move=> k; elim=> [//|a xs IHxs] SIZE ALL.
    destruct xs as [|b xs].
    - rewrite /max0 //= max0n; apply ALL.
      by rewrite in_cons; apply/orP; left.
    - rewrite max0_cons IHxs; [ | by done | ].
      + by rewrite [a]ALL; [ rewrite maxnn | rewrite in_cons; apply/orP; left].
      + move=> x H; apply ALL.
        rewrite in_cons; move: H => /orP [/eqP EQ | IN].
        * by subst x; rewrite !in_cons; apply/orP; right; apply/orP; left.
        * by rewrite !in_cons; apply/orP; right; apply/orP; right.
  Qed.

  (** We prove that no element in a sequence [xs] is greater than [max0 xs]. *)
  Lemma in_max0_le :
    forall xs x, x \in xs -> x <= max0 xs.
  Proof.
    elim=> [//|a xs IHxs] x.
    rewrite in_cons; move => /orP [/eqP EQ | IN]; subst.
    - by rewrite !max0_cons leq_maxl.
    - apply leq_trans with (max0 xs); first by eauto.
      by rewrite max0_cons; apply leq_maxr.
  Qed.

  (** We prove that for a non-empty sequence [xs], [max0 xs ∈ xs]. *)
  Lemma max0_in_seq :
    forall xs,
      xs <> [::] ->
      max0 xs \in xs.
  Proof.
    elim=> [//|a xs IHxs] _.
    destruct xs as [|n xs].
    - destruct a; simpl; first by done.
      by rewrite /max0 //= max0n in_cons eq_refl.
    - rewrite max0_cons.
      move: (leq_total a (max0 (n::xs))) => /orP [LE|LE].
      + by rewrite maxnE subnKC // in_cons; apply/orP; right; apply IHxs.
      + rewrite maxnE; move: LE; rewrite -subn_eq0; move => /eqP EQ.
        by rewrite EQ addn0 in_cons; apply/orP; left.
  Qed.

  (** We prove a technical lemma stating that one can remove
      duplicating element from the head of a sequence. *)
  Lemma max0_2cons_eq :
    forall x xs,
      max0 (x::x::xs) = max0 (x::xs).
  Proof. by intros; rewrite !max0_cons maxnA maxnn. Qed.

  (** Similarly, we prove that one can remove the first element of a
      sequence if it is not greater than the second element of this
      sequence. *)
  Lemma max0_2cons_le :
    forall x1 x2 xs,
      x1 <= x2 ->
      max0 (x1::x2::xs) = max0 (x2::xs).
  Proof.
    by move=> x1 x2 ? ?; rewrite !max0_cons maxnA [maxn x1 x2]maxnE subnKC.
  Qed.

  (** We prove that [max0] of a sequence [xs]
      is equal to [max0] of sequence [xs] without 0s. *)
  Lemma max0_rem0 :
    forall xs,
      max0 ([seq x <- xs | 0 < x]) = max0 xs.
  Proof.
    elim=> [//|a xs IHxs].
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
    { by exists (size xs). }
    move: EX => [len LE].
    generalize dependent xs; elim: len => [|n IHlen] xs LE.
    - by intros; move: LE; rewrite leqn0 size_eq0; move => /eqP EQ; subst.
    - move: LE; rewrite leq_eqVlt; move => /orP [/eqP EQ| LE]; last by apply IHlen.
      destruct xs as [ | x1 xs]; first by inversion EQ.
      destruct xs as [ | x2 xs]; first by rewrite /max leq_max; apply/orP; right.
      have ->: last0 [:: x1, x2 & xs] = last0 [:: x2 & xs] by done.
      rewrite max0_cons leq_max; apply/orP; right; apply IHlen.
      move: EQ => /eqP; simpl; rewrite eqSS; move => /eqP EQ.
      by subst.
  Qed.

  (** Let's introduce the notion of the nth element of a sequence. *)
  Notation "xs [| n |]" := (nth 0 xs n) (at level 30).

  (** If any element of a sequence [xs] is less-than-or-equal-to
      the corresponding element of a sequence [ys], then [max0] of
      [xs] is less-than-or-equal-to max of [ys]. *)
  Lemma max_of_dominating_seq :
    forall xs ys,
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
    elim: len => [ | len IHlen] xs LE1 ys LE2.
    { by move: LE1 LE2; rewrite !leqn0 !size_eq0; move => /eqP E1 /eqP E2; subst. }
    { move: xs ys LE1 LE2 => [ |x xs] [//|y ys] LE1 LE2 H.
      { have L: forall xs, (forall n, xs [| n |] = 0) -> max0 xs = 0.
        { clear; elim=> [//|x xs IHxs] H.
          rewrite max0_cons.
          apply/eqP; rewrite eqn_leq; apply/andP; split; last by done.
          rewrite geq_max; apply/andP; split.
          - by specialize (H 0); simpl in H; rewrite H.
          - rewrite leqn0; apply/eqP; apply: IHxs.
            by move=> n; specialize (H n.+1); simpl in H.
        }
        rewrite L; first by done.
        move=> n0; specialize (H n0).
        by destruct n0; simpl in *; apply/eqP; rewrite -leqn0.
      }
      { rewrite !max0_cons geq_max; apply/andP; split.
        + rewrite leq_max; apply/orP; left.
          by specialize (H 0); simpl in H.
        + rewrite leq_max; apply/orP; right.
          apply IHlen; try (by rewrite ltnS in LE1, LE2).
          by move=> n1; specialize (H n1.+1); simpl in H.
      }
    }
  Qed.

End Max0.

(** Additional lemmas about [rem] for lists. *)
Section RemList.

  (** We prove that if [x] lies in [xs] excluding [y], then
      [x] also lies in [xs]. *)
  Lemma rem_in :
    forall {X : eqType} (x y : X) (xs : seq X),
      x \in rem y xs -> x \in xs.
  Proof.
    move=> X x y; elim=> [|a xs IHxs] /= H.
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

  (** Similarly, we prove that if [x <> y] and [x] lies in [xs],
      then [x] lies in [xs] excluding [y]. *)
  Lemma in_neq_impl_rem_in :
    forall {X : eqType} (x y : X) (xs : seq X),
      x \in xs ->
      x != y ->
      x \in rem y xs.
  Proof.
    move=> X x y; elim=> [//|a xs IHxs].
    rewrite in_cons => /orP [/eqP EQ | IN]; intros NEQ.
    { rewrite -EQ //=.
      move: NEQ; rewrite -eqbF_neg => /eqP ->.
      by rewrite in_cons; apply/orP; left.
    }
    { simpl; destruct (a == y) eqn:AD; first by done.
      rewrite in_cons; apply/orP; right.
      by apply IHxs.
    }
  Qed.

  (** We prove that if we remove an element [x] for which [P x] from a
      filter, then the size of the filter decreases by [1]. *)
  Lemma filter_size_rem :
    forall {X : eqType} (x : X) (xs : seq X) (P : pred X),
      (x \in xs) ->
      P x ->
      size [seq y <- xs | P y] = size [seq y <- rem x xs | P y] + 1.
  Proof.
    move=> X x + P + H0; elim=> [|a xs IHxs] H; first by inversion H.
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

(** Additional lemmas about sequences. *)
Section AdditionalLemmas.

  (** We show that if [n > 0], then [nth (x::xs) n = nth xs (n-1)]. *)
  Lemma nth0_cons :
    forall x xs n,
      n > 0 ->
      nth 0 (x :: xs) n = nth 0 xs n.-1.
  Proof. by move=> ? ? []. Qed.

  (** Equality of singleton lists is identical to equality of option types. *)
  Lemma seq1_some {T : eqType} :
    forall (x y : T),
      ([:: x] == [:: y]) = (Some x == Some y).
  Proof.
    move=> x y.
    case: (eqVneq x y) => [-> //=|/eqP NEQ]; first by rewrite !eq_refl.
    apply/eqP; rewrite ifF.
    - by move=> []EQ; apply: NEQ.
    - by apply/negbTE/eqP => -[].
  Qed.

  (** We prove that a sequence [xs] of size [n.+1] can be destructed
     into a sequence [xs_l] of size [n] and an element [x] such that
     [x = xs ++ [::x]]. *)
  Lemma seq_elim_last :
    forall {X : Type} (n : nat) (xs : seq X),
      size xs = n.+1 ->
      exists x xs__c, xs = xs__c ++ [:: x] /\ size xs__c = n.
  Proof.
    intros X n xs SIZE.
    elim: n xs SIZE => [|n IHn] xs SIZE.
    - destruct xs as [|x xs]; first by done.
      destruct xs; last by done.
      by exists x, [::]; split.
    - destruct xs as [|x xs]; first by done.
      specialize (IHn xs).
      feed IHn; first by simpl in SIZE; apply eq_add_S in SIZE.
      destruct IHn as [x__n [xs__n [EQ__n SIZE__n]]]; subst xs.
      exists x__n, (x :: xs__n); split; first by done.
      simpl in SIZE; apply eq_add_S in SIZE.
      rewrite size_cat //= in SIZE; rewrite addn1 in SIZE; apply eq_add_S in SIZE.
      by apply eq_S.
  Qed.

  (** Next, we prove that [x ∈ xs] implies that [xs] can be split
     into two parts such that [xs = xsl ++ [::x] ++ [xsr]]. *)
  Lemma in_cat :
    forall {X : eqType} (x : X) (xs : list X),
      x \in xs -> exists xsl xsr, xs = xsl ++ [::x] ++ xsr.
  Proof.
    move=> X x; elim=> [//|a xs IHxs] SUB.
    move: SUB; rewrite in_cons; move => /orP [/eqP EQ|IN].
    - by subst; exists [::], xs.
    - feed IHxs; first by done.
      clear IN; move: IHxs => [xsl [xsr EQ]].
      by subst; exists (a::xsl), xsr.
  Qed.

  (** We prove that for any two sequences [xs] and [ys] the fact that [xs] is a sub-sequence
     of [ys] implies that the size of [xs] is at most the size of [ys]. *)
  Lemma subseq_leq_size :
    forall {X : eqType} (xs ys: seq X),
      uniq xs ->
      (forall x, x \in xs -> x \in ys) ->
      size xs <= size ys.
  Proof.
    intros X xs ys UNIQ SUB.
    have EXm: exists m, size ys <= m; first by exists (size ys).
    move: EXm => [m SIZEm].
    move: xs ys SIZEm UNIQ SUB.
    elim: m => [|m IHm] xs ys SIZEm UNIQ SUB.
    { move: SIZEm; rewrite leqn0 size_eq0; move => /eqP SIZEm; subst ys.
      destruct xs as [|s xs]; first by done.
      specialize (SUB s).
      by feed SUB; [rewrite in_cons; apply/orP; left | done].
    }
    { destruct xs as [ | x xs]; first by done.
      move: (@in_cat _ x ys) => Lem.
      feed Lem; first by apply SUB; rewrite in_cons; apply/orP; left.
      move: Lem => [ysl [ysr EQ]]; subst ys.
      rewrite !size_cat //= -addnC add1n addSn ltnS -size_cat; eapply IHm.
      - move: SIZEm; rewrite !size_cat //= => SIZE.
        by rewrite add1n addnS ltnS addnC in SIZE.
      - by move: UNIQ; rewrite cons_uniq => /andP [_ UNIQ].
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
          - by exfalso; move: IN; rewrite in_cons => /orP [IN|IN]; [rewrite IN in EQ | ].
          - by apply/orP; left.
        }
    }
  Qed.

  (** Given two sequences [xs] and [ys], two elements [x] and [y], and
      an index [idx] such that [nth xs idx = x, nth ys idx = y], we
      show that the pair [(x, y)] is in [zip xs ys]. *)
  Lemma in_zip :
    forall {X Y : eqType} (xs : seq X) (ys : seq Y) (x x__d : X) (y y__d : Y),
      size xs = size ys ->
      (exists idx, idx < size xs /\ nth x__d xs idx = x /\ nth y__d ys idx = y) ->
      (x, y) \in zip xs ys.
  Proof.
    move=> X Y xs ys x x__d y y__d.
    elim: xs ys => [|x1 xs IHxs] ys EQ [idx [LT [NTHx NTHy]]] //.
    destruct ys as [ | y1 ys]; first by done.
    rewrite //= in_cons; apply/orP.
    destruct idx as [ | idx]; [left | right].
    { by simpl in NTHx, NTHy; subst. }
    { simpl in NTHx, NTHy, LT.
      eapply IHxs.
      - by apply eq_add_S.
      - by exists idx; repeat split; eauto.
    }
  Qed.

  (** This lemma allows us to check proposition of the form
      [forall x ∈ xs, exists y ∈ ys, P x y] using a boolean expression
      [all P (zip xs ys)]. *)
  Lemma forall_exists_implied_by_forall_in_zip:
    forall {X Y : eqType} (P_bool : X * Y -> bool) (P_prop : X -> Y -> Prop) (xs : seq X),
      (forall x y, P_bool (x, y) <-> P_prop x y) ->
      (exists ys, size xs = size ys /\ all P_bool (zip xs ys) == true) ->
      (forall x, x \in xs -> exists y, P_prop x y).
  Proof.
    move=> X Y P_bool P_prop xs EQ TR x IN.
    destruct TR as [ys [SIZE ALL]].
    set (idx := index x xs).
    have x__d : Y by destruct xs, ys.
    have y__d : Y by destruct xs, ys.
    exists (nth y__d ys idx); apply EQ; clear EQ.
    move: ALL => /eqP/allP -> //.
    eapply in_zip; first by done.
    exists idx; repeat split.
    - by rewrite index_mem.
    - by apply nth_index.
      Unshelve. by done.
  Qed.

  (** Given two sequences [xs] and [ys] of equal size and without
      duplicates, the fact that [xs ⊆ ys] implies that [ys ⊆ xs]. *)
  Lemma subseq_eq:
    forall {X : eqType} (xs ys : seq X),
      uniq xs ->
      uniq ys ->
      size xs = size ys ->
      (forall x, x \in xs -> x \in ys) ->
      (forall x, x \in ys -> x \in xs).
  Proof.
    intros X xs ys UNIQ SUB.
    have EXm: exists m, size ys <= m; first by exists (size ys).
    move: EXm => [m SIZEm].
    move: SIZEm UNIQ SUB; move: xs ys.
    elim: m => [|m IHm] xs ys SIZEm UNIQx UNIQy EQ SUB a IN.
    { by move: SIZEm; rewrite leqn0 size_eq0; move => /eqP SIZEm; subst ys. }
    { destruct xs as [ | x xs].
      { by move: EQ; simpl => /eqP; rewrite eq_sym size_eq0 => /eqP EQ; subst ys. }
      { destruct (x == a) eqn:XA; first by rewrite in_cons eq_sym; apply/orP; left.
        move: XA => /negP/negP NEQ.
        rewrite in_cons eq_sym; apply/orP; right.
        specialize (IHm xs (rem x ys)); apply IHm.
        { rewrite size_rem; last by apply SUB; rewrite in_cons; apply/orP; left.
          by rewrite -EQ //=; move: SIZEm; rewrite -EQ //=. }
        { by move: UNIQx; rewrite cons_uniq => /andP [_ UNIQ]. }
        { by apply rem_uniq. }
        { rewrite size_rem; last by apply SUB; rewrite in_cons; apply/orP; left.
          by rewrite -EQ //=. }
        { intros b INb.
          apply in_neq_impl_rem_in.
          -  apply SUB.
             rewrite in_cons.
             by apply/orP; right.
          - move: UNIQx.
            rewrite cons_uniq => /andP [NIN _].
            apply/negP => /eqP EQbx; subst.
            by move: NIN => /negP NIN; apply: NIN.
        }
        { by apply in_neq_impl_rem_in; last rewrite eq_sym. }
      }
    }
  Qed.

  (** We prove that if no element of a sequence [xs] satisfies a
     predicate [P], then [filter P xs] is equal to an empty
     sequence. *)
  Lemma filter_in_pred0 :
    forall {X : eqType} (xs : seq X) (P : pred X),
      (forall x, x \in xs -> ~~ P x) ->
      filter P xs = [::].
  Proof.
    move=> X xs P; elim: xs => [//|a xs IHxs] ALLF.
    rewrite //= IHxs; last first.
    + by intros; apply ALLF; rewrite in_cons; apply/orP; right.
    + destruct (P a) eqn:EQ; last by done.
      move: EQ => /eqP; rewrite eqb_id -[P a]Bool.negb_involutive; move => /negP T.
      exfalso; apply: T.
      by apply ALLF; apply/orP; left.
  Qed.

  (** We show that any two elements having the same index in a
      sequence must be equal. *)
  Lemma eq_ind_in_seq :
    forall {X : eqType} (a b : X) (xs : seq X),
      index a xs = index b xs ->
      a \in xs ->
      b \in xs ->
      a = b.
  Proof.
    move=> X a b xs EQ IN_a IN_b.
    move: (nth_index a IN_a) => EQ_a.
    move: (nth_index a IN_b) => EQ_b.
    by rewrite -EQ_a -EQ_b EQ.
  Qed.

  (** We show that the nth element in a sequence is either in the
      sequence or is the default element. *)
  Lemma default_or_in :
    forall {X : eqType} (n : nat) (d : X) (xs : seq X),
      nth d xs n = d \/ nth d xs n \in xs.
  Proof.
    move=> x n d xs; destruct (leqP (size xs) n).
    - by left; apply nth_default.
    - by right; apply mem_nth.
  Qed.

  (** We show that in a unique sequence of size greater than one
      there exist two unique elements.  *)
  Lemma exists_two :
    forall {X : eqType} (xs : seq X),
      size xs > 1 ->
      uniq xs ->
      exists a b, a <> b /\ a \in xs /\ b \in xs.
  Proof.
    move=> T xs GT1 UNIQ.
    (* get an element of [T] so that we can use nth *)
    have HEAD: exists x, ohead xs = Some x by elim: xs GT1 UNIQ => // a l _ _ _; exists a => //.
    move: (HEAD) => [x0 _].
    have GT0 : 0 < size xs by exact: ltn_trans GT1.
    exists (nth x0 xs 0).
    exists (nth x0 xs 1).
    repeat split; try apply mem_nth => //.
    apply /eqP; apply contraNneq with (b := (0 == 1)) => // /eqP.
    by rewrite nth_uniq.
  Qed.


  (** The predicate [all] implies the predicate [has], if the sequence is not empty. *)
  Lemma has_all_nilp {T : eqType}:
    forall (s : seq T) (P : pred T),
      all P s ->
      ~~ nilp s ->
      has P s.
  Proof.
    case => // a s P /allP ALL _.
    by apply /hasP; exists a; [|move: (ALL a); apply]; exact: mem_head.
  Qed.

End AdditionalLemmas.


(** Additional lemmas about [sorted]. *)
Section Sorted.

  (** We show that if [[x | x ∈ xs : P x]] is sorted with respect to
      values of some function [f], then it can be split into two parts:
      [[x | x ∈ xs : P x /\ f x <= t]] and [[x | x ∈ xs : P x /\ f x <= t]]. *)
  Lemma sorted_split :
    forall {X : eqType} (xs : seq X) P f t,
      sorted (fun x y => f x <= f y) xs ->
      [seq x <- xs | P x] = [seq x <- xs | P x & f x <= t] ++ [seq x <- xs | P x & f x > t].
  Proof.
    clear; move=> X xs P f t; elim: xs => [//|a xs IHxs] /= SORT.
    have TR : transitive (T:=X) (fun x y : X => f x <= f y).
    { intros ? ? ? LE1 LE2; lia. }
    destruct (P a) eqn:Pa, (leqP (f a) t) as [R1 | R1]; simpl.
    { erewrite IHxs; first by reflexivity.
      by eapply path_sorted; eauto. }
    { erewrite IHxs; last by eapply path_sorted; eauto.
      replace ([seq x <- xs | P x & f x <= t]) with (@nil X); first by done.
      symmetry; move: SORT; rewrite path_sortedE // => /andP [ALL SORT].
      apply filter_in_pred0; intros ? IN; apply/negP; intros H; move: H => /andP [Px LEx].
      by move: ALL => /allP ALL; specialize (ALL _ IN); simpl in ALL; lia.
    }
    { by eapply IHxs, path_sorted; eauto. }
    { by eapply IHxs, path_sorted; eauto. }
  Qed.

  (** We show that if a sequence [xs1 ++ xs2] is sorted, then both
      subsequences [xs1] and [xs2] are sorted as well. *)
  Lemma sorted_cat:
    forall {X : eqType} {R : rel X} (xs1 xs2 : seq X),
      transitive R ->
      sorted R (xs1 ++ xs2) -> sorted R xs1 /\ sorted R xs2.
  Proof.
    move=> X R; elim=> [//|a xs1 IHxs1] xs2 TR SORT; split.
    { move: SORT; rewrite /= path_sortedE// all_cat => /andP[/andP[ALL1 ALL2] SORT].
      rewrite path_sortedE//; apply/andP; split=> //.
      exact: (proj1 (IHxs1 _ _ SORT)).
    }
    { simpl in *; move: SORT; rewrite //= path_sortedE // all_cat => /andP [/andP [ALL1 ALL2] SORT].
      by apply IHxs1.
    }
  Qed.

End Sorted.

(** Additional lemmas about [last]. *)
Section Last.

  (** First, we show that the default element does not change the
      value of [last] for non-empty sequences.  *)
  Lemma nonnil_last :
    forall {X : eqType} (xs : seq X) (d1 d2 : X),
      xs != [::] ->
      last d1 xs = last d2 xs.
  Proof. by move=> X xs d1 d2; elim: xs => [//|a xs IHxs] _. Qed.

  (** We show that if a sequence [xs] contains an element that
      satisfies a predicate [P], then the last element of [filter P xs]
      is in [xs]. *)
  Lemma filter_last_mem :
    forall {X : eqType} (xs : seq X) (d : X) (P : pred X),
      has P xs ->
      last d (filter P xs) \in xs.
  Proof.
    move=> X; elim=> [//|a xs IHxs] d P /hasP [x + Px].
    rewrite in_cons => /orP [/eqP EQ | IN].
    { simpl; subst a; rewrite Px; simpl.
      destruct (has P xs) eqn:HAS.
      { by rewrite in_cons; apply/orP; right; apply IHxs. }
      { replace (filter _ _) with (@nil X).
        - by simpl; rewrite in_cons; apply/orP; left.
        - symmetry; apply filter_in_pred0; intros y IN.
          by move: HAS => /negP/negP/hasPn ALLN; apply: ALLN.
      }
    }
    { rewrite in_cons; apply/orP; right.
      simpl; destruct (P a); simpl; apply IHxs.
      all: by apply/hasP; exists x.
    }
  Qed.

End Last.



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
  Lemma nin_rem_all :
    forall {X : eqType} (x : X) (xs : seq X),
      ~ (x \in rem_all x xs).
  Proof.
    move=> X x; elim=> [//|a xs IHxs] IN.
    apply: IHxs.
    simpl in IN; destruct (a == x) eqn:EQ; first by done.
    move: IN; rewrite in_cons; move => /orP [/eqP EQ2 | IN]; last by done.
    by subst; exfalso; rewrite eq_refl in EQ.
  Qed.

  (** Next we show that [rem_all x xs ⊆ xs].  *)
  Lemma in_rem_all :
    forall {X : eqType} (a x : X) (xs : seq X),
      a \in rem_all x xs -> a \in xs.
  Proof.
    intros X a x; elim=> [//|a0 xs IHxs] /= IN.
    destruct (a0 == x) eqn:EQ.
    - by rewrite in_cons; apply/orP; right; eauto.
    - move: IN; rewrite in_cons; move => /orP [EQ2|IN].
      + by rewrite in_cons; apply/orP; left.
      + by rewrite in_cons; apply/orP; right; auto.
  Qed.

  (** If an element [x] is smaller than any element of
      a sequence [xs], then [rem_all x xs = xs]. *)
  Lemma rem_lt_id :
    forall x xs,
      (forall y, y \in xs -> x < y) ->
      rem_all x xs = xs.
  Proof.
    move=> x; elim=> [//|a xs IHxs] MIN /=.
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

  (** First, we show that [iota m n] can be split into two parts
      [iota m nle] and [iota (m + nle) (n - nle)] for any [nle <= n]. *)
  Lemma iotaD_impl :
    forall n_le m n,
      n_le <= n ->
      iota m n = iota m n_le ++ iota (m + n_le) (n - n_le).
  Proof.
    move=> n_le m n LE.
    interval_to_duration n_le n k.
    by rewrite iotaD; replace (_ + _ - _) with k; last lia.
  Qed.

  (** Next, we prove that [index_iota a b = a :: index_iota a.+1 b]
      for [a < b]. *)
  Remark index_iota_lt_step :
    forall a b,
      a < b ->
      index_iota a b = a :: index_iota a.+1 b.
  Proof.
    move=> a b LT; unfold index_iota.
    destruct b; first by done.
    rewrite ltnS in LT.
    by rewrite subSn //.
  Qed.

  (** We prove that one can remove duplicating element from the
      head of a sequence by which [range] is filtered. *)
  Lemma range_filter_2cons :
    forall x xs k,
      [seq ρ <- range 0 k | ρ \in x :: x :: xs] =
      [seq ρ <- range 0 k | ρ \in x :: xs].
  Proof.
    move=> x xs k; apply: eq_filter => x0.
    by rewrite !in_cons; destruct (x0 == x), (x0 \in xs).
  Qed.

  (** Consider [a], [b], and [x] s.t. [a ≤ x < b],
      then filter of [iota_index a b] with predicate
      [(_ == x)] yields [::x]. *)
  Lemma index_iota_filter_eqx :
    forall x a b,
      a <= x < b ->
      [seq ρ <- index_iota a b | ρ == x] = [::x].
  Proof.
    move=> x a b.
    have EX : exists k, b - a <= k.
    { exists (b-a); by simpl. }
    destruct EX as [k BO].
    revert x a b BO; elim: k => [|k IHk] => x a b BO /andP [GE LT].
    { by exfalso; move: BO; rewrite leqn0 subn_eq0; move => BO; lia. }
    { destruct a as [|a].
      { destruct b; first by done.
        rewrite index_iota_lt_step //; simpl.
        destruct (0 == x) eqn:EQ.
        - move: EQ => /eqP EQ; subst x.
          rewrite filter_in_pred0 //.
          by intros x; rewrite mem_index_iota -lt0n; move => /andP [T1 _].
        - by apply IHk; lia.
      }
      rewrite index_iota_lt_step; last by lia.
      simpl; destruct (a.+1 == x) eqn:EQ.
      - move: EQ => /eqP EQ; subst x.
        rewrite filter_in_pred0 //.
        intros x; rewrite mem_index_iota; move => /andP [T1 _].
        by rewrite neq_ltn; apply/orP; right.
      - by rewrite IHk //; lia.
    }
  Qed.

  (** As a corollary we prove that filter of [iota_index a b]
      with predicate [(_ ∈ [::x])] yields [::x]. *)
  Corollary index_iota_filter_singl :
    forall x a b,
      a <= x < b ->
      [seq ρ <- index_iota a b | ρ \in [:: x]] = [::x].
  Proof.
    move=> x a b NEQ.
    rewrite -{2}(index_iota_filter_eqx _ a b) //.
    apply eq_filter; intros ?.
    by repeat rewrite in_cons; rewrite in_nil Bool.orb_false_r.
  Qed.

  (** Next we prove that if an element [x] is not in a sequence [xs],
      then [iota_index a b] filtered with predicate [(_ ∈ xs)] is
      equal to [iota_index a b] filtered with predicate [(_ ∈ rem_all
      x xs)]. *)
  Lemma index_iota_filter_inxs :
    forall a b x xs,
      x < a ->
      [seq ρ <- index_iota a b | ρ \in xs] =
      [seq ρ <- index_iota a b | ρ \in rem_all x xs].
  Proof.
    intros a b x xs LT.
    apply eq_in_filter.
    intros y; rewrite mem_index_iota; move => /andP [LE GT].
    elim: xs => [//|y' xs IHxs].
    rewrite in_cons IHxs; simpl; clear IHxs.
    destruct (y == y') eqn:EQ1, (y' == x) eqn:EQ2; auto.
    - by exfalso; move: EQ1 EQ2 => /eqP EQ1 /eqP EQ2; subst; lia.
    - by move: EQ1 => /eqP EQ1; subst; rewrite in_cons eq_refl.
    - by rewrite in_cons EQ1.
  Qed.

  (** We prove that if an element [x] is a min of a sequence [xs],
      then [iota_index a b] filtered with predicate [(_ ∈ x::xs)] is
      equal to [x :: iota_index a b] filtered with predicate [(_ ∈
      rem_all x xs)]. *)
  Lemma index_iota_filter_step :
    forall x xs a b,
      a <= x < b ->
      (forall y, y \in xs -> x <= y) ->
      [seq ρ <- index_iota a b | ρ \in x :: xs] =
      x :: [seq ρ <- index_iota a b | ρ \in rem_all x xs].
  Proof.
    intros x xs a b B MIN.
    have EX : exists k, b - a <= k.
    { exists (b-a); by simpl. } destruct EX as [k BO].
    revert x xs a b B MIN BO.
    elim: k => [ |k IHk] x xs a b /andP [LE GT] MIN BO.
    - by move_neq_down BO; lia.
    - move: LE; rewrite leq_eqVlt; move => /orP [/eqP EQ|LT].
      + subst.
        rewrite index_iota_lt_step //.
        replace ([seq ρ <- x :: index_iota x.+1 b | ρ \in x :: xs])
          with (x :: [seq ρ <- index_iota x.+1 b | ρ \in x :: xs]); last first.
        { by rewrite /= in_cons eqxx.
        }
        rewrite (index_iota_filter_inxs _ _ x) //; simpl.
        rewrite eq_refl.
        replace (@in_mem nat x (@mem nat (seq_predType _) (@rem_all _ x xs))) with false; first by reflexivity.
        apply/eqP; rewrite eq_sym eqbF_neg.
        apply/negP; apply nin_rem_all.
      + rewrite index_iota_lt_step //; last by lia.
        replace ([seq ρ <- a :: index_iota a.+1 b | ρ \in x :: xs])
          with ([seq ρ <- index_iota a.+1 b | ρ \in x :: xs]); last first.
        { simpl; replace (@in_mem nat a (@mem nat (seq_predType _) (@cons nat x xs))) with false; first by done.
          apply/eqP; rewrite eq_sym eqbF_neg.
          apply/negP; rewrite in_cons; intros C; move: C => /orP [/eqP C|C].
          - by subst; rewrite ltnn in LT.
          - by move_neq_down LT; apply MIN.
        }
        replace ([seq ρ <- a :: index_iota a.+1 b | ρ \in rem_all x xs])
          with ([seq ρ <- index_iota a.+1 b | ρ \in rem_all x xs]); last first.
        { simpl; replace (@in_mem nat a (@mem nat (seq_predType _) (@rem_all _ x xs))) with false; first by done.
          apply/eqP; rewrite eq_sym eqbF_neg; apply/negP; intros C.
          apply in_rem_all in C.
          by move_neq_down LT; apply MIN.
        }
        by rewrite IHk //; lia.
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
    clear=> x a b idx P.
    have EX : exists k, b - a <= k.
    { exists (b-a); by simpl. } destruct EX as [k BO].
    revert x a b idx P BO; elim: k => [|k IHk].
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
          apply IHk; try lia.
            by rewrite index_iota_lt_step // //= PA //= in LT2.
        * apply IHk; try lia.
            by rewrite index_iota_lt_step // //= PA //= in LT2.
  Qed.

End IotaRange.

(** A sequence [xs] is a prefix of another sequence [ys] iff
    there exists a sequence [xs_tail] such that [ys] is a
    concatenation of [xs] and [xs_tail]. *)
Definition prefix_of {T : eqType} (xs ys : seq T) := exists xs_tail, xs ++ xs_tail = ys.

(** Furthermore, every prefix of a sequence is said to be
    strict if it is not equal to the sequence itself. *)
Definition strict_prefix_of {T : eqType} (xs ys : seq T) :=
  exists xs_tail, xs_tail <> [::] /\ xs ++ xs_tail = ys.

(** We define a helper function that shifts a sequence of numbers forward
    by a constant offset, and an analogous version that shifts them backwards,
    removing any number that, in the absence of Coq' s saturating subtraction,
    would become negative. These functions are very useful in transforming
    abstract RTA's search space. *)
Definition shift_points_pos (xs : seq nat) (s : nat) : seq nat :=
  map (addn s) xs.
Definition shift_points_neg (xs : seq nat) (s : nat) : seq nat :=
  let nonsmall := filter (fun x => x >= s) xs in
  map (fun x => x - s) nonsmall.
