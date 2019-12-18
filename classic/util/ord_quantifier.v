Require Import prosa.classic.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype.

(* Lemmas about the exists for Ordinals: [exists x, P x]. *)
Section OrdExists.

  Lemma exists_ord0:
    forall P,
      [exists x in 'I_0, P x] = false.
  Proof.
    intros P.
    apply negbTE; rewrite negb_exists; apply/forall_inP.
    intros x; destruct x as [x LT].
    by exfalso; rewrite ltn0 in LT.
  Qed.

  Lemma exists_recr:
    forall n P,
      [exists x in 'I_n.+1, P x] =
      [exists x in 'I_n, P (widen_ord (leqnSn n) x)] || P (ord_max).
  Proof.
    intros n P.
    apply/idP/idP.
    {
      move => /exists_inP EX; destruct EX as [x IN Px].
      destruct x as [x LT].
      remember LT as LT'; clear HeqLT'. 
      rewrite ltnS leq_eqVlt in LT; move: LT => /orP [/eqP EQ | LT].
      {
        apply/orP; right.
        unfold ord_max; subst x.
        apply eq_trans with (y := P (Ordinal LT')); last by done.
        by f_equal; apply ord_inj.
      }
      {
        apply/orP; left.
        apply/exists_inP; exists (Ordinal LT); first by done.
        apply eq_trans with (y := P (Ordinal LT')); last by done.
        by f_equal; apply ord_inj.
      }
    }
    {
      intro OR; apply/exists_inP.
      move: OR => /orP [/exists_inP EX | MAX].
      {
        by destruct EX as [x IN Px]; exists (widen_ord (leqnSn n) x).
      }
      by exists ord_max.
    }
  Qed.

End OrdExists.

(* Lemmas about the forall for Ordinals: [exists x, P x]. *)
Section OrdForall.

  Lemma forall_ord0:
    forall P,
      [forall x in 'I_0, P x].
  Proof.
    intros P; apply/forall_inP.
    by intros x IN0; destruct x.
  Qed.

  Lemma forall_recr:
    forall n P,
      [forall x in 'I_n.+1, P x] =
      [forall x in 'I_n, P (widen_ord (leqnSn n) x)] && P (ord_max).
  Proof.
    intros n P.
    apply/idP/idP.
    {
      move => /forall_inP ALL.
      apply/andP; split; last by apply ALL.
      by apply/forall_inP; intros x IN; apply ALL.
    }
    {
      move => /andP [/forall_inP ALL MAX].
      apply/forall_inP; intros x IN.
      destruct x as [x LT].
      unfold ord_max in *.
      remember LT as LT'; clear HeqLT'.
      rewrite ltnS leq_eqVlt in LT; move: LT => /orP [/eqP EQ | LT].
      {
        subst n.
        apply/eqP; rewrite -MAX; apply/eqP.
        by unfold ord_max; apply f_equal, ord_inj.
      }
      {
        feed (ALL (Ordinal LT)); first by done.
        apply/eqP; rewrite -ALL; apply/eqP.
        by apply f_equal, ord_inj.
      }
    }
  Qed.

End OrdForall.

(* Tactics for simplifying exists and forall. *)
Ltac simpl_exists_ord := rewrite !exists_recr !exists_ord0 /=.
Ltac simpl_forall_ord := rewrite !forall_recr !forall_ord0 /=.