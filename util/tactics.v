From mathcomp Require Import ssreflect ssrbool ssrnat eqtype bigop.

(** Lemmas & tactics adopted (with permission) from [V. Vafeiadis' Vbase.v]. *)

Lemma neqP: forall (T: eqType) (x y: T), reflect (x <> y) (x != y).
Proof. intros; case eqP; constructor; auto. Qed.

Ltac ins := simpl in *; try done; intros.

(* ************************************************************************** *)
(** ** Exploiting a hypothesis *)
(* ************************************************************************** *)

(** Exploit an assumption (adapted from [CompCert]). *)

Lemma modusponens : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof. by auto. Qed.

Ltac exploit x :=
  refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _) _)
  || refine (modusponens _ _ (x _ _) _)
  || refine (modusponens _ _ (x _) _).

 
(* This tactic feeds the precondition of an implication in order to derive the conclusion
   (taken from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013).

   Usage: feed H.

   H: P -> Q  ==becomes==>  H: P
                            ____
                            Q

   After completing this proof, Q becomes a hypothesis in the context. *)
Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

(* Generalization of feed for multiple hypotheses.
   feed_n is useful for accessing conclusions of long implications.

   Usage: feed_n 3 H.
     H: P1 -> P2 -> P3 -> Q.

   We'll be asked to prove P1, P2 and P3, so that Q can be inferred. *)
Ltac feed_n n H := match constr:(n) with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
  end.

(** We introduce tactics [rt_auto] and [rt_eauto] as a shorthand for
    [(e)auto with basic_rt_facts] to facilitate automation. Here, we
    use scope [basic_rt_facts] that contains a collection of basic
    real-time theory lemmas. *)
(** Note: constant [3] was chosen because most of the basic rt facts
    have the structure [A1 -> A2 -> ... B], where [Ai] is a hypothesis
    usually present in the context, which gives the depth of the
    search which is equal to two. One additional level of depth (3)
    was added to support rare exceptions to this rule. At the same
    time, the constant should not be too large to avoid slowdowns in
    case of an unsuccessful application of automation. *)
Ltac rt_auto := auto 3 with basic_rt_facts.
Ltac rt_eauto := eauto 3 with basic_rt_facts.

(* ************************************************************************** *)
(** * Handier movement of inequalities. *)
(* ************************************************************************** *)
Ltac move_neq_down H :=
  exfalso;
  (move: H; rewrite ltnNge; move => /negP H; apply: H; clear H)
  || (move: H; rewrite leqNgt; move => /negP H; apply: H; clear H).

Ltac move_neq_up H :=
  (rewrite ltnNge; apply/negP; intros H)
  || (rewrite leqNgt; apply/negP; intros H).

(** The following tactic converts inequality [t1 <= t2] into a constant
    [k] such that [t2 = t1 + k] and substitutes all the occurrences of
    [t2]. *)
Ltac interval_to_duration t1 t2 k :=
  match goal with
  | [ H: (t1 <= t2) = true |- _ ] =>
    ltac:(
      assert (EX : exists (k: nat), t2 = t1 + k);
      [exists (t2 - t1); rewrite subnKC; auto | ];
      destruct EX as [k EQ]; subst t2; clear H
    )
  | [ H: (t1 < t2) = true |- _ ] =>
    ltac:(
      assert (EX : exists (k: nat), t2 = t1 + k);
      [exists (t2 - t1); rewrite subnKC; auto using ltnW | ];
      destruct EX as [k EQ]; subst t2; clear H
    )
  | [ H: is_true (t1 <= t2) |- _ ] =>
    ltac:(
      assert (EX : exists (k: nat), t2 = t1 + k);
      [exists (t2 - t1); rewrite subnKC; auto | ];
      destruct EX as [k EQ]; subst t2; clear H
    )
  | [ H: is_true (t1 < t2) |- _ ] =>
    ltac:(
      assert (EX : exists (k: nat), t2 = t1 + k);
      [exists (t2 - t1); rewrite subnKC; auto using ltnW | ];
      destruct EX as [k EQ]; subst t2; clear H
    )
  end.

