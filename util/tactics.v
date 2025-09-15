From mathcomp Require Import ssreflect ssrbool ssrnat eqtype bigop.

(** Lemmas & tactics adopted (with permission) from [V. Vafeiadis' Vbase.v]. *)

Lemma neqP : forall (T : eqType) (x y : T), reflect (x <> y) (x != y).
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

(** If a subexpression [expr] of a goal is known to be equal to
    [false], it may be tempting to use a lemma of the form [expr =
    false] to simply rewrite the [expr] with [false]. However, the
    coding style of Prosa dictates that lemmas should be stated in the
    form [~~ expr]. Therefore, direct rewriting with such lemmas is
    not possible. This tactic implicitly transforms a lemma of the
    form [~~ expr] into [expr = false].

    As an example, suppose we have a goal [f(B1 || B2 && B3 ) = 1],
    where [B1, B2, B3 : bool] and [f : bool -> nat]. Suppose we also have
    several lemmas of the form [Li : H1 -> H2 -> ... -> Hn -> ~~ Bi]. One
    possible way to reduce [f(B1 || B2 && B3)] to [f(false)] is to
    somehow replace [Bi]-s with [false] (e.g., via [negbTE]) and then
    apply [Li]-s. This can be tedious if boolean variable names are
    long. The [rewrite_neg] tactic allows one to simply write
    [rewrite_neg Bi] to replace [Bi] with [false]. *)
Ltac rewrite_neg H :=
  let NEWH := fresh in
  (unshelve ((exploit H; last (rewrite -eqbF_neg => /eqP NEWH; rewrite NEWH; clear NEWH)) => //)) => //.


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

(** We introduce tactics [rt_auto] and [fail] as a shorthand for
    [(e)auto with basic_rt_facts] to facilitate automation. Here, we
    use scope [basic_rt_facts] that contains a collection of basic
    real-time theory lemmas. *)
(** Note: constant [4] was chosen because most of the basic rt facts
    have the structure [A1 -> A2 -> ... B], where [Ai] is a hypothesis
    usually present in the context, which gives the depth of the
    search which is equal to two. Two additional levels of depth (4)
    was added to support rare exceptions to this rule. In particular,
    depth 4 is needed for automatic periodic->RBF arrival model
    conversion. At the same time, the constant should not be too large
    to avoid slowdowns in case of an unsuccessful application of
    automation. *)
#[deprecated(since="prosa-0.6", note="use by or // instead")]
Ltac rt_auto := auto 4 with basic_rt_facts.
#[deprecated(since="prosa-0.6", note="use by or // instead")]
Ltac rt_eauto := eauto 4 with basic_rt_facts.

Ltac done := solve [ ssreflect.done | eauto 4 with basic_rt_facts ].
#[export] Hint Resolve I : basic_rt_facts.  (* ensure the database exists *)

(** Note: [idtac] is a no-op. However, it suppresses the default obligation tactic,
    which uses [intros] to introduce unnamed variables. This is a Coq technicality
    that a casual reader may safely ignore. It is necessary to avoid triggering one
    of Prosa's continuous integration checks that validates that no proof scripts
    depend on automatically generated names.  *)
#[global] Obligation Tactic := idtac.

(** The mathematical components library turns off Coq' s support for the enforcement
    of structured sub-proofs. We do want structured sub-proofs in Prosa, however, so
    here we turn strict checking back on. *)
#[global] Set Bullet Behavior "Strict Subproofs".
#[global] Set Default Goal Selector "!".

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
  | [ H: is_true(t1 <= t2) |- _ ] =>
    ltac:(
      assert (EX : exists (k: nat), t2 = t1 + k);
      [exists (t2 - t1); rewrite subnKC; auto using ltnW | ];
      destruct EX as [k EQ]; subst t2; clear H
    )
  | [ H: is_true(t1 < t2) |- _ ] =>
    ltac:(
      assert (EX : exists (k: nat), t2 = t1 + k);
      [exists (t2 - t1); rewrite subnKC; auto using ltnW | ];
      destruct EX as [k EQ]; subst t2; clear H
    )
  end.
