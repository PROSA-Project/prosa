From mathcomp Require Import ssreflect ssrbool ssrnat eqtype bigop.

(** Lemmas & tactics adopted (with permission) from [V. Vafeiadis' Vbase.v]. *)

Lemma neqP: forall (T: eqType) (x y: T), reflect (x <> y) (x != y).
Proof. intros; case eqP; constructor; auto. Qed.

Ltac ins := simpl in *; try done; intros.

(* ************************************************************************** *)
(** ** Exploiting a hypothesis *)
(* ************************************************************************** *)

(** Exploit an assumption (adapted from [CompCert]). *)

Ltac exploit x :=
    refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _) _)
 || refine ((fun x y => y x) (x _ _) _)
 || refine ((fun x y => y x) (x _) _).
 
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
Ltac convert_two_instants_into_instant_and_duration t1 t2 k :=
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
  end.

