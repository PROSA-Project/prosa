Require Import prosa.classic.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Lemmas about big operators over Ordinals that use Ordinal functions.
   There is no support for them in ssreflect. *)
Section BigOrdFunOrd.

  Definition fun_ord_to_nat {n} {T} (x0: T) (f: 'I_n -> T) : nat -> T.
  (* if x < n, apply the function f in the (Ordinal x: 'I_n), else return default x0. *)
    intro x; destruct (x < n) eqn:LT;
      [by apply (f (Ordinal LT)) | by apply x0].
  Defined.

  Lemma eq_fun_ord_to_nat :
    forall n {T: Type} x0 (f: 'I_n -> T) (x: 'I_n),
      (fun_ord_to_nat x0 f) x = f x.
  Proof.
    ins; unfold fun_ord_to_nat; des_eqrefl.
      by f_equal; apply ord_inj.
      by destruct x; ins; rewrite i in EQ.
  Qed.

  Lemma eq_bigr_ord T n op idx r (P : pred 'I_n)
                    (F1: nat -> T) (F2: 'I_n -> T) :
    (forall i, P i -> F1 i = F2 i) ->
    \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
  Proof.
    induction r; ins; first by rewrite 2!big_nil.
    rewrite 2!big_cons; destruct (P a) eqn:EQ;
      by rewrite IHr; ins; rewrite H; ins.
  Qed.

  Lemma big_mkord_ord {T} {n} {op} {idx} x0 (P : pred 'I_n) (F: 'I_n -> T) :
    \big[op/idx]_(i < n | P i) F i =
      \big[op/idx]_(i < n | P i) (fun_ord_to_nat x0 F) i.
  Proof.
    have EQ := eq_bigr_ord T n op idx _ _ (fun_ord_to_nat x0 F) F.
    rewrite EQ; [by ins | by ins; rewrite eq_fun_ord_to_nat].
  Qed.

End BigOrdFunOrd.