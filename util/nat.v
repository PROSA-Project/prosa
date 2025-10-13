From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.
Require Export mathcomp.zify.zify.

Require Export prosa.util.tactics.

(** To aid rewriting steps in larger proofs, we note two simple facts about
    natural numbers. *)

(** Given [m >= p] and [n >= q], an expression [(m + n) - (p + q)] can be
    rewritten as expression [(m - p) + (n - q)]. *)
Fact subnACA {m n p q} :
  p <= m -> q <= n ->
  (m + n) - (p + q) = (m - p) + (n - q).
Proof. by lia. Qed.

(** We note that [m + p <= n] implies [m <= n - p]. Note that this fact is similar
    to ssreflect's lemma [leq_subRL]; however, this fact avoids the precondition
    [n <= p] since it is only an implication. *)
Fact leq_subRL_impl {m n p} : m + n <= p -> n <= p - m.
Proof. by lia. Qed.
