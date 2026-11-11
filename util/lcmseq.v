Require Export prosa.util.bigop.

(** The least common multiple of all natural numbers in a sequence. *)
Definition lcml (xs : seq nat) : nat := \big[lcmn/1]_(x <- xs) x.
