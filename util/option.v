From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(** * Definitions for working with option types *)

(** Unwraps a natural number out of an [option nat]. *)
Definition unwrap (opt : option nat) := if opt is Some x then x else 0.

(** We proof, that [Some] is an inverse to [unwrap] if the number is not [None]. *)
Lemma unwrap_inv :
  forall o : option nat,
    o != None ->
    Some (unwrap o) = o.
Proof.
  move=> o; case o => //.
Qed.
