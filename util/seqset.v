From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype.

(** In this section, we define a notion of a set (based on a sequence
    without duplicates). *)
Section SeqSet.

  (** Let [T] be any type with decidable equality. *)
  Context {T : eqType}.

  (** We define a set as a sequence that has no duplicates. *)
  Record set :=
  {
    _set_seq :> seq T ;
    _ : uniq _set_seq (* no duplicates *)
  }.

  (** Now we add the [ssreflect] boilerplate code to support [_ == _]
      and [_ ∈ _] operations. *)
  Set Warnings "-redundant-canonical-projection".
  HB.instance Definition _  setSubType := [isSub for _set_seq].
  HB.instance Definition _ := [Equality of set by <:].
  Canonical Structure mem_set_predType := PredType (fun (l : set) => mem_seq (_set_seq l)).
  Definition set_of of phant T := set.

End SeqSet.
Set Warnings "redundant-canonical-projection".

Notation " {set R } " := (set_of (Phant R)).

(** Next we prove a basic lemma about sets. *)
Section Lemmas.

  (** Consider a set [s]. *)
  Context {T : eqType}.
  Variable s : {set T}.

  (** Then we show that element of [s] are unique. *)
  Lemma set_uniq : uniq s.
  Proof. by destruct s. Qed.

End Lemmas.
