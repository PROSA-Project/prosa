From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype.

Section SeqSet.

  (* Let T be any type with decidable equality. *)
  Context {T: eqType}.

  (* We define a set as a sequence that has no duplicates. *)
  Record set :=
  {
    _set_seq :> seq T ;
    _ : uniq _set_seq (* no duplicates *)
  }.

  (* Now we add the [ssreflect] boilerplate code. *)
  Canonical Structure setSubType := [subType for _set_seq].
  Definition set_eqMixin := [eqMixin of set by <:].
  Canonical Structure set_eqType := EqType set set_eqMixin.
  Canonical Structure mem_set_predType := PredType (fun (l : set) => mem_seq (_set_seq l)).
  Definition set_of of phant T := set.

End SeqSet.

Notation " {set R } " := (set_of (Phant R)).

Section Lemmas.

  Context {T: eqType}.
  Variable s: {set T}.

  Lemma set_uniq : uniq s.
  Proof.
    by destruct s.
  Qed.

End Lemmas.
