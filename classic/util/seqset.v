Require Export prosa.util.seqset.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype.

Section Lemmas.

  Context {T: eqType}.
  Variable s: {set T}.

  Lemma set_mem : forall x, (x \in s) = (x \in _set_seq s).
  Proof.
    by intros x; destruct s.
  Qed.
  
End Lemmas.

Section LemmasFinType.
  
  Context {T: finType}.
  Variable s: {set T}.

  Lemma set_card : #|s| = size s.
  Proof.
    have UNIQ: uniq s by destruct s.
    by move: UNIQ => /card_uniqP ->.
  Qed.
  
End LemmasFinType.
