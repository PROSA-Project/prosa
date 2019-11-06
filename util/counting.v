From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Additional lemmas about counting. *)
Section Counting.
  
  Lemma count_filter_fun :
    forall (T: eqType) (l: seq T) P,
      count P l = size (filter P l).
  Proof.
    intros T l P.
    induction l; simpl; first by done.
    by destruct (P a); [by rewrite add1n /=; f_equal | by rewrite add0n].
  Qed.

End Counting.