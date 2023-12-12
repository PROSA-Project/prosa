From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop seq div ssrfun.

(** Consider a sequence of unique elements [xs], an element [x0], and
    a predicate [P := λ x => x == x0]. Then, any "bigop" over the
    sequence [xs] w.r.t. the predicate and a function [F] is equal to
    [F x0]. *)
Lemma big_pred1_seq :
  forall [R : Type] [idx : R] [op : Monoid.law idx] [X : eqType] [P : pred X] [F : X -> R]
    (xs : seq X) (i : X),
    (i \in xs) ->
    (uniq xs) ->
    P =1 pred1 i ->
    \big[op/idx]_(j <- xs | P j) F j = F i.
Proof.
  move=> R idx op X P F xs i IN UNI Pi.
  have HAS: has P xs
    by apply /hasP; exists i => //=; rewrite (Pi i) pred1E.
  move: UNI; have [j s1 s2 Pj nPs1] := (split_find HAS) => UNI.
  have nPs2 : ~~ has P s2.
  { apply: contraT => /negPn => hPs2; exfalso.
    move: UNI; rewrite cat_uniq //= => /andP [UNI1 /andP [/negP NE UNI2]].
    move: hPs2 => /hasP [j' IN' Pj'].
    apply/NE/hasP; exists j' => //.
    move: Pj' Pj; rewrite (Pi j') (Pi j) !pred1E => /eqP -> /eqP ->.
    by rewrite mem_rcons mem_head. }
  rewrite -cats1 big_catl // big_catr // big_cons big_nil.
  rewrite ifT // Monoid.simpm.
  by move: Pj; rewrite (Pi j) pred1E //= => /eqP ->.
Qed.
