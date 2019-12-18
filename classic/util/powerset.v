Require Import prosa.classic.util.tactics.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop tuple.

Section PowerSet.
  
  (* Based on https://www.ps.uni-saarland.de/formalizations/fset/html/libs.fset.html *)
  Definition powerset {T: eqType} (l: seq T) : seq (seq T) :=
    let mT := ((size l).-tuple bool) in
      (map (fun m : mT => (mask m l)) (enum {: mT})).

  Lemma mem_powerset {T: eqType} (x: seq T) y :
    y \in (powerset x) -> {subset y <= x}.          
  Proof.
    intros POW; red; intros z IN; unfold powerset in POW.
    move: POW => /mapP POW; destruct POW as [pair POW EQ]; subst.
    by apply mem_mask with (m := pair).
  Qed.

End PowerSet.