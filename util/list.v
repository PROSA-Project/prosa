From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Additional lemmas about rem for lists. *)
Section RemList.
  
  (* We prove that if x lies in xs excluding y, then x also lies in xs. *)
  Lemma rem_in:
    forall (T: eqType) (x y: T) (xs: seq T),
      x \in rem y xs -> x \in xs.
  Proof.
    clear; intros.
    induction xs; simpl in H.
    { by rewrite in_nil in H. }
    { rewrite in_cons; apply/orP.
      destruct (a == y) eqn:EQ. 
      { by move: EQ => /eqP EQ; subst a; right. }
      { move: H; rewrite in_cons; move => /orP [/eqP H | H].
        - by subst a; left.
        - by right; apply IHxs.
      }
    }
  Qed.

  (* We prove that if we remove an element x for which P x from 
     a filter, then the size of the filter decreases by 1. *)
  Lemma filter_size_rem: 
    forall (T: eqType) (x:T) (xs: seq T) (P: T -> bool), 
      (x \in xs) ->
      P x ->
      size [seq y <- xs | P y] = size [seq y <- rem x xs | P y] + 1.
  Proof.
    clear; intros.
    induction xs; first by inversion H.
    move: H; rewrite in_cons; move => /orP [/eqP H | H]; subst.
    { by simpl; rewrite H0 -[X in X = _]addn1 eq_refl. }
    { specialize (IHxs H); simpl in *. 
      case EQab: (a == x); simpl.
      { move: EQab => /eqP EQab; subst.
          by rewrite H0 addn1. }
      { case Pa: (P a); simpl.
        - by rewrite IHxs !addn1.
        - by rewrite IHxs.
      }
    }
  Qed.

End RemList.
