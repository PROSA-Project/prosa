From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.
Require Import prosa.classic.util.all. 

Section find_seq.
  Context {T:eqType}.
  Variable P: T-> bool.
  Fixpoint findP l:= 
    match l with 
    | nil => None
    | x::s => if P x then Some x else findP s
    end.

  Lemma findP_FIFO:
    forall (l:seq T) x y,
    P y = true -> y \in l -> x <> y ->
    findP l = Some x ->
    find (fun j => j==x) l < find (fun j => j==y) l.
  Proof.
    intros* PY YIN NEQ FIND.
    induction l.
    - auto.
    - case (a==x)eqn:AX;case (a==y)eqn:AY;simpl; rewrite AX AY;auto.
      + move/eqP in AX;move/eqP in AY;rewrite AX in AY;auto.
      + simpl in FIND;move/eqP in AY;rewrite AY PY in FIND;clarify;
        by move/eqP in AX. 
      + rewrite in_cons in YIN. move:YIN=> /orP [/eqP EQ | YIN]. move/eqP in AY;auto.
        simpl in FIND. case (P a) eqn:PA;clarify. move/eqP in AX;auto. apply IHl;auto.
  Qed.

  Lemma find_uniql:
    forall (x:T) l1 l2,
    uniq(l1 ++ l2) ->
    x \in l2 ->
    ~ x \in l1.
  Proof.
    intros. intro XIN.
    induction l1. auto. 
    case (a==x)eqn:AX;move/eqP in AX;simpl in H;
    move:H=>/andP [NIN U];move/negP in NIN;auto.
    rewrite AX in NIN. have XIN12: x \in (l1++l2).
    rewrite mem_cat. apply/orP. by right.
    apply IHl1;auto. rewrite in_cons in XIN.
    move:XIN=>/orP [/eqP EQ | XL1];auto.
  Qed.

  Lemma find_uniq:
    forall (x:T) l1 l2,
    uniq(l1 ++ l2) ->
    x \in l2 ->
    has (fun x': T=> x'==x) l1 = false.
  Proof.
    intros.
    apply /negP /negP /hasPn.
    unfold prop_in1. intros.
    apply find_uniql with (x:=x) in H; last by assumption.
    case (x0==x) eqn:XX; last trivial.
    move/eqP in XX.
    rewrite XX in H1; by contradiction.
  Qed.

  Lemma findP_in_seq:
    forall (l:seq T) x,
    findP l = Some x ->
    P x /\ x \in l.
  Proof.
    intros* FIND.
    split.
    - generalize dependent x. induction l.
      + by rewrite /=.
      + simpl. case (P a) eqn:CASE. intros x SOME.
        case : SOME => AX. subst. auto.
        assumption.
    - generalize dependent x. induction l.
      + by rewrite /=.
      + simpl. case (P a) eqn:CASE. intros x SOME.
        case : SOME => AX. subst. rewrite in_cons.
        apply/orP. left. trivial.
        intros x FIND. rewrite in_cons. apply/orP. right. auto.
  Qed.

  Lemma findP_notSome_in_seq:
    forall (l:seq T) x,
    findP l != Some x ->
    x \in l->
    ~ P x \/ exists y, findP l = Some y.
  Proof.
    intros* NFIND IN.
    generalize dependent x. induction l;intros x G IN.
    - auto.
    - simpl in G. case (P a) eqn:CASE.
      + right;exists a;simpl;by rewrite CASE.
      + case (a==x) eqn:AX.
        * left. move/eqP in AX. by rewrite -AX CASE.
        * apply IHl in G. destruct G as [NP|EXIST].
          -- by left.
          -- right. simpl. by rewrite CASE. 
             rewrite in_cons in IN. move/orP in IN.
             destruct IN as [XA | XINL].
             ++ move/eqP in XA. move/eqP in AX. auto.
             ++ trivial.
   Qed.

End find_seq.



