From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Rewriting *)
(** In this file we prove a few lemmas 
   that simplify work with rewriting. *)
Section RewriteFacilities.
  
  Lemma diseq:
    forall {X : Type} (p : X -> Prop) (x y : X),
      ~ p x -> p y -> x <> y.
  Proof. intros ? ? ? ? NP P EQ; subst; auto. Qed.

  
  Lemma eqprop_to_eqbool {X : eqType} {a b : X}: a = b -> a == b.
  Proof. by intros; apply/eqP. Qed.

  Lemma eqbool_true {X : eqType} {a b : X}: a == b -> a == b = true.
  Proof. by move =>/eqP EQ; subst b; rewrite eq_refl. Qed.

  Lemma eqbool_false {X : eqType} {a b : X}: a != b -> a == b = false.
  Proof. by apply negbTE. Qed.

  
  Lemma eqbool_to_eqprop {X : eqType} {a b : X}: a == b -> a = b.
  Proof. by intros; apply/eqP. Qed.

  Lemma neqprop_to_neqbool {X : eqType} {a b : X}: a <> b -> a != b.
  Proof. by intros; apply/eqP. Qed.

  Lemma neqbool_to_neqprop {X : eqType} {a b : X}: a != b -> a <> b.
  Proof. by intros; apply/eqP. Qed.

  Lemma neq_sym {X : eqType} {a b : X}:
    a != b -> b != a.
  Proof.
    intros NEQ; apply/eqP; intros EQ;
      subst b; move: NEQ => /eqP NEQ; auto. Qed.

  Lemma neq_antirefl {X : eqType} {a : X}:
    (a != a) = false.
  Proof. by apply/eqP. Qed.
  
  
  Lemma option_inj_eq {X : eqType} {a b : X}:
    a == b -> Some a == Some b.
  Proof. by move => /eqP EQ; apply/eqP; rewrite EQ. Qed.

  Lemma option_inj_neq {X : eqType} {a b : X}:
    a != b -> Some a != Some b.
  Proof.
    by move => /eqP NEQ;
     apply/eqP; intros CONTR;
       apply: NEQ; inversion_clear CONTR. Qed.

  (** Example *)
  (* As a motivation for this file, we consider the following example. *)
  Section Example.

    (* Let X  be an arbitrary type ... *)
    Context {X : eqType}.

    (* ... f be an arbitrary function [bool -> bool] ... *)
    Variable f : bool -> bool.

    (* ... p be an arbitrary predicate on X ... *)
    Variable p : X -> Prop.

    (* ... and let a and b be two elements of X such that ... *)
    Variables a b : X.
    
    (* ... p holds for a and doesn't hold for b. *)
    Hypothesis H_pa : p a.
    Hypothesis H_npb : ~ p b.

    (* The following examples are commented out
       to expose the insides of the proofs. *)
    
    (*
    (* Simplifying some relatively sophisticated 
       expressions can be quite tedious. *)
    [Goal f ((a == b) && f false) = f false.]
    [Proof.]
      (* Things like [simpl/compute] make no sense here. *)
      (* One can use [replace] to generate a new goal. *)
      [replace (a == b) with false; last first.]
      (* However, this leads to a "loss of focus". Moreover, 
         the resulting goal is not so trivial to prove. *)
      [{ apply/eqP; rewrite eq_sym eqbF_neg.]
      [    by apply/eqP; intros EQ; subst b; apply H_npb. }]
      [  by rewrite Bool.andb_false_l.]
    [Abort.]
     *)
    
    (*
    (* The second attempt. *)
    [Goal f ((a == b) && f false) = f false.]
      (* With the lemmas above one can compose multiple 
         transformations in a single rewrite. *)
      [  by rewrite (eqbool_false (neq_sym (neqprop_to_neqbool (diseq _ _ _ H_npb H_pa))))]
      [        Bool.andb_false_l.]
    [Qed.]
    *)
    
  End Example.
  
End RewriteFacilities.
