Require Export prosa.util.tactics.

(* *********************************************************************)
(*                                                                     *)
(*     Basic lemmas & tactics (based on Viktor Vafeiadis' Vbase.v)     *)
(*                                                                     *)
(* *********************************************************************)

(** This file collects a number of basic lemmas and tactics for better
    proof automation, structuring large proofs, or rewriting.  Most of 
    the rewriting support is ported from ssreflect. *)

(** Symbols starting with [vlib__] are internal. *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype bigop.

Open Scope bool_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* ************************************************************************** *)
(** * Very basic automation *)
(* ************************************************************************** *)

(** Set up for basic simplification *)

Create HintDb vlib discriminated. 

(** Adaptation of the ss-reflect "[done]" tactic. *)

Ltac vlib__basic_done := 
  solve [trivial with vlib | apply sym_equal; trivial | discriminate | contradiction].

Ltac done := trivial with vlib; hnf; intros;
  solve [try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

(** A variant of the ssr "done" tactic that performs "eassumption". *)

Ltac edone := try eassumption; trivial; hnf; intros;
  solve [try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split;
         try eassumption; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by"  tactic(tac) := (tac; done).
Tactic Notation "eby" tactic(tac) := (tac; edone).

(* ************************************************************************** *)
(** * Equality types *)
(* ************************************************************************** *)

Lemma vlib__internal_eqP : 
  forall (T: eqType) (x y : T), reflect (x = y) (x == y).
Proof. by intros; apply/eqP. Qed.

Lemma beq_refl : forall (T : eqType) (x : T), x == x.
Proof. by intros; case eqP. Qed.

Lemma beq_sym : forall (T : eqType) (x y : T), (x == y) = (y == x).
Proof. intros; do 2 case eqP; congruence. Qed.

Hint Resolve beq_refl : vlib.
Hint Rewrite beq_refl : vlib_trivial.

Notation eqxx := beq_refl.

(* ************************************************************************** *)
(** * Basic simplification tactics *)
(* ************************************************************************** *)

Lemma vlib__negb_rewrite : forall b, negb b -> b = false.
Proof. by intros []. Qed.

Lemma vlib__andb_split : forall b1 b2, b1 && b2 -> b1 /\ b2.
Proof. by intros [] []. Qed.

Lemma vlib__nandb_split : forall b1 b2, b1 && b2 = false -> b1 = false \/ b2 = false.
Proof. intros [] []; auto. Qed. 

Lemma vlib__orb_split : forall b1 b2, b1 || b2 -> b1 \/ b2.
Proof. intros [] []; auto. Qed.

Lemma vlib__norb_split : forall b1 b2, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof. intros [] []; auto. Qed.

Lemma vlib__eqb_split : forall b1 b2 : bool, (b1 -> b2) -> (b2 -> b1) -> b1 = b2.
Proof. intros [] [] H H'; unfold is_true in *; auto using sym_eq. Qed.

Lemma vlib__beq_rewrite : forall (T : eqType) (x1 x2 : T), x1 == x2 -> x1 = x2.
Proof. by intros *; case eqP. Qed.

Lemma vlib__leq_split : forall x1 x2 x3, x1 <= x2 -> x2 <= x3 -> x1 <= x2 <= x3.
Proof. by intros; apply/andP; split. Qed.

Lemma vlib__ltn_split1 : forall x1 x2 x3, x1 <= x2 -> x2 < x3 -> x1 <= x2 < x3.
Proof. by intros; apply/andP; split. Qed.

Lemma vlib__ltn_split2 : forall x1 x2 x3, x1 < x2 -> x2 <= x3 -> x1 < x2 <= x3.
Proof. by intros; apply/andP; split. Qed.

(** Set up for basic simplification: database of reflection lemmas *)

Create HintDb vlib_refl discriminated.

Hint Resolve andP orP nandP norP negP vlib__internal_eqP neqP : vlib_refl.

(* Add x <= y <= z splitting to the core hint database. *)
Hint Immediate vlib__leq_split vlib__ltn_split1 vlib__ltn_split2 : core.


Ltac vlib__complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H;
  (*  (lazymatch goal with | [ |- f _ = f _ -> _] => fail | _ => idtac end);  
      (* Previous statement no longer necessary in 8.4 *) *)
  clear H; intros; subst X;
  try subst.

Ltac vlib__clarify1 :=
  try subst;
  repeat match goal with
  | [H: is_true (andb _ _) |- _] => 
      let H' := fresh H in case (vlib__andb_split H); clear H; intros H' H
  | [H: is_true (negb ?x) |- _] => rewrite (vlib__negb_rewrite H) in *
  | [H: is_true ?x        |- _] => rewrite H in *
  | [H: ?x = true         |- _] => rewrite H in *
  | [H: ?x = false        |- _] => rewrite H in *
  | [H: is_true (_ == _)  |- _] => generalize (vlib__beq_rewrite H); clear H; intro H
  | [H: ?f _             = ?f _             |- _] => vlib__complaining_inj f H
  | [H: ?f _ _           = ?f _ _           |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _         = ?f _ _ _         |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => vlib__complaining_inj f H
  end; try done.

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  vlib__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; discriminate
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; vlib__clarify1
  end; (* autorewrite with vlib_trivial; *) try done.

Ltac inv x := inversion x; clarify.
Ltac simpls  := simpl in *; try done.

Tactic Notation "case_eq" constr(x) := case_eq (x).

Tactic Notation "case_eq" constr(x) "as" simple_intropattern(H) :=
  destruct x as [] eqn:H; try done.

Ltac vlib__clarsimp1 :=
  clarify; (autorewrite with vlib_trivial vlib in * ); 
  (autorewrite with vlib_trivial in * ); try done;
  clarify; auto 1 with vlib.

Ltac clarsimp := intros; simpl in *; vlib__clarsimp1.

Ltac autos   := clarsimp; auto with vlib.

(* ************************************************************************** *)
(** Destruct but give useful names *)
(* ************************************************************************** *)

(** Destruct, but no case split *)
Ltac desc :=
  repeat match goal with
    | H: is_true (_ == _) |- _ => generalize (vlib__beq_rewrite H); clear H; intro H
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ =>
      let x' := H in
      let y' := fresh H in
        destruct H as [x' y']
    | H : is_true (_ && _) |- _ => 
          let H' := fresh H in case (vlib__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
          let H' := fresh H in case (vlib__norb_split H); clear H; intros H H'
    | H : ?x = ?x   |- _ => clear H
  end.

Ltac des :=
  repeat match goal with
    | H: is_true (_ == _) |- _ => generalize (vlib__beq_rewrite H); clear H; intro H
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : exists2 x, ?p & ?q |- _ =>
      let x' := fresh x in destruct H as [x' H1 H2]
    | H : ?p /\ ?q |- _ =>
      let x' := H in
      let y' := fresh H in
        destruct H as [x' y']
    | H : is_true (_ && _) |- _ => 
        let H' := fresh H in case (vlib__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
        let H' := fresh H in case (vlib__norb_split H); clear H; intros H H'
    | H : ?x = ?x |- _ => clear H
    | H : ?p <-> ?q |- _ =>
      let x' := H in
      let y' := fresh H in
        destruct H as [x' y']
    | H : ?p \/ ?q |- _ =>
      let x' := H in
      let y' := H in
      destruct H as [x' | y']
    | H : is_true (_ || _) |- _ => case (vlib__orb_split H); clear H; intro H
    | H : (_ && _) = false |- _ => case (vlib__nandb_split H); clear H; intro H
  end.

Ltac des_if_asm :=
  clarify;
  repeat 
    match goal with 
      | H: context[ match ?x with _ => _ end ] |- _ => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn:Heq; clarify
        end 
    end.

Ltac des_if_goal :=
  clarify;
  repeat 
    match goal with 
      | |- context[match ?x with _ => _ end] => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn:Heq; clarify
        end 
    end.

Ltac des_if :=
  clarify;
  repeat 
    match goal with 
      | |- context[match ?x with _ => _ end] => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn:Heq; clarify
        end 
      | H: context[ match ?x with _ => _ end ] |- _ => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] eqn:Heq; clarify
        end 
    end.

Ltac des_eqrefl :=
  match goal with
    | H: context[match ?X with |true => _ | false => _ end Logic.eq_refl] |- _ =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    revert H;
    generalize (Logic.eq_refl X);
    try (generalize X at 1 3); try (generalize X at 2 3);
    intros id' EQ; destruct id'; intros H
    | |- context[match ?X with |true => _ | false => _ end Logic.eq_refl] =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    generalize (Logic.eq_refl X);
    try (generalize X at 1 3); try (generalize X at 2 3);
    intros id' EQ; destruct id'
  end.

Ltac desf_asm := clarify; des; des_if_asm.

Ltac desf := clarify; des; des_if.

Ltac clarassoc := clarsimp; autorewrite with vlib_trivial vlib vlibA in *; try done. 

Ltac vlib__hacksimp1 :=
   clarsimp;
   match goal with
     | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                         |rewrite <- H; clear H; clarsimp]
     | _ => solve [f_equal; clarsimp]
   end.

Ltac hacksimp :=
   clarsimp;
   try match goal with
   | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                              |rewrite <- H; clear H; clarsimp]
   | |- context[match ?p with _ => _ end] => solve [destruct p; vlib__hacksimp1]
   | _ => solve [f_equal; clarsimp]
   end.

(* ************************************************************************** *)
(** ** Delineating cases in proofs *)
(* ************************************************************************** *)

(** Named case tactics (taken from Libtactics) *)

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move x at top
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.

(** Lightweight case tactics (without names) *)

Tactic Notation "--" tactic(c) :=
  first [
    assert (WithinCaseM := True); move WithinCaseM at top
  | fail 1 "because we are working on a different case." ]; c.

Tactic Notation "++" tactic(c) :=
  first [
    assert (WithinCaseP := True); move WithinCaseP at top
  | fail 1 "because we are working on a different case." ]; c.

(* ************************************************************************** *)
(** * New tactics for ssreflect *)
(* ************************************************************************** *)

(* Tactic for simplifying a sum with constant term.
   Usage: simpl_sum_const in H.
   H: \sum_(2 <= x < 4) 5 > 0  ==becomes==>  H: 5 * (4 - 2) > 0 *)
Ltac simpl_sum_const :=
  rewrite ?big_const_nat ?big_const_ord ?big_const_seq iter_addn ?muln1 ?mul1n ?mul0n
          ?muln0 ?addn0 ?add0n.

(* Tactic for splitting all conjunctions in a hypothesis.
   Usage: split_conj H.
   H: A /\ (B /\ C)  ==becomes==>  H1: A
                                   H2: B
                                   H3: C *)
Ltac split_conj X :=
  hnf in X;
  repeat match goal with
    | H : ?p /\ ?q |- _ =>
      let x' := H in
      let y' := fresh H in
        destruct H as [x' y']
  end.
