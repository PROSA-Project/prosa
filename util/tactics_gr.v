(* ------------------------------------------------------- *)
(** #<hr> <center> <h1>#
        Basic and simple tactics and notations
       (mostly taken form Software Foundations' LibTactics.v 
        with a few complements) 
#</h1>#    
#</center> <hr>#                                           *)
(*          Pascal Fradet - 2014_2015                      *)
(* ------------------------------------------------------- *)

Require Export Bool Arith.

Set Implicit Arguments.


(* ####################################################### *)
(** *          Some Tactics taken from LibTactics.v        
      by Software Foundations - B. Pierce et al. - Upenn   *)
(* ####################################################### *)
(** The [skip] tactic can be used at any time to admit the current
    goal. Using [skip] is much more efficient than using the [Focus] 
    top-level command to reach a particular subgoal.
*)
(*
Variable skip_axiom : False. 
  (* To obtain a safe development, change to [skip_axiom : True] *)
Ltac skip_with_axiom :=
  elimtype False; apply skip_axiom.

Tactic Notation "skip" := 
   skip_with_axiom. *)

(** ** Introduction *)

(** [introv] is used to name only non-dependent hypothesis.
 - If [introv] is called on a goal of the form [forall x, H],
   it should introduce all the variables quantified with a
   [forall] at the head of the goal, but it does not introduce
   hypotheses that preceed an arrow constructor, like in [P -> Q]. 
 - If [introv] is called on a goal that is not of the form
   [forall x, H] nor [P -> Q], the tactic unfolds definitions
   until the goal takes the form [forall x, H] or [P -> Q].
   If unfolding definitions does not produces a goal of this form,
   then the tactic [introv] does nothing at all. *)
   
(* [introv_rec] introduces all visible variables.
   It does not try to unfold any definition. *)

Ltac introv_rec :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; introv_rec
  | |- _ => idtac
  end.

(* [introv_noarg] forces the goal to be a [forall] or an [->],
   and then calls [introv_rec] to introduces variables
   (possibly none, in which case [introv] is the same as [hnf]).
   If the goal is not a product, then it does not do anything. *)

Ltac introv_noarg :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => introv_rec
  | |- ?G => hnf;
     match goal with
     | |- ?P -> ?Q => idtac
     | |- forall _, _ => introv_rec
     end
  | |- _ => idtac
  end.

  (* simpler yet perhaps less efficient imlementation *)
  Ltac introv_noarg_not_optimized :=
    intro; match goal with H:_|-_ => revert H end; introv_rec.

(* [introv_arg H] introduces one non-dependent hypothesis 
   under the name [H], after introducing the variables
   quantified with a [forall] that preceeds this hypothesis. 
   This tactic fails if there does not exist a hypothesis
   to be introduced. *)

Ltac introv_arg H :=
  hnf; match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.

(* [introv I1 .. IN] iterates [introv Ik] *)

Tactic Notation "introv" :=
  introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
  introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.

(* ---------------------------------------------------------------------- *)
(** ** Optional arguments for tactics  *)
(*
(** [ltac_no_arg] is a constant that can be used to simulate 
    optional arguments in tactic definitions. 
    Use [mytactic ltac_no_arg] on the tactic invokation,
    and use [match arg with ltac_no_arg => ..] or
    [match type of arg with ltac_No_arg  => ..] to
    test whether an argument was provided. *)

Inductive ltac_No_arg : Set := 
  | ltac_no_arg : ltac_No_arg.

*)
(* ---------------------------------------------------------------------- *)
(** ** Wildcard arguments for tactics  *)

(** [ltac_wild] is a constant that can be used to simulate 
    wildcard arguments in tactic definitions. Notation is [__]. *)

Inductive ltac_Wild : Set := 
  | ltac_wild : ltac_Wild.

(*
Notation "'__'" := ltac_wild : ltac_scope. *)

(** [ltac_wilds] is another constant that is typically used to
    simulate a sequence of [N] wildcards, with [N] chosen 
    appropriately depending on the context. Notation is [___]. *)

Inductive ltac_Wilds : Set := 
  | ltac_wilds : ltac_Wilds.

(*
Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope. *)

(* ---------------------------------------------------------------------- *)
(** ** Position markers *)

(** [ltac_Mark] and [ltac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(** [gen_until_mark] repeats [generalize] on hypotheses from the 
    context, starting from the bottom and stopping as soon as reaching
    an hypothesis of type [Mark]. If fails if [Mark] does not
    appear in the context. *)

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with 
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

(** [intro_until_mark] repeats [intro] until reaching an hypothesis of
    type [Mark]. It throws away the hypothesis [Mark]. 
    It fails if [Mark] does not appear as an hypothesis in the 
    goal. *)

Ltac intro_until_mark :=
  match goal with 
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.

(* ---------------------------------------------------------------------- *)
(** ** An alias for [eq] *)

(** [eq'] is an alias for [eq] to be used for equalities in 
    inductive definitions, so that they don't get mixed with
    equalities generated by [inversion]. *)

Definition eq' := @eq.

Hint Unfold eq'.

Notation "x '='' y" := (@eq' _ x y)
  (at level 70, y at next level).


(** [def_to_eq E X H] applies when [X := E] is a local
    definition. It adds an assumption [H: X = E]
    and then clears the definition of [X].
    [def_to_eq_sym] is similar except that it generates
    the equality [H: E = X]. *)

Ltac def_to_eq X HX E :=
  assert (HX : X = E) by reflexivity; clearbody X.
Ltac def_to_eq_sym X HX E :=
  assert (HX : E = X) by reflexivity; clearbody X.

(** ** Absurd goals *)

(** [false_goal] replaces any goal by the goal [False]. 
    Contrary to the tactic [false] (below), it does not try to do
    anything else *)

Tactic Notation "false_goal" :=
  elimtype False.

(** [false_post] is the underlying tactic used to prove goals
    of the form [False]. In the default implementation, it proves
    the goal if the context contains [False] or an hypothesis of the
    form [C x1 .. xN  =  D y1 .. yM], or if the [congruence] tactic
    finds a proof of [x <> x] for some [x]. *) 

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(** [false] replaces any goal by the goal [False], and calls [false_post] *)

Tactic Notation "false" :=
  false_goal; try false_post.
(** [cases] is similar to [case_eq E] except that it generates the
    equality in the context and not in the goal, and generates the
    equality the other way round. The syntax [cases E as H]
    allows specifying the name [H] of that hypothesis. *)

Tactic Notation "cases" constr(E) "as" ident(H) :=
  let X := fresh "x" in
  set (X := E) in *; def_to_eq_sym X H E;
  destruct X.

Tactic Notation "cases" constr(E) :=
  let H := fresh "Eq" in cases E as H.


(* ---------------------------------------------------------------------- *)
(** ** Tagging of hypotheses *)

(** [get_last_hyp tt] is a function that returns the last hypothesis
    at the bottom of the context. It is useful to obtain the default
    name associated with the hypothesis, e.g. 
    [intro; let H := get_last_hyp tt in let H' := fresh "P" H in ...] *)

Ltac get_last_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.

(*
(** [ltac_tag_subst] is a specific marker for hypotheses 
    which is used to tag hypotheses that are equalities to 
    be substituted. *)

Definition ltac_tag_subst (A:Type) (x:A) := x. *)

(** [ltac_to_generalize] is a specific marker for hypotheses 
    to be generalized. *)

Definition ltac_to_generalize (A:Type) (x:A) := x.

Ltac gen_to_generalize :=
  repeat match goal with 
    H: ltac_to_generalize _ |- _ => generalize H; clear H end.

Ltac mark_to_generalize H :=
  let T := type of H in
  change T with (ltac_to_generalize T) in H.


(* ---------------------------------------------------------------------- *)
(** ** Deconstructing terms *)

(** [get_head E] is a tactic that returns the head constant of the 
    term [E], ie, when applied to a term of the form [P x1 ... xN] 
    it returns [P]. If [E] is not an application, it returns [E]. 
    Warning: the tactic seems to loop in some cases when the goal is 
    a product and one uses the result of this function. *)

Ltac get_head E :=
  match E with
  | ?P _ _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ => constr:(P)  
  | ?P _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ => constr:(P)  
  | ?P _ _ _ _ => constr:(P)  
  | ?P _ _ _ => constr:(P) 
  | ?P _ _ => constr:(P)  
  | ?P _ => constr:(P)
  | ?P => constr:(P)
  end.
(*
(** [get_fun_arg E] is a tactic that decomposes an application
  term [E], ie, when applied to a term of the form [X1 ... XN] 
  it returns a pair made of [X1 .. X(N-1)] and [XN]. *)

Ltac get_fun_arg E :=
  match E with
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X => constr:((X1 X2 X3 X4 X5 X6,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X => constr:((X1 X2 X3 X4 X5,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X => constr:((X1 X2 X3 X4,X))  
  | ?X1 ?X2 ?X3 ?X4 ?X => constr:((X1 X2 X3,X))
  | ?X1 ?X2 ?X3 ?X => constr:((X1 X2,X)) 
  | ?X1 ?X2 ?X => constr:((X1,X))
  | ?X1 ?X => constr:((X1,X))
  end.
*)

(* ---------------------------------------------------------------------- *)
(** ** Unfolding *)

(** [unfolds] unfolds the head definition in the goal, i.e. if the
    goal has form [P x1 ... xN] then it calls [unfold P].
    If the goal is an equality, it tries to unfold the head constant
    on the left-hand side, and otherwise tries on the right-hand side.
    If the goal is a product, it calls [intros] first. *)

Ltac apply_to_head_of E cont :=
  let go E :=  
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A 
  end.

Ltac unfolds_base :=
  match goal with |- ?G => 
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.
(*
(** [unfolds in H] unfolds the head definition of hypothesis [H], i.e. if 
    [H] has type [P x1 ... xN] then it calls [unfold P in H]. *)

Ltac unfolds_in_base H :=
  match type of H with ?G => 
   apply_to_head_of G ltac:(fun P => unfold P in H) end.

Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H. *)

(** [unfolds P1,..,PN] is a shortcut for [unfold P1,..,PN in *]. *)

Tactic Notation "unfolds" reference(F1) :=
  unfold F1 in *.
Tactic Notation "unfolds" reference(F1) "," reference(F2) :=
  unfold F1,F2 in *.
Tactic Notation "unfolds" reference(F1) "," reference(F2) 
 "," reference(F3) :=
  unfold F1,F2,F3 in *.
Tactic Notation "unfolds" reference(F1) "," reference(F2) 
 "," reference(F3) "," reference(F4) :=
  unfold F1,F2,F3,F4 in *.
Tactic Notation "unfolds" reference(F1) "," reference(F2) 
 "," reference(F3) "," reference(F4) "," reference(F5) :=
  unfold F1,F2,F3,F4,F5 in *.
Tactic Notation "unfolds" reference(F1) "," reference(F2) 
 "," reference(F3) "," reference(F4) "," reference(F5) "," reference(F6) :=
  unfold F1,F2,F3,F4,F5,F6 in *.
Tactic Notation "unfolds" reference(F1) "," reference(F2) 
 "," reference(F3) "," reference(F4) "," reference(F5) 
 "," reference(F6) "," reference(F7) :=
  unfold F1,F2,F3,F4,F5,F6,F7 in *.
Tactic Notation "unfolds" reference(F1) "," reference(F2) 
 "," reference(F3) "," reference(F4) "," reference(F5) 
 "," reference(F6) "," reference(F7) "," reference(F8) :=
  unfold F1,F2,F3,F4,F5,F6,F7,F8 in *.

(** [exists T1 ... TN] is a shorthand for [exists T1; ...; exists TN].
    It is intended to prove goals of the form [exist X1 .. XN, P].
    If an argument provided is [__] (double underscore), then an
    evar is introduced. [exists T1 .. TN ___] is equivalent to
    [exists T1 .. TN __ __ __] with as many [__] as possible. *)

Tactic Notation "exists_original" constr(T1) :=
  exists T1.
Tactic Notation "exists" constr(T1) :=
  match T1 with
  | ltac_wild => esplit
  | ltac_wilds => repeat esplit
  | _ => exists T1
  end.
Tactic Notation "exists" constr(T1) constr(T2) :=
  exists T1; exists T2.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) :=
  exists T1; exists T2; exists T3.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) :=
  exists T1; exists T2; exists T3; exists T4.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) 
 constr(T5) :=
  exists T1; exists T2; exists T3; exists T4; exists T5.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) 
 constr(T5) constr(T6) :=
  exists T1; exists T2; exists T3; exists T4; exists T5; exists T6.

(* ********************************************************************** *)
(** * Inversion *)

(* ---------------------------------------------------------------------- *)
(** ** Basic inversion *)

(** [invert keep H] is same to [inversion H] except that it puts all the
    facts obtained in the goal. The keyword [keep] means that the
    hypothesis [H] should not be removed. *)

Tactic Notation "invert" "keep" hyp(H) :=
  pose ltac_mark; inversion H; gen_until_mark.

(** [invert keep H as X1 .. XN] is the same as [inversion H as ...] except
    that only hypotheses which are not variable need to be named
    explicitely, in a similar fashion as [introv] is used to name
    only hypotheses. *)

Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1) :=
  invert keep H; introv I1. 
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) :=
  invert keep H; introv I1 I2. 
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert keep H; introv I1 I2 I3. 

(** [invert H] is same to [inversion H] except that it puts all the
    facts obtained in the goal and clears hypothesis [H].
    In other words, it is equivalent to [invert keep H; clear H]. *)

Tactic Notation "invert" hyp(H) :=
  invert keep H; clear H.

(** [invert H as X1 .. XN] is the same as [invert keep H as X1 .. XN]
    but it also clears hypothesis [H]. *)

Tactic Notation "invert_tactic" hyp(H) tactic(tac) :=
  let H' := fresh in rename H into H'; tac H'; clear H'.
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => invert keep H as I1).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) :=
  invert_tactic H (fun H => invert keep H as I1 I2).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => invert keep H as I1 I2 I3).


(* ---------------------------------------------------------------------- *)
(** ** Inversion with substitution *)

(** Our inversion tactics is able to get rid of dependent equalities
    generated by [inversion], using proof irrelevance. *)

(* --we do not import Eqdep because it imports nasty hints automatically 
    Require Import Eqdep. *)

Axiom inj_pair2 : forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
       existT P p x = existT P p y -> x = y.
(* Proof. apply Eqdep.EqdepTheory.inj_pair2. Qed.*)

Ltac inverts_tactic H i1 i2 i3 i4 i5 i6 :=
  let rec go i1 i2 i3 i4 i5 i6 :=
    match goal with 
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh in intro H; 
                           first [ subst x | subst y ]; 
                           go i1 i2 i3 i4 i5 i6
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H; 
         generalize (@inj_pair2 _ P p x y H);
         clear H; go i1 i2 i3 i4 i5 i6
    | |- (?P -> ?Q) => i1; go i2 i3 i4 i5 i6 ltac:(intro)
    | |- (forall _, _) => intro; go i1 i2 i3 i4 i5 i6
    end in
  generalize ltac_mark; invert keep H; go i1 i2 i3 i4 i5 i6;
  unfold eq' in *.

(** [inverts keep H] is same to [invert keep H] except that it 
    applies [subst] to all the equalities generated by the inversion. *)

Tactic Notation "inverts" "keep" hyp(H) :=
  inverts_tactic H ltac:(intro) ltac:(intro) ltac:(intro) 
                   ltac:(intro) ltac:(intro) ltac:(intro).

(** [inverts keep H as X1 .. XN] is the same as
    [invert keep H as X1 .. XN] except that it applies [subst] to all the 
    equalities generated by the inversion *)

Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) :=
  inverts_tactic H ltac:(intros I1) 
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2)
   ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
 simple_intropattern(I5) simple_intropattern(I6) :=
  inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
   ltac:(intros I4) ltac:(intros I5) ltac:(intros I6).

(** [inverts H] is same to [inverts keep H] except that it 
    clears hypothesis [H]. *)

Tactic Notation "inverts" hyp(H) :=
  inverts keep H; clear H.

(** [inverts H as X1 .. XN] is the same as [inverts keep H as X1 .. XN]
    but it also clears the hypothesis [H]. *)

Tactic Notation "inverts_tactic" hyp(H) tactic(tac) :=
  let H' := fresh in rename H into H'; tac H'; clear H'.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) :=
  invert_tactic H (fun H => inverts keep H as I1).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) :=
  invert_tactic H (fun H => inverts keep H as I1 I2).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) 
 simple_intropattern(I5) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) 
 simple_intropattern(I5) simple_intropattern(I6) :=
  invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5 I6).

(** [inverts H as] performs an inversion on hypothesis [H], substitutes
    generated equalities, and put in the goal the other freshly-created
    hypotheses, for the user to name explicitly. 
    [inverts keep H as] is the same except that it does not clear [H].
    --TODO: reimplement [inverts] above using this one *)

Ltac inverts_as_tactic H :=
  let rec go tt :=
    match goal with 
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H; 
                           first [ subst x | subst y ]; 
                           go tt
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H; 
         generalize (@inj_pair2 _ P p x y H);
         clear H; go tt
    | |- (forall _, _) => 
       intro; let H := get_last_hyp tt in mark_to_generalize H; go tt
    end in
  pose ltac_mark; inversion H; 
  generalize ltac_mark; gen_until_mark; 
  go tt; gen_to_generalize; unfolds ltac_to_generalize;
  unfold eq' in *.

Tactic Notation "inverts" "keep" hyp(H) "as" :=
  inverts_as_tactic H.

Tactic Notation "inverts" hyp(H) "as" :=
  inverts_as_tactic H; clear H.

Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) 
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) 
 simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) 
 simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7)
 simple_intropattern(I8) :=
  inverts H as; introv I1 I2 I3 I4 I5 I6 I7 I8.

(* ####################################################### *)
(*   We mostly make use of  (introv, inverts, etc.)        *)
(*   and the following small shortcuts                     *)
(* ####################################################### *)

Ltac easy := solve [simpl; intros; auto].
(* Ltac easy := solve [simpl; intros; info_auto]. *)

Ltac dupl_base h1 h2 := generalize h1; intro h2.
Tactic Notation "dupl" hyp(H1)
                 ident(H2):= dupl_base H1 H2.
Tactic Notation "dupl" hyp(H1)
                 ident(H2) 
                 ident(H3):= dupl_base H1 H2; dupl H1 H3.
Tactic Notation "dupl" hyp(H1) 
                 ident(H2) 
                 ident(H3)
                 ident(H4):= dupl_base H1 H2; dupl H1 H3; dupl H1 H4.

Lemma eqfst: forall A B (a b:A*B), a=b -> fst a = fst b.
Proof. introv H. rewrite H. reflexivity. Qed.

Lemma eqsnd: forall A B (a b:A*B), a=b -> snd a = snd b.
Proof. introv H. rewrite H. reflexivity. Qed.

Lemma dpair : forall A B (x:A*B), exists f, exists s, x = (f,s).
Proof. introv. destruct x. exists a b. easy. Qed.

Ltac dstpair_base H Hf Hs :=  
dupl H Hf; apply eqfst in Hf; simpl in Hf;
dupl H Hs; apply eqsnd in Hs; simpl in Hs.

Tactic Notation "dstpair" hyp(H1) ident(H2) ident(H3) := dstpair_base H1 H2 H3.

Tactic Notation "dstpair" constr(E) ident(f) ident(s) ident(H) ident(Hf) ident(Hs)
              := destruct (dpair E) as [f [s H]]; dstpair_base H Hf Hs.
