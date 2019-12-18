(* Require Import Extraction. *) (* Required for Coq 8.7 *)
Require Import prosa.classic.analysis.uni.basic.tdma_wcrt_analysis.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Set Implicit Arguments.

CoInductive Task_T :Type:=
  build_task: nat->nat->nat->nat -> 
              Task_T.

Definition get_slot(tsk:Task_T):= 
  match tsk with
  | build_task x  _ _ _  => x end.

Definition get_cost (tsk:Task_T):=
 match tsk with
  | build_task _ x _ _  => x end.

Definition get_D (tsk:Task_T):=
 match tsk with
  | build_task _ _ x _  => x end.

Definition get_P (tsk:Task_T):=
  match tsk with
  | build_task _ _ _ x => x end.

Definition task_eq (t1 t2: Task_T) :=
      (get_slot t1 == get_slot t2)&&
      (get_cost t1 == get_cost t2)&&
      (get_D t1 == get_D t2)&&
      (get_P t1 == get_P t2) .

Fixpoint In (a:Task_T) (l:list Task_T) : Prop :=
    match l with
      | nil => False
      | b :: m =>  a=b \/ In a m
    end.

Definition schedulable_tsk T tsk:=
    let bound := WCRT_OneJobTDMA.WCRT_formula T (get_slot tsk) (get_cost tsk) in
  if (bound <= get_D tsk)&& (bound <= get_P tsk) then true else false .

Fixpoint schedulability_test T (l: list Task_T):=
match l with
|nil => true
|x::s=> (schedulable_tsk T x) && (schedulability_test T s)
end.

Theorem schedulability_test_valid T TL:
schedulability_test T TL
    <-> (forall tsk, In tsk TL ->schedulable_tsk T tsk) .
Proof.
induction TL;split;auto.
- intros STL tsk IN. rewrite /= in IN. move:IN=> [EQ |IN];
  rewrite /= in STL; move/andP in STL.
  + rewrite EQ;apply STL.
  + apply IHTL. apply STL. assumption.
- intro ALL. apply/andP;split.
  + apply ALL. simpl;by left.
  + apply IHTL;intros tsk IN;apply ALL;simpl;by right.
Qed. 

Definition cycle l:=
(foldr plus 0 (map get_slot l)).

Definition schedulability_tdma (l: list Task_T):=
schedulability_test (cycle l) l.

Theorem schedulability_tdma_valid task_list:
   schedulability_tdma task_list
    <-> (forall tsk, In tsk task_list ->schedulable_tsk (cycle task_list) tsk) .
Proof.
rewrite /schedulability_tdma. apply schedulability_test_valid.
Qed.

(*Eval compute in cycle [:: build_task(2,3,4,4);(6,2,5,6)].

Eval compute in WCRT_OneJobTDMA.WCRT_formula 4 2 3.

Eval compute in schedulability_tdma [::(2,3,7,7);(1,2,6,6)]. *)

(*Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool =>"bool" [ "true" "false" ].
Extract Inductive nat => int [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant eqn => "(=)".
Extract Constant addn => "(+)".
Extract Constant subn => "fun n m -> Pervasives.max 0 (n-m)".
Extract Constant muln => "( * )".
Extract Inlined Constant leq => "(<=)".
Recursive Extraction schedulability_tdma.
Extraction "schedulability_tdma.ml" schedulability_tdma. *)