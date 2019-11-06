Require Import rt.util.all.
Require Import rt.model.arrival.basic.task.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

Module ConcreteTask.

  Import SporadicTaskset.
  
  Section Defs.
    
    (* Definition of a concrete task. *)
    Record concrete_task :=
    {
      task_id: nat; (* for uniqueness *)  
      task_cost: nat;
      task_period: nat;
      task_deadline: nat;
      task_jitter: nat
    }.

    (* To make it compatible with ssreflect, we define a decidable
       equality for concrete tasks. *)
    Definition task_eqdef (t1 t2: concrete_task) :=
      (task_id t1 == task_id t2) &&
      (task_cost t1 == task_cost t2) &&
      (task_period t1 == task_period t2) &&
      (task_deadline t1 == task_deadline t2) &&
      (task_jitter t1 == task_jitter t2).

    (* Next, we prove that task_eqdef is indeed an equality, ... *)
    Lemma eqn_task : Equality.axiom task_eqdef.
    Proof.
      unfold Equality.axiom; intros x y.
      destruct (task_eqdef x y) eqn:EQ.
      {
        apply ReflectT.
        unfold task_eqdef in *.
        move: EQ => /andP [/andP [/andP [/andP [/eqP ID /eqP COST] /eqP PERIOD] /eqP DL] /eqP JITTER].
        by destruct x, y; simpl in *; subst. 
      }
      {
        apply ReflectF.
        unfold task_eqdef, not in *; intro BUG.
        apply negbT in EQ; rewrite negb_and in EQ.
        destruct x, y.
        rewrite negb_and in EQ.
        move: EQ => /orP [/orP [EQ | /eqP DL] | /eqP JITTER]; last by apply JITTER; inversion BUG.
        rewrite negb_and in EQ.
        move: EQ => /orP [EQ | /eqP DL]; last by apply DL; inversion BUG.
        rewrite negb_and in EQ.
        move: EQ => /orP [/eqP ID | /eqP PERIOD]; last by apply PERIOD; inversion BUG.
        by apply ID; inversion BUG.
        by apply DL; inversion BUG.
      }
    Qed.

    (* ..., which allows instantiating the canonical structure. *)
    Canonical concrete_task_eqMixin := EqMixin eqn_task.
    Canonical concrete_task_eqType := Eval hnf in EqType concrete_task concrete_task_eqMixin.

  End Defs.

  Section ConcreteTaskset.

    Definition concrete_taskset :=
      taskset_of concrete_task_eqType.

  End ConcreteTaskset.
  
End ConcreteTask.