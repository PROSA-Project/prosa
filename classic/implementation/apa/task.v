Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.task.
Require Import rt.model.schedule.apa.affinity.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

Module ConcreteTask.

  Import Time SporadicTaskset Affinity.
  
  Section Defs.

    (* Let num_cpus be the number of processors. *)
    Context {num_cpus: nat}.
    
    (* Definition of a concrete task. *)
    Record concrete_task :=
    {
      task_id: nat; (* for uniqueness *)  
      task_cost: time;
      task_period: time;
      task_deadline: time;
      task_affinity: affinity num_cpus
    }.

    (* To make it compatible with ssreflect, we define a decidable
       equality for concrete tasks. *)
    Definition task_eqdef (t1 t2: concrete_task) :=
      (task_id t1  == task_id t2) &&
      (task_cost t1 == task_cost t2) &&
      (task_period t1 == task_period t2) &&
      (task_deadline t1 == task_deadline t2) &&
      (task_affinity t1 == task_affinity t2).

    (* Next, we prove that task_eqdef is indeed an equality, ... *)
    Lemma eqn_task : Equality.axiom task_eqdef.
    Proof.
      unfold Equality.axiom; intros x y.
      destruct (task_eqdef x y) eqn:EQ.
      {
        apply ReflectT.
        unfold task_eqdef in *.
        move: EQ => /andP [/andP [/andP [/andP [/eqP ID /eqP COST]] /eqP PERIOD] /eqP DL] /eqP ALPHA.
        by destruct x, y; simpl in *; subst. 
      }
      {
        apply ReflectF.
        unfold task_eqdef, not in *; intro BUG.
        apply negbT in EQ; rewrite negb_and in EQ.
        destruct x, y.
        rewrite negb_and in EQ.
        move: EQ => /orP [EQ | /eqP DL]; last by apply DL; inversion BUG.
        move: EQ => /orP [EQ | /eqP PERIOD]; last by apply PERIOD; inversion BUG.
        rewrite negb_and in EQ.
        move: EQ => /orP [EQ | /eqP COST]; last by apply COST; inversion BUG.
        rewrite negb_and in EQ.
        move: EQ => /orP [/eqP ID | /eqP ALPHA]; last by apply ALPHA; inversion BUG.
        by apply ID; inversion BUG.
      }
    Qed.

    (* ..., which allows instantiating the canonical structure. *)
    Canonical concrete_task_eqMixin := EqMixin eqn_task.
    Canonical concrete_task_eqType := Eval hnf in EqType concrete_task concrete_task_eqMixin.

  End Defs.

  Section ConcreteTaskset.

    (* Let num_cpus be the number of processors. *)
    Variable num_cpus: nat.
    
    Definition concrete_taskset :=
      taskset_of (@concrete_task_eqType num_cpus).

  End ConcreteTaskset.
  
End ConcreteTask.