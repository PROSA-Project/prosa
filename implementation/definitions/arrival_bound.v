Require Export prosa.implementation.definitions.extrapolated_arrival_curve.

(** * Implementation of a Task's Arrival Bound *)

(** In this file, we define a reference implementation of the notion of a task's
    arrival bound.

    Note that its use is entirely optional: clients of Prosa may choose to use
    this type or implement their own notion of arrival bounds. *)

(** A task's arrival bound is an inductive type comprised of three types of
    arrival patterns: (a) periodic, characterized by a period between consequent
    activation of a task, (b) sporadic, characterized by a minimum inter-arrival
    time, or (c) arrival-curve prefix, characterized by a finite prefix of an
    arrival curve. *)
Inductive task_arrivals_bound :=
| Periodic : nat -> task_arrivals_bound
| Sporadic : nat -> task_arrivals_bound
| ArrivalPrefix : ArrivalCurvePrefix -> task_arrivals_bound.

(** To make it compatible with ssreflect, we define a decidable
    equality for arrival bounds. *)
Definition task_arrivals_bound_eqdef (tb1 tb2 : task_arrivals_bound) :=
  match tb1, tb2 with
  | Periodic p1, Periodic p2 => p1 == p2
  | Sporadic s1, Sporadic s2 => s1 == s2
  | ArrivalPrefix s1, ArrivalPrefix s2 => s1 == s2
  | _, _ => false
  end.

(** Next, we prove that [task_eqdef] is indeed an equality, ... *)
Lemma eqn_task_arrivals_bound : Equality.axiom task_arrivals_bound_eqdef.
Proof.
  intros x y.
  destruct (task_arrivals_bound_eqdef x y) eqn:EQ.
  { apply ReflectT; destruct x, y.
    all: try by move: EQ => /eqP EQ; subst.
  }
  { apply ReflectF; destruct x, y.
    all: try by move: EQ => /eqP EQ.
    all: by move: EQ => /neqP; intros NEQ1 NEQ2; apply NEQ1; inversion NEQ2.
  }
Qed.

(** ..., which allows instantiating the canonical structure for [[eqType of task_arrivals_bound]]. *)
Canonical task_arrivals_bound_eqMixin := EqMixin eqn_task_arrivals_bound.
Canonical task_arrivals_bound_eqType := Eval hnf in EqType task_arrivals_bound task_arrivals_bound_eqMixin.

