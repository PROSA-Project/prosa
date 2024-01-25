From HB Require Import structures.
Require Export prosa.implementation.definitions.arrival_bound.
Require Export prosa.model.task.arrival.curves.
Require Export prosa.model.priority.numeric_fixed_priority.

(** * Implementation of Tasks and Jobs *)

(** This file provides reference implementations of the notions of "tasks" and
    "jobs" that can be used to meet the hypotheses on which many of the analyses
    in Prosa are based.

    Note that their use is entirely optional: clients of Prosa may choose to use
    these types or implement their own notions of "tasks" and "jobs". *)

(** ** Implementation of a Concrete Task *)


(** A task comprises of an id, a cost, an arrival bound, a deadline
    and a priority. *)
Structure concrete_task :=
  { task_id: nat (* for uniqueness *)
  ; task_cost: nat
  ; task_arrival: task_arrivals_bound
  ; task_deadline: instant
  ; task_priority : nat
  }.

(** To make it compatible with ssreflect, we define a decidable
    equality for concrete tasks. *)
Definition task_eqdef (t1 t2: concrete_task) :=
  (task_id t1 == task_id t2)
  && (task_cost t1 == task_cost t2)
  && (task_arrival t1 == task_arrival t2)
  && (task_deadline t1 == task_deadline t2)
  && (task_priority t1 == task_priority t2).

(** Next, we prove that [task_eqdef] is indeed an equality, ... *)
Lemma eqn_task : Equality.axiom task_eqdef.
Proof.
  unfold Equality.axiom; intros x y.
  destruct (task_eqdef x y) eqn:EQ.
  { apply ReflectT.
    unfold task_eqdef in *.
    move: EQ => /andP [/andP [/andP [/andP [/eqP ID /eqP COST] /eqP PER] /eqP DL] /eqP PRIO].
    by destruct x, y; simpl in *; subst. }
  { apply ReflectF.
    unfold task_eqdef, not in * => BUG.
    apply negbT in EQ.
    repeat rewrite negb_and in EQ.
    destruct x, y.
    move: BUG => [ID COST PER DL PRIO].
    rewrite ID COST PER DL PRIO //= in EQ.
    by subst; rewrite !eq_refl in EQ.
  }
Qed.

(** ..., which allows instantiating the canonical structure for [concrete_task : eqType]. *)
HB.instance Definition _  := hasDecEq.Build concrete_task eqn_task.


(** ** Implementation of a Concrete Job *)


(** A job comprises of an id, an arrival time, a cost, a deadline and the
    task it belongs to. *)
Record concrete_job :=
  { job_id: nat
  ; job_arrival: instant
  ; job_cost: nat
  ; job_deadline: instant
  ; job_task: concrete_task : eqType
  }.

(** For convenience, we define a function that converts each possible arrival
    bound (periodic, sporadic, and arrival-curve prefix) into an arrival-curve
    prefix... *)
Definition get_arrival_curve_prefix tsk :=
  match task_arrival tsk with
  | Periodic p => inter_arrival_to_prefix p
  | Sporadic m => inter_arrival_to_prefix m
  | ArrivalPrefix steps => steps
  end.

(** ... and define the "arrival bound" concept for concrete tasks. *)
Definition concrete_max_arrivals tsk Δ :=
  extrapolated_arrival_curve (get_arrival_curve_prefix tsk) Δ.

(** To make it compatible with ssreflect, we define a decidable
    equality for concrete jobs. *)
Definition job_eqdef (j1 j2: concrete_job) :=
  (job_id j1 == job_id j2)
  && (job_arrival j1 == job_arrival j2)
  && (job_cost j1 == job_cost j2)
  && (job_deadline j1 == job_deadline j2)
  && (job_task j1 == job_task j2).

(** Next, we prove that [job_eqdef] is indeed an equality, ... *)
Lemma eqn_job : Equality.axiom job_eqdef.
Proof.
  unfold Equality.axiom; intros x y.
  destruct (job_eqdef x y) eqn:EQ.
  { apply ReflectT; unfold job_eqdef in *.
    move: EQ => /andP [/andP [/andP [/andP [/eqP ID /eqP ARR] /eqP COST] /eqP DL] /eqP TASK].
    by destruct x, y; simpl in *; subst. }
  { apply ReflectF.
    unfold job_eqdef, not in *; intro BUG.
    apply negbT in EQ; rewrite negb_and in EQ.
    destruct x, y.
    rewrite negb_and in EQ.
    move: EQ => /orP [EQ | /eqP TASK].
    - move: EQ => /orP [EQ | /eqP DL].
      + rewrite negb_and in EQ.
        move: EQ => /orP [EQ | /eqP COST].
        * rewrite negb_and in EQ.
          move: EQ => /orP [/eqP ID | /eqP ARR].
          ** by apply ID; inversion BUG.
          ** by apply ARR; inversion BUG.
        * by apply COST; inversion BUG.
      + by apply DL; inversion BUG.
    - by apply TASK; inversion BUG. }
Qed.

(** ... which allows instantiating the canonical structure for [concrete_job : eqType].*)
HB.instance Definition _  := hasDecEq.Build concrete_job eqn_job.

(** ** Instances for Concrete Jobs and Tasks. *)

(** In the following, we connect the concrete task and job types defined above
    to the generic Prosa interfaces for task and job parameters. *)
Section Parameters.

  (** First, we connect the above definition of tasks with the
      generic Prosa task-parameter interfaces. *)
  Let Task := concrete_task : eqType.
  #[global,program] Instance TaskCost : TaskCost Task := task_cost.
  #[global,program] Instance TaskPriority : TaskPriority Task := task_priority.
  #[global,program] Instance TaskDeadline : TaskDeadline Task := task_deadline.
  #[global,program] Instance ConcreteMaxArrivals : MaxArrivals Task := concrete_max_arrivals.

  (** Second, we do the same for the above definition of job. *)
  Let Job := concrete_job : eqType.
  #[global,program] Instance JobTask : JobTask Job Task := job_task.
  #[global,program] Instance JobArrival : JobArrival Job := job_arrival.
  #[global,program] Instance JobCost : JobCost Job := job_cost.

End Parameters.
