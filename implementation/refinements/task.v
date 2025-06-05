Require Export prosa.analysis.definitions.request_bound_function.
Require Export prosa.implementation.facts.extrapolated_arrival_curve.
Require Export prosa.implementation.refinements.arrival_bound.
Require Export prosa.implementation.definitions.task.

(** ** Task Refinement *)

(** In this module, we define a generic version of concrete task and
    prove that it is isomorphic to the standard, natural-number-based
    definition. *)

(** We begin by defining the generic task type. *)
Section Definitions.

  (** In this file, we refine the Prosa standard implementation of
        jobs and tasks. *)
  Definition Task := concrete_task : eqType.
  Definition Job := concrete_job : eqType.

  (** Consider a generic type [T], for which all the basic arithmetical
        operations, ordering, and equality are defined. *)
  Context `{T : Type}.
  Context `{!zero_of T, !one_of T, !sub_of T, !add_of T, !mul_of T,
            !div_of T, !mod_of T, !eq_of T, !leq_of T, !lt_of T}.
  Context `{!eq_of (seq T)}.
  Context `{!eq_of (@task_arrivals_bound_T T)}.

  (** We define a generic task type that uses [T] for each numerical value. *)
  Structure task_T :=
    {
    task_id_T: T;
    task_cost_T: T;
    task_arrival_T: @task_arrivals_bound_T T;
    task_deadline_T: T;
    task_priority_T: T
    }.

  (** Further, we define the equality for two generic tasks as the equality
        of each attribute. *)
  Definition task_eqdef_T (t1 t2: task_T) :=
    (task_id_T t1 == task_id_T t2)%C &&
    (task_cost_T t1 == task_cost_T t2)%C &&
    (task_arrival_T t1 == task_arrival_T t2)%C &&
    (task_deadline_T t1 == task_deadline_T t2)%C &&
    (task_priority_T t1 == task_priority_T t2)%C.

  (** Next, we define a helper function that convert a minimum inter-arrival time
        to an arrival curve prefix. *)
  Definition inter_arrival_to_extrapolated_arrival_curve_T (p : T) : T * seq (T * T) := (p, [::(1, 1)])%C.

  (** Further, we define the arrival bound of a task as, possibly, (1) periodic,
        (2) sporadic, or (3) an arrival curve. Note that, internally, the workload
        bound is always represented by an arrival curve. *)
  Definition get_extrapolated_arrival_curve_T (tsk : task_T) : T * seq (T * T) :=
    match task_arrival_T tsk with
    | Periodic_T p => inter_arrival_to_extrapolated_arrival_curve_T p
    | Sporadic_T m => inter_arrival_to_extrapolated_arrival_curve_T m
    | ArrivalPrefix_T steps => steps
    end.

  (** With the previous definition in place, we define the workload bound... *)
  Definition ConcreteMaxArrivals_T (tsk : task_T) (Δ : T): T :=
    extrapolated_arrival_curve_T (get_extrapolated_arrival_curve_T tsk) Δ.

  (** ... and the task request-bound function. *)
  Definition task_rbf_T (tsk : task_T) (Δ : T) :=
    (task_cost_T tsk * ConcreteMaxArrivals_T tsk Δ)%C.

  (** Further, we define a valid arrival bound as (1) a positive
        minimum inter-arrival time/period, or (2) a valid arrival curve prefix. *)
  Definition valid_arrivals_T (tsk : task_T) : bool :=
    match task_arrival_T tsk with
    | Periodic_T p => (1 <= p)%C
    | Sporadic_T m => (1 <= m)%C
    | ArrivalPrefix_T ac_prefix_vec => valid_extrapolated_arrival_curve_T ac_prefix_vec
    end.

  (** Next, we define a helper function that yields the horizon of the arrival
        curve prefix of a task ... *)
  Definition get_horizon_of_task_T (tsk : task_T) : T :=
    horizon_of_T (get_extrapolated_arrival_curve_T tsk).

  (** ... another one that yields the time steps of the arrival curve, ... *)
  Definition get_time_steps_of_task_T (tsk : task_T) : seq T :=
    time_steps_of_T (get_extrapolated_arrival_curve_T tsk).

  (** ... a function that yields the same time steps, offset by δ, ... *)
  Definition time_steps_with_offset_T tsk δ :=
    [seq t + δ | t <- get_time_steps_of_task_T tsk]%C.

  (** ... and a generalization of the previous function that repeats the time
        steps for each given offset. *)
  Definition repeat_steps_with_offset_T (tsk : task_T) (offsets : seq T): seq T :=
    (flatten (map (time_steps_with_offset_T tsk) offsets))%C.
End Definitions.

(** In this section, we define two functions used to convert from a generic task
      to the standard task definition, and vice-versa. *)
Section Translation.

  (** First, we define the function that maps a generic task to a natural-number
        task... *)
  Definition taskT_to_task (tsk: @task_T N) : Task :=
    match tsk with
    | {| task_id_T := id;
         task_cost_T := cost;
         task_arrival_T := arrival_bound;
         task_deadline_T := deadline;
         task_priority_T := priority |}
      =>
      {| task.task_id := nat_of_bin id;
         task.task_cost := nat_of_bin cost;
         task.task_arrival := task_abT_to_task_ab arrival_bound;
         task.task_deadline := nat_of_bin deadline;
         task.task_priority := nat_of_bin priority |}
    end.

  (** ... and its function relationship. *)
  Definition Rtask := fun_hrel taskT_to_task.

  (** Finally, we define the converse function, mapping a natural-number
        task to a generic one. *)
  Definition task_to_taskT (tsk: Task) : @task_T N :=
    match tsk with
    | {| task.task_id := id;
         task.task_cost := cost;
         task.task_arrival := arrival_bound;
         task.task_deadline := deadline;
         task.task_priority := priority |}
      =>
      {| task_id_T := bin_of_nat id;
         task_cost_T := bin_of_nat cost;
         task_arrival_T := task_ab_to_task_abT arrival_bound;
         task_deadline_T := bin_of_nat deadline;
         task_priority_T := bin_of_nat priority |}
    end.

End Translation.

(** In this fairly technical section, we prove a series of refinements
      aimed to be able to convert between a standard natural-number task
      and a generic task. *)
Section Theory.

  (** We prove the refinement of the constructor functions. *)
  Global Instance refine_task :
    refines (Rnat ==> Rnat ==> Rtask_ab ==> Rnat ==> Rnat ==> Rtask)%rel
            Build_concrete_task Build_task_T.
  Proof.
    by rewrite refinesE=> _ i <- _ c <- _ p <- _ d <- _ pr <-.
  Qed.

  (** Next, we prove a refinement for the task id. *)
  Global Instance refine_task_id :
    refines (Rtask ==> Rnat)%rel task_id task_id_T.
  Proof.
    rewrite refinesE => _ tsk <-.
    by destruct tsk.
  Qed.

  (** Next, we prove a refinement for the task cost. *)
  Global Instance refine_task_cost :
    refines (Rtask ==> Rnat)%rel task_cost task_cost_T.
  Proof.
    rewrite refinesE => _ tsk <-.
    by destruct tsk.
  Qed.

  (** Next, we prove a refinement for the task arrival. *)
  Global Instance refine_task_arrival :
    refines (Rtask ==> Rtask_ab)%rel task_arrival task_arrival_T.
  Proof.
    rewrite refinesE => _ tsk <-.
    by destruct tsk.
  Qed.

  (** Next, we prove a refinement for the task deadline. *)
  Global Instance refine_task_deadline :
    refines (Rtask ==> Rnat)%rel task_deadline task_deadline_T.
  Proof.
    rewrite refinesE => _ tsk <-.
    by destruct tsk.
  Qed.

  (** Next, we prove a refinement for the task priority. *)
  Global Instance refine_task_priority :
    refines (Rtask ==> Rnat)%rel task_priority task_priority_T.
  Proof.
    rewrite refinesE => _ tsk <-.
    by destruct tsk.
  Qed.

  (** Next, we prove a refinement for the task period. *)
  Global Instance refine_Periodic :
    refines (Rnat ==> Rtask_ab)%rel Periodic Periodic_T.
  Proof.
    rewrite refinesE => t t' Rt.
    compute in Rt; subst.
    by compute.
  Qed.

  (** Next, we prove a refinement for the task minimum inter-arrival time. *)
  Global Instance refine_Sporadic :
    refines (Rnat ==> Rtask_ab)%rel Sporadic Sporadic_T.
  Proof.
    rewrite refinesE => t t' Rt.
    compute in Rt; subst.
    by compute.
  Qed.

  (** Next, we prove a refinement for the task id conversion. *)
  Local Instance refine_task' :
    refines (unify (A:= task_T) ==> Rtask)%rel taskT_to_task id.
  Proof.
    rewrite refinesE => tsk tsk' UNI.
    by have UNIT := unify_rel; last specialize (UNIT _ _ _ UNI); subst tsk'; clear UNI.
  Qed.

  (** Finally, we prove a refinement for the id conversion applied to a list of tasks. *)
  Local Instance refine_task_set' :
    refines (unify (A:= seq task_T) ==> list_R Rtask)%rel (map taskT_to_task) id.
  Proof.
    rewrite refinesE => ts ts' UNI.
    have UNIT := unify_rel; last specialize (UNIT _ _ _ UNI); subst ts'; clear UNI.
    induction ts as [ | tsk ts].
    - by simpl; apply nil_R.
    - simpl; apply cons_R; last by done.
      by unfold Rtask, fun_hrel.
  Qed.

End Theory.


(** * Task Declaration Notation *)

(** For convenience, we define a simple notation for declaring concrete tasks
    using numbers represented in binary, which is used in POET's certificates to
    improve readability. *)
From Stdlib Require Export NArith.

(** We declare a notation to declare a task instance of type [Task_T]. *)
Notation "'[' 'TASK' 'id:' c1 'cost:' c2 'deadline:' c3 'arrival:' c4 'priority:' c5 ']'" :=
  {| task_id_T := c1
  ;  task_cost_T := c2
  ;  task_deadline_T := c3
  ;  task_arrival_T := c4
  ;  task_priority_T := c5
  |} (at level 6, right associativity, only parsing).

(** As a special case, we declare a variant of the above notation that does not
    require specifying a priority (which is meaningless in EDF certificates). *)
Notation "'[' 'TASK' 'id:' c1 'cost:' c2 'deadline:' c3 'arrival:' c4 ']'" :=
  [TASK id: c1 cost: c2 deadline: c3 arrival: c4 priority: 0%N]
    (at level 6, right associativity, only parsing).

(** In the following, we further provide specialized versions of the two cases
    above for periodic and sporadic tasks. *)

(** (1) A shorthand notation for periodic tasks with numeric priorities. *)
Notation "'[' 'PERIODIC-TASK' 'id:' c1 'cost:' c2 'deadline:' c3 'period:' c4 'priority:' c5 ']'"
  := [TASK id: c1 cost: c2 deadline: c3 arrival: Periodic_T c4 priority: c5 ]
       (at level 6, right associativity, only parsing).

(** (2) shorthand notation for periodic tasks without numeric priorities. *)
Notation "'[' 'PERIODIC-TASK' 'id:' c1 'cost:' c2 'deadline:' c3 'period:' c4 ']'"
  := [PERIODIC-TASK id: c1 cost: c2 deadline: c3 period: c4 priority: 0%N]
       (at level 6, right associativity, only parsing).

(** (3) A shorthand notation for simple sporadic tasks with numeric priorities
        described only by a minimum inter-arrival separation. *)
Notation "'[' 'SPORADIC-TASK' 'id:' c1 'cost:' c2 'deadline:' c3 'separation:' c4 'priority:' c5 ']'"
  := [TASK id: c1 cost: c2 deadline: c3 arrival: Sporadic_T c4 priority: c5]
     (at level 6, right associativity, only parsing).

(** (4) A shorthand notation for simple sporadic tasks without numeric priorities
        described only by a minimum inter-arrival separation. *)
Notation "'[' 'SPORADIC-TASK' 'id:' c1 'cost:' c2 'deadline:' c3 'separation:' c4 ']'"
  := [SPORADIC-TASK id: c1 cost: c2 deadline: c3 separation: c4 priority: 0%N]
       (at level 6, right associativity, only parsing).

(** Finally, we provide a simplified notation for specifying arrival curves. *)
Notation "'[' 'CURVE' 'horizon:' c1 'steps:' c2 ']'"
  := (ArrivalPrefix_T (c1, c2))
    (at level 6, right associativity, only parsing).
