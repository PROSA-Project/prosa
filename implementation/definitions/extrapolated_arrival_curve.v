From mathcomp Require Export ssreflect ssrbool eqtype ssrnat div seq path fintype bigop.
Require Export prosa.behavior.time.
Require Export prosa.util.all.

(** This file introduces an implementation of arrival curves via the
    periodic extension of finite _arrival-curve prefix_. An
    arrival-curve prefix is a pair comprising a horizon and a list of
    steps. The horizon defines the domain of the prefix, in which no
    extrapolation is necessary. The list of steps ([duration × value])
    describes the value changes of the corresponding arrival curve
    within the domain.

    For time instances outside of an arrival-curve prefix's domain,
    extrapolation is necessary. Therefore, past the domain,
    arrival-curve values are extrapolated assuming that the
    arrival-curve prefix is repeated with a period equal to the
    horizon.

    Note that such a periodic extension does not necessarily give the
    tightest curve, and hence it is not optimal. The advantage is
    speed of calculation: periodic extension can be done in constant
    time, whereas the optimal extension takes roughly quadratic time
    in the number of steps. *)

(** An arrival-curve prefix is defined as a pair comprised of a
    horizon and a list of steps ([duration × value]) that describe the
    value changes of the described arrival curve.

    For example, an arrival-curve prefix [(5, [:: (1, 3)])] describes
    an arrival sequence with job bursts of size [3] happening every
    [5] time instances. *)
Definition ArrivalCurvePrefix : Type := duration * seq (duration * nat).

(** Given an inter-arrival time [p] (or period [p]), the corresponding
    arrival-curve prefix can be defined as [(p, [:: (1, 1)])]. *) 
Definition inter_arrival_to_prefix (p : nat) : ArrivalCurvePrefix := (p, [:: (1, 1)]).

(** The first component of arrival-curve prefix [ac_prefix] is called horizon. *)
Definition horizon_of (ac_prefix : ArrivalCurvePrefix) := fst ac_prefix.

(** The second component of [ac_prefix] is called steps. *)
Definition steps_of (ac_prefix : ArrivalCurvePrefix) := snd ac_prefix.

(** The time steps of [ac_prefix] are the first components of the
    steps. That is, these are time instances before the horizon
    where the corresponding arrival curve makes a step. *)
Definition time_steps_of (ac_prefix : ArrivalCurvePrefix) :=
  map fst (steps_of ac_prefix).

(** The function [step_at] returns the last step ([duration ×
    value]) such that [duration ≤ t]. *)
Definition step_at (ac_prefix : ArrivalCurvePrefix) (t : duration) :=
  last (0, 0) [ seq step <- steps_of ac_prefix | fst step <= t ].

(* The function [value_at] returns the _value_ of the last step
   ([duration × value]) such that [duration ≤ t] *)
Definition value_at (ac_prefix : ArrivalCurvePrefix) (t : duration) :=
  snd (step_at ac_prefix t).

(** Finally, we define a function [extrapolated_arrival_curve] that
    performs the periodic extension of the arrival-curve prefix (and
    hence, defines an arrival curve).
    
    Value of [extrapolated_arrival_curve t] is defined as 
    [t %/ h * value_at horizon] plus [value_at (t mod horizon)]. 
    The first summand corresponds to [k] full repetitions of the 
    arrival-curve prefix inside interval <<[0,t)>>. The second summand 
    corresponds to the residual change inside interval <<[k*h, t)>>. *)
Definition extrapolated_arrival_curve (ac_prefix : ArrivalCurvePrefix) (t : duration) :=
  let h := horizon_of ac_prefix in
  t %/ h * value_at ac_prefix h + value_at ac_prefix (t %% h).

(** In the following section, we define a few validity predicates. *)
Section ValidArrivalCurvePrefix.

  (** Horizon should be positive. *)
  Definition positive_horizon (ac_prefix : ArrivalCurvePrefix) :=
    horizon_of ac_prefix > 0.

  (** Horizon should bound time steps. *)
  Definition large_horizon (ac_prefix : ArrivalCurvePrefix) :=
    forall s, s \in time_steps_of ac_prefix -> s <= horizon_of ac_prefix.

  (** There should be no infinite arrivals; that is, [value_at 0 = 0]. *)
  Definition no_inf_arrivals (ac_prefix : ArrivalCurvePrefix) :=
    value_at ac_prefix 0 = 0.

  (** Bursts must be specified; that is, [steps_of] should contain a
      pair [(ε, b)]. *)
  Definition specified_bursts (ac_prefix : ArrivalCurvePrefix) :=
    ε \in time_steps_of ac_prefix.

  (** Steps should be strictly increasing both in time steps and values. *)
  Definition ltn_steps a b := (fst a < fst b) && (snd a < snd b).
  Definition sorted_ltn_steps (ac_prefix : ArrivalCurvePrefix) :=
    sorted ltn_steps (steps_of ac_prefix).

  (** The conjunction of the 5 afore-defined properties defines a
      valid arrival-curve prefix. *)
  Definition valid_arrival_curve_prefix (ac_prefix : ArrivalCurvePrefix) :=
    positive_horizon ac_prefix
    /\ large_horizon ac_prefix
    /\ no_inf_arrivals ac_prefix
    /\ specified_bursts ac_prefix
    /\ sorted_ltn_steps ac_prefix.

  (** We also define a predicate for non-decreasing order that is
      more convenient for proving some of the claims. *)
  Definition leq_steps a b := (fst a <= fst b) && (snd a <= snd b).
  Definition sorted_leq_steps (ac_prefix : ArrivalCurvePrefix) :=
    sorted leq_steps (steps_of ac_prefix).

End ValidArrivalCurvePrefix.
