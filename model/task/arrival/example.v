Require Import prosa.model.task.arrival.periodic.
Require Import prosa.model.task.arrival.periodic_as_sporadic.
Require Import prosa.model.task.arrival.sporadic_as_curve.
Require Import prosa.model.task.arrival.curve_as_rbf.

(** * Arrival Model Conversion

  This file demonstrates the automatic conversion of arrival
  models. In particular, we show how a set of periodic tasks can be
  interpreted also as (1) sporadic tasks with minimum inter-arrival
  times, (2) sporadic tasks with arrival curves, and (3) request-bound
  functions.  *)

Section AutoArrivalModelConversion.

  (** Consider periodic tasks ... *)
  Context {Task : TaskType} `{PeriodicModel Task}.

  (** ... and their corresponding jobs. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task}.

  (** Given a set of such periodic tasks  ... *)
  Variable ts : TaskSet Task.

  (** ... and a valid arrival sequence, ...*)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... if the tasks are valid periodic tasks, ...*)
  Hypothesis H_respects : taskset_respects_periodic_task_model arr_seq ts.
  Hypothesis H_valid_periods : valid_periods ts.

  (** ... then we can automatically interpret them also as satisfying
      other arrival models, as we demonstrate in the following. *)

  (** ** Periodic Tasks as Sporadic Tasks *)

  (** The tasks satisfy the sporadic validity constraint... *)
  Goal valid_taskset_inter_arrival_times ts.
  Proof. by []. Qed.

  (** ... and arrival sequence is legal under the sporadic task
      model. *)
  Goal taskset_respects_sporadic_task_model ts arr_seq.
  Proof. by []. Qed.

  (** ** Periodic Tasks as Arrival Curves *)

  (** The tasks satisfy the arrival-curve validity constraint... *)
  Goal valid_taskset_arrival_curve ts max_arrivals.
  Proof. by []. Qed.

  (** ... and the arrival sequence is legal under the arrival-curve
      model. *)
  Goal taskset_respects_max_arrivals arr_seq ts.
  Proof. by []. Qed.

  (** ** Periodic Tasks as RBFs *)

    (** RBFs combine information about job costs and job arrivals. We consider two
        cases: tasks with (1) traditional scalar WCETs and (2) cumulative WCET(n)
        bounds. *)

  Section ScalarWCET.

    (** Assuming that each task has a WCET... *)
    Context `{TaskCost Task}.

    (** ... and that jobs are compliant with the WCET, ... *)
    Context `{JobCost Job}.
    Hypothesis H_valid_costs : arrivals_have_valid_job_costs arr_seq.

    (** ... the tasks satisfy the RBF validity constraint... *)
    Goal valid_taskset_request_bound_function ts max_request_bound.
    Proof. by []. Qed.

    (** ... and the arrival sequence is legal under the RBF model. *)
    Goal taskset_respects_max_request_bound arr_seq ts.
    Proof.
      (* NB: Ideally, we would like this to be solved via [by done], too, but
         Prosa's [done] tactic calls [eauto] with a search depth of 4, which is
         not enough here. However, bumping the search depth of the default
         [done] to 5 causes massive compilation slowdowns elsewhere, so we have
         to call [eauto] explicitly here. *)
      by eauto 5 with basic_rt_facts.
    Qed.

  End ScalarWCET.


  (** The same upper-RBF conversion also works when tasks provide a native
      WCET(n) bound rather than only a scalar WCET. *)
  Section CumulativeWCET.

    (** Assume that each task has a valid cumulative cost bound ... *)
    Context `{TaskCumulativeCost Task}.
    Hypothesis H_valid_cumulative_cost : taskset_has_valid_cumulative_cost_bounds ts.

    (** ... that upper-bounds the cost of consecutive jobs. *)
    Context `{JobCost Job}.
    Hypothesis H_respects_cumulative_cost : taskset_respects_cumulative_cost_bounds arr_seq ts.

    (** Then the tasks satisfy the RBF validity constraint. *)
    Goal valid_taskset_request_bound_function ts max_request_bound.
    Proof. by []. Qed.

    (** And the arrival sequence is legal under the RBF model. *)
    Goal taskset_respects_max_request_bound arr_seq ts.
    Proof. by []. Qed.

  End CumulativeWCET.

  (** Thanks to type-class resolution, all conversions from more restrictive to
      less restrictive task models happen transparently and the necessary proofs
      are found automatically.

      Of course, it is possible to start from sporadic tasks or tasks with
      arrival curves, too. *)

End AutoArrivalModelConversion.
