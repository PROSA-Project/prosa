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
  Proof. by rt_auto. Qed.

  (** ... and arrival sequence is legal under the sporadic task
      model. *)
  Goal taskset_respects_sporadic_task_model ts arr_seq.
  Proof. by rt_auto. Qed.

  (** ** Periodic Tasks as Arrival Curves *)

  (** The tasks satisfy the arrival-curve validity constraint... *)
  Goal valid_taskset_arrival_curve ts max_arrivals.
  Proof. by rt_auto. Qed.

  (** ... and the arrival sequence is legal under the arrival-curve
      model. *)
  Goal taskset_respects_max_arrivals arr_seq ts.
  Proof. by rt_eauto. Qed.

  (** ** Periodic Tasks as RBFs *)

  (** Assuming that each task has a WCET... *)
  Context `{TaskCost Task}.

  (** ... and that jobs are compliant with the WCET, ... *)
  Context `{JobCost Job}.
  Hypothesis H_valid_costs : jobs_have_valid_job_costs.

  (** ... the tasks satisfy the RBF validity constraint... *)
  Goal valid_taskset_request_bound_function ts (task_max_rbf max_arrivals).
  Proof. by rt_auto. Qed.

  (** ... and the arrival sequence is legal under the RBF model. *)
  Goal taskset_respects_max_request_bound arr_seq ts.
  Proof. by rt_eauto. Qed.

  (** Thanks to type-class resolution, all conversions from more
      restrictive to less restrictive task model happen transparently
      and the and necessary proofs are found automatically.

      Of course, it is possible to start from sporadic tasks or tasks
      with arrival curves, too. *)

End AutoArrivalModelConversion.
