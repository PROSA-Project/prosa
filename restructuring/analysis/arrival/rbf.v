Require Import rt.util.all.
Require Export rt.restructuring.behavior.all.
Require Import rt.restructuring.analysis.definitions.job_properties.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.aggregate.task_arrivals.
Require Import rt.restructuring.model.arrival.arrival_curves.
Require Import rt.restructuring.analysis.arrival.workload_bound.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Request Bound Functions (RBF) *)
(** In this section, we prove some properties of Request Bound Functions (RBF). *)
Section RequestBoundFunctions.
  
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  
  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent:
    consistent_arrival_times arr_seq.

  (** Let tsk be any task. *)
  Variable tsk : Task.

  (** Let max_arrivals be a family of valid arrival curves, i.e., for any task tsk in ts 
     [max_arrival tsk] is (1) an arrival bound of tsk, and (2) it is a monotonic function 
     that equals 0 for the empty interval delta = 0. *)
  Context `{MaxArrivals Task}.
  Hypothesis H_valid_arrival_curve : valid_arrival_curve tsk (max_arrivals tsk).
  Hypothesis H_is_arrival_curve : respects_max_arrivals arr_seq tsk (max_arrivals tsk).
  
  (** Let's define some local names for clarity. *)
  Let task_rbf := task_request_bound_function tsk.

  (** We prove that [task_rbf 0] is equal to 0. *)
  Lemma task_rbf_0_zero:
    task_rbf 0 = 0.
  Proof.
    rewrite /task_rbf /task_request_bound_function.
    apply/eqP; rewrite muln_eq0; apply/orP; right; apply/eqP.
      by move: H_valid_arrival_curve => [T1 T2].
  Qed.
  
  (** We prove that task_rbf is monotone. *)
  Lemma task_rbf_monotone:
    monotone task_rbf leq.
  Proof.
    rewrite /monotone; intros ? ? LE.
    rewrite /task_rbf /task_request_bound_function leq_mul2l.
    apply/orP; right.
      by move: H_valid_arrival_curve => [_ T]; apply T.
  Qed.      
  
  (** Consider any job j of tsk. This guarantees that 
     there exists at least one job of task tsk. *)
  Variable j : Job.
  Hypothesis H_j_arrives : arrives_in arr_seq j.
  Hypothesis H_job_of_tsk : job_task j = tsk.
  
  (** Then we prove that task_rbf 1 is greater than or equal to task cost. *)
  Lemma task_rbf_1_ge_task_cost:
    task_rbf 1 >= task_cost tsk.
  Proof.
    have ALT: forall n, n = 0 \/ n > 0.
    { by clear; intros n; destruct n; [left | right]. }
    specialize (ALT (task_cost tsk)); destruct ALT as [Z | POS]; first by rewrite Z. 
    rewrite leqNgt; apply/negP; intros CONTR.
    move: H_is_arrival_curve => ARRB.
    specialize (ARRB (job_arrival j) (job_arrival j + 1)).
    feed ARRB; first by rewrite leq_addr.
    rewrite addKn in ARRB.
    move: CONTR; rewrite /task_rbf /task_request_bound_function; move => CONTR.
    move: CONTR; rewrite -{2}[task_cost tsk]muln1 ltn_mul2l; move => /andP [_ CONTR].
    move: CONTR; rewrite -addn1 -{3}[1]add0n leq_add2r leqn0; move => /eqP CONTR.
    move: ARRB; rewrite CONTR leqn0 eqn0Ngt; move => /negP T; apply: T.
    rewrite /number_of_task_arrivals -has_predT. 
    rewrite /task_arrivals_between.
    apply/hasP; exists j; last by done.
    rewrite /arrivals_between addn1 big_nat_recl; last by done. 
    rewrite big_geq ?cats0; last by done.
    rewrite mem_filter.
    apply/andP; split.
    - by apply/eqP.
    - move: H_j_arrives => [t ARR].
      move: (ARR) => CONS.
      apply H_arrival_times_are_consistent in CONS.
        by rewrite CONS.
  Qed.
  
End RequestBoundFunctions.