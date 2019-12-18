Require Import prosa.classic.util.all.
Require Import prosa.classic.model.time prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority
               prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.arrival.curves.bounds.
Require Import prosa.classic.analysis.uni.arrival_curves.workload_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Module RBF.
 
  Import Job Time ArrivalSequence ArrivalCurves TaskArrival Priority MaxArrivalsWorkloadBound.

  (* In this section, we prove some properties of Request Bound Functions (RBF). *)
  Section RBFProperties.
    
    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
         
    (* Consider an FP policy that indicates a higher-or-equal priority relation,
       and assume that the relation is reflexive and transitive. *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.

    (* Let tsk be any task. *)
    Variable tsk: Task.

    (* Let max_arrivals be a proper arrival curve for task tsk, i.e.,  
       [max_arrival tsk] is (1) an arrival bound of tsk, and (2) it is 
       a monotonic function that equals 0 for the empty interval delta = 0. *)
    Variable max_arrivals: Task -> time -> nat.
    Hypothesis H_proper_arrival_curve:
      proper_arrival_curve job_task arr_seq max_arrivals tsk.

    (* Let's define some local names for clarity. *)
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.

    (* We prove that [task_rbf 0] is equal to 0. *)
    Lemma task_rbf_0_zero:
      task_rbf 0 = 0.
    Proof.
      rewrite /task_rbf /task_request_bound_function.
      apply/eqP; rewrite muln_eq0; apply/orP; right; apply/eqP.
        by move: H_proper_arrival_curve => [_ [T _]]; apply T. 
    Qed.
    
    (* We prove that task_rbf is monotone. *)
    Lemma task_rbf_monotone:
      monotone task_rbf leq.
    Proof.
      rewrite /monotone; intros.
      rewrite /task_rbf /task_request_bound_function leq_mul2l.
      apply/orP; right.
        by move: H_proper_arrival_curve => [_ T]; apply T.
    Qed.      
    
    (* Consider any job j of tsk. *)
    Variable j: Job.
    Hypothesis H_j_arrives: arrives_in arr_seq j.
    Hypothesis H_job_of_tsk: job_task j = tsk.
     
    (* Then we prove that task_rbf 1 is greater than or equal to task cost. *)
    Lemma task_rbf_1_ge_task_cost:
      task_rbf 1 >= task_cost tsk.
    Proof.
      have ALT: forall n, n = 0 \/ n > 0.
      { by clear; intros n; destruct n; [left | right]. }
      specialize (ALT (task_cost tsk)); destruct ALT as [Z | POS]; first by rewrite Z. 
      rewrite leqNgt; apply/negP; intros CONTR.
      move: H_proper_arrival_curve => [ARRB _].
      specialize (ARRB (job_arrival j) (job_arrival j + 1)).
      feed ARRB; first by rewrite leq_addr.
      rewrite addKn in ARRB.
      move: CONTR; rewrite /task_rbf /task_request_bound_function; move => CONTR.
      move: CONTR; rewrite -{2}[task_cost tsk]muln1 ltn_mul2l; move => /andP [_ CONTR].
      move: CONTR; rewrite -addn1 -{3}[1]add0n leq_add2r leqn0; move => /eqP CONTR.
      move: ARRB; rewrite CONTR leqn0 eqn0Ngt; move => /negP T; apply: T.
      rewrite /num_arrivals_of_task -has_predT. 
      rewrite /arrivals_of_task_between /is_job_of_task.
      apply/hasP; exists j; last by done.
      rewrite /jobs_arrived_between addn1 big_nat_recl; last by done. 
      rewrite big_geq ?cats0; last by done.
      rewrite mem_filter.
      apply/andP; split.
      - by apply/eqP.
      - move: H_j_arrives => [t ARR].
        move: (ARR) => CONS.
        apply H_arrival_times_are_consistent in CONS.
          by rewrite CONS.
    Qed.
    
  End RBFProperties.

End RBF. 