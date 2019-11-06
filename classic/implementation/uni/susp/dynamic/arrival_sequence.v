Require Import rt.util.all.
Require Import rt.model.arrival.basic.arrival_sequence rt.model.arrival.basic.task rt.model.arrival.basic.task_arrival rt.model.arrival.basic.job.
Require Import rt.implementation.uni.susp.dynamic.task
               rt.implementation.uni.susp.dynamic.job.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq div.

Module ConcreteArrivalSequence.

  Import Job ArrivalSequence ConcreteTask ConcreteJob SporadicTaskset TaskArrival.

  Section PeriodicArrivals.

    Variable ts: concrete_taskset.

    (* At any time arr_time, we release Some job of tsk if t is a multiple of the period,
       otherwise we release None. *)
    Definition add_job (arr_time: time) (tsk: concrete_task) :=
      if task_period tsk %| arr_time  then
        Some (Build_concrete_job (arr_time %/ task_period tsk) arr_time
                                 (task_cost tsk) (task_deadline tsk) tsk)
      else
        None.

    (* The arrival sequence at any time t is simply the partial map of add_job. *)
    Definition periodic_arrival_sequence (t: time) := pmap (add_job t) ts.

  End PeriodicArrivals.

  Section Proofs.

    (* Let ts be any concrete task set with valid parameters. *)
    Variable ts: concrete_taskset.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    
    (* Regarding the periodic arrival sequence built from ts, we prove that...*)
    Let arr_seq := periodic_arrival_sequence ts.

    (* ... arrival times are consistent, ... *)
    Theorem periodic_arrivals_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Proof.
      move => j t ARRj.
      rewrite /arrives_at mem_pmap in ARRj.
      move: ARRj => /mapP ARRj; destruct ARRj as [tsk IN SOME].
      by unfold add_job in *; desf.
    Qed.

    (* ... every job comes from the task set, ... *)
    Theorem periodic_arrivals_all_jobs_from_taskset:
      forall j,
        arrives_in arr_seq j ->
        job_task j \in ts.
    Proof.
      move => j [t ARRj].
      rewrite mem_pmap in ARRj.
      move: ARRj => /mapP ARRj; destruct ARRj as [tsk IN SOME].
      by unfold add_job in *; desf.
    Qed.

    (* ..., jobs have valid parameters, ... *)
    Theorem periodic_arrivals_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    Proof.
      rename H_valid_task_parameters into PARAMS.
      unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
      move => j [t ARRj].
      rewrite mem_pmap in ARRj; move: ARRj => /mapP [tsk IN SOME].
      unfold add_job in SOME; desf.
      specialize (PARAMS tsk IN); des.
      unfold valid_sporadic_job, valid_realtime_job, job_cost_positive.
      by repeat split; try (by done); apply leqnn.
    Qed.

    (* ... job arrivals satisfy the sporadic task model, ... *)
    Theorem periodic_arrivals_are_sporadic:
      sporadic_task_model task_period job_arrival job_task arr_seq.
    Proof.
      move => j j' /eqP DIFF [arr ARR] [arr' ARR'] SAMEtsk LE.
      rewrite eqE /= /job_eqdef negb_and /= SAMEtsk eq_refl orbF in DIFF.
      rewrite 2!mem_pmap in ARR ARR'.
      move: ARR ARR' => /mapP [tsk_j INj SOMEj] /mapP [tsk_j' INj' SOMEj'].
      unfold add_job in SOMEj, SOMEj'; desf; simpl in *;
      move: Heq0 Heq => /dvdnP [k DIV] /dvdnP [k' DIV'].
      {
        rewrite DIV DIV' -mulSnr.
        rewrite leq_eqVlt in LE; move: LE => /orP [/eqP EQ | LESS].
        { 
          exfalso; move: DIFF => /negP DIFF; apply DIFF.
          by subst; rewrite EQ !eq_refl.
        }
        subst; rewrite leq_mul2r; apply/orP; right.
        by rewrite ltn_mul2r in LESS; move: LESS => /andP [_ LT].
      }
    Qed.

    (* ... and the arrival sequence has no duplicate jobs. *)
    Theorem periodic_arrivals_is_a_set:
      arrival_sequence_is_a_set arr_seq.
    Proof.
      intros t.
      unfold arr_seq, periodic_arrival_sequence.
      apply (pmap_uniq) with (g := job_task); last by destruct ts.
      by unfold add_job, ocancel; intro tsk; desf.
    Qed.
      
  End Proofs.
  
End ConcreteArrivalSequence.