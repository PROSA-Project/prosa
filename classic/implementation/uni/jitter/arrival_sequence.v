Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.arrival_sequence prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.task_arrival prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.implementation.uni.jitter.task
               prosa.classic.implementation.uni.jitter.job.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq div.

Module ConcreteArrivalSequence.

  Import Job ArrivalSequence ConcreteTask ConcreteJob SporadicTaskset TaskArrival.

  Section PeriodicArrivals.

    Variable ts: concrete_taskset.

    (* At any time t, we release Some job of tsk if t is a multiple of the period,
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

    (* We also show that job costs are bounded by task costs... *)
    Theorem periodic_arrivals_job_cost_le_task_cost:
      forall j,
        arrives_in arr_seq j ->
        job_cost j <= task_cost (job_task j).
    Proof.
      intros j [t ARRj].
      rewrite mem_pmap in ARRj.
      move: ARRj => /mapP [tsk_j INj SOMEj].
      by unfold add_job in SOMEj; desf. 
    Qed.

    (* ...and that job deadlines equal task deadlines. *)
    Theorem periodic_arrivals_job_deadline_eq_task_deadline:
      forall j,
        arrives_in arr_seq j ->
        job_deadline j = task_deadline (job_task j).
    Proof.
      intros j [t ARRj].
      rewrite mem_pmap in ARRj.
      move: ARRj => /mapP [tsk_j INj SOMEj].
      by unfold add_job in SOMEj; desf. 
    Qed.

  End Proofs.
  
End ConcreteArrivalSequence.