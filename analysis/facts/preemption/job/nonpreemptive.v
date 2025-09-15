Require Export prosa.model.job.properties.
Require Export prosa.model.schedule.nonpreemptive.
Require Export prosa.model.preemption.fully_nonpreemptive.
Require Export prosa.analysis.facts.behavior.all.

(** * Platform for Fully Non-Preemptive model *)

(** In this section, we prove that instantiation of predicate
    [job_preemptable] to the fully non-preemptive model indeed
    defines a valid preemption model. *)
Section FullyNonPreemptiveModel.

  (**  Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** We assume that jobs are fully non-preemptive. *)
  #[local] Existing Instance fully_nonpreemptive_job_model.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any non-preemptive unit-service schedule of the arrival sequence ... *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_unit_service : unit_service_proc_model PState.
  Variable sched : schedule PState.
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule  sched.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.


  (** Then, we prove that fully_nonpreemptive_model is a valid preemption model. *)
  Lemma valid_fully_nonpreemptive_model :
    valid_preemption_model arr_seq sched.
  Proof.
    move=> j _; split; [by apply/orP; left | split; [by apply/orP; right | split]].
    - move => t; rewrite /job_preemptable /fully_nonpreemptive_job_model Bool.negb_orb -lt0n; move => /andP [POS NCOMPL].
      move: (incremental_service_during _ H_unit_service _ _ _ _ POS) => [ft [/andP [_ LT] [SCHED SERV]]].
      apply H_nonpreemptive_sched with ft.
      + by apply ltnW.
      + by [].
      + rewrite /completed_by -ltnNge.
        move: NCOMPL; rewrite neq_ltn; move => /orP [//|GE]; exfalso.
        move: GE; rewrite ltnNge; move => /negP GE; apply: GE.
        exact: completion.service_at_most_cost.
    - intros t NSCHED SCHED.
      rewrite /job_preemptable /fully_nonpreemptive_job_model.
      apply/orP; left.
      apply/negP; intros CONTR; move: CONTR => /negP; rewrite -lt0n; intros POS.
      move: (incremental_service_during _ H_unit_service _ _ _ _ POS) => [ft [/andP [_ LT] [SCHEDn SERV]]].
      move: NSCHED => /negP NSCHED; apply: NSCHED.
      apply H_nonpreemptive_sched with ft.
      + by rewrite -ltnS.
      + by [].
      + rewrite /completed_by -ltnNge.
        apply leq_ltn_trans with (service sched j t.+1).
        * by rewrite /service /service_during big_nat_recr //= leq_addr.
        * by apply H_completed_jobs_dont_execute.
  Qed.

  (** We also prove that under the fully non-preemptive model
      [job_max_nonpreemptive_segment j] is equal to [job_cost j] ... *)
  Lemma job_max_nps_is_job_cost :
    forall j, job_max_nonpreemptive_segment j = job_cost j.
  Proof.
    move=> j.
    rewrite /job_max_nonpreemptive_segment /lengths_of_segments
            /job_preemption_points /job_preemptable /fully_nonpreemptive_job_model.
    case: (posnP (job_cost j)) => [ZERO|POS].
    { by rewrite ZERO; compute. }
    have ->: forall n, n>0 -> [seq ρ <- index_iota 0 n.+1 | (ρ == 0) || (ρ == n)] = [:: 0; n].
    { clear; simpl; intros.
      apply/eqP; rewrite eqseq_cons; apply/andP; split=> [//|].
      have ->:  forall xs P1 P2, (forall x, x \in xs -> ~~ P1 x) -> [seq x <- xs | P1 x || P2 x] = [seq x <- xs | P2 x].
      { clear; move=> t xs P1 P2 H.
        apply eq_in_filter.
        move=> x IN. specialize (H _ IN).
          by destruct (P1 x), (P2 x).
      }
      - rewrite filter_pred1_uniq//; first by apply iota_uniq.
        by rewrite mem_iota; apply/andP; split; [|rewrite add1n].
      - intros x; rewrite mem_iota; move => /andP [POS _].
        by rewrite -lt0n.
    }
    { by rewrite /distances/= subn0 /max0/= max0n. }
    { by []. }
  Qed.

  (** ... and [job_last_nonpreemptive_segment j] is equal to [job_cost j]. *)
  Lemma job_last_nps_is_job_cost :
    forall j, job_last_nonpreemptive_segment j = job_cost j.
  Proof.
    move=> j.
    rewrite /job_last_nonpreemptive_segment /lengths_of_segments
            /job_preemption_points /job_preemptable /fully_nonpreemptive_job_model.
    case: (posnP (job_cost j)) => [ZERO|POS]; first by rewrite ZERO; compute.
    have ->: forall n, n>0 -> [seq ρ <- index_iota 0 n.+1 | (ρ == 0) || (ρ == n)] = [:: 0; n]; last by done.
    { clear; simpl; intros.
      apply/eqP; rewrite eqseq_cons; apply/andP; split=> [//|].
      have ->:  forall xs P1 P2, (forall x, x \in xs -> ~~ P1 x) -> [seq x <- xs | P1 x || P2 x] = [seq x <- xs | P2 x].
      { clear; move=> t xs P1 P2 H.
        apply eq_in_filter.
        move=> x IN. specialize (H _ IN).
          by destruct (P1 x), (P2 x).
      }
      - rewrite filter_pred1_uniq //; first by apply iota_uniq.
        by rewrite mem_iota; apply/andP; split; [|rewrite add1n].
      - intros x; rewrite mem_iota; move => /andP [POS _].
        by rewrite -lt0n.
    }
    { by rewrite /distances/= subn0. }
  Qed.

End FullyNonPreemptiveModel.
Global Hint Resolve valid_fully_nonpreemptive_model : basic_rt_facts.

(** In this section, we prove the equivalence between no preemptions and a non-preemptive schedule. *)
Section NoPreemptionsEquivalence.

  (** Consider any type of jobs with preemption points. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any type of schedule. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** We prove that no preemptions in a schedule is equivalent to a non-preemptive schedule. *)
  Lemma no_preemptions_equiv_nonpreemptive :
    (forall j t, ~~preempted_at sched j t) <-> nonpreemptive_schedule sched.
  Proof.
    split.
    { move=> NOT_PREEMPTED j t t'.
      elim: t'; first by rewrite leqn0 => /eqP ->.
      move=> t' IH LE_tt' SCHEDULED INCOMP.
      apply contraT => NOT_SCHEDULED'.
      move: LE_tt'. rewrite leq_eqVlt => /orP [/eqP EQ |];
        first by move: NOT_SCHEDULED' SCHEDULED; rewrite -EQ => /negP //.
      rewrite ltnS => LEQ.
      have SCHEDULED': scheduled_at sched j t'
        by apply IH, (incompletion_monotonic _ _ _ t'.+1) => //.
      move: (NOT_PREEMPTED j t'.+1).
      rewrite /preempted_at -pred_Sn -andbA negb_and => /orP [/negP //|].
      rewrite negb_and => /orP [/negPn|/negPn].
      - by move: INCOMP => /negP.
      - by move: NOT_SCHEDULED' => /negP. }
    { move => NONPRE j t.
      apply contraT => /negPn /andP [/andP [SCHED_PREV INCOMP] NOT_SCHED].
      have SCHED: scheduled_at sched j t
        by apply: (NONPRE j t.-1 t) => //; apply leq_pred.
      contradict NOT_SCHED.
      apply /negP.
      by rewrite Bool.negb_involutive.
    }
  Qed.

End NoPreemptionsEquivalence.
