Require Export prosa.analysis.facts.behavior.all.
Require Export prosa.analysis.facts.model.ideal_schedule.
Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.model.schedule.nonpreemptive.

(** Furthermore, we assume the fully non-preemptive job model. *)
Require Import prosa.model.preemption.fully_nonpreemptive.

(** * Platform for Fully Non-Preemptive model *)
(** In this section, we prove that instantiation of predicate
    [job_preemptable] to the fully non-preemptive model indeed
    defines a valid preemption model. *)
Section FullyNonPreemptiveModel.
  
  (**  Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
   
  (** Next, consider any non-preemptive ideal uniprocessor schedule of
      this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_nonpreemptive_sched : nonpreemptive_schedule  sched.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.  
  
  (** For simplicity, let's define some local names. *)
  Let job_pending := pending sched.
  Let job_completed_by := completed_by sched.
  Let job_scheduled_at := scheduled_at sched.
  
  (** Then, we prove that fully_nonpreemptive_model is a valid preemption model. *)
  Lemma valid_fully_nonpreemptive_model:
    valid_preemption_model arr_seq sched.
  Proof.
    intros j; split; [by apply/orP; left | split; [by apply/orP; right | split]].
    - move => t; rewrite /job_preemptable /fully_nonpreemptive_model Bool.negb_orb -lt0n; move => /andP [POS NCOMPL].
      move: (incremental_service_during _ _ _ _ _ POS) => [ft [/andP [_ LT] [SCHED SERV]]].
      apply H_nonpreemptive_sched with ft.
      + by apply ltnW. 
      + by done. 
      + rewrite /completed_by -ltnNge.
        move: NCOMPL; rewrite neq_ltn; move => /orP [LE|GE]; [by done | exfalso].
        move: GE; rewrite ltnNge; move => /negP GE; apply: GE.
        apply completion.service_at_most_cost; eauto 2 with basic_facts.
    - intros t NSCHED SCHED.
      rewrite /job_preemptable /fully_nonpreemptive_model.
      apply/orP; left. 
      apply/negP; intros CONTR; move: CONTR => /negP; rewrite -lt0n; intros POS. 
      move: (incremental_service_during _ _ _ _ _ POS) => [ft [/andP [_ LT] [SCHEDn SERV]]].
      move: NSCHED => /negP NSCHED; apply: NSCHED.
      apply H_nonpreemptive_sched with ft.
      + by rewrite -ltnS.
      + by done. 
      + rewrite /completed_by -ltnNge.
        apply leq_ltn_trans with (service sched j t.+1).  
        * by rewrite /service /service_during big_nat_recr //= leq_addr. 
        * rewrite -addn1; apply leq_trans with (service sched j t.+2). 
          have <-: (service_at sched j t.+1) = 1.
          { by apply/eqP; rewrite eqb1 -scheduled_at_def. }
            by rewrite -big_nat_recr //=.
            by apply completion.service_at_most_cost; eauto 2 with basic_facts.
  Qed.

  (** We also prove that under the fully non-preemptive model
      [job_max_nonpreemptive_segment j] is equal to [job_cost j] ... *)
  Lemma job_max_nps_is_job_cost:
    forall j, job_max_nonpreemptive_segment j = job_cost j.
  Proof.
    intros.
    rewrite /job_max_nonpreemptive_segment /lengths_of_segments
            /job_preemption_points /job_preemptable /fully_nonpreemptive_model.
    case: (posnP (job_cost j)) => [ZERO|POS].
    { by rewrite ZERO; compute. }
    have ->: forall n, n>0 -> [seq ρ <- index_iota 0 n.+1 | (ρ == 0) || (ρ == n)] = [:: 0; n].
    { clear; simpl; intros.
      apply/eqP; rewrite eqseq_cons; apply/andP; split; first by done.
      have ->:  forall xs P1 P2, (forall x, x \in xs -> ~~ P1 x) -> [seq x <- xs | P1 x || P2 x] = [seq x <- xs | P2 x].
      { clear; intros.
        apply eq_in_filter.
        intros ? IN. specialize (H _ IN).
          by destruct (P1 x), (P2 x).
      }
      rewrite filter_pred1_uniq; first by done.
      - by apply iota_uniq. 
      - by rewrite mem_iota; apply/andP; split; [done | rewrite add1n].
      - intros x; rewrite mem_iota; move => /andP [POS _].
          by rewrite -lt0n.
    } 
    by rewrite /distances; simpl; rewrite subn0 /max0; simpl; rewrite max0n.
      by done.
  Qed.
  
  (** ... and [job_last_nonpreemptive_segment j] is equal to [job_cost j]. *)
  Lemma job_last_nps_is_job_cost:
    forall j, job_last_nonpreemptive_segment j = job_cost j.
  Proof.
    intros.
    rewrite /job_last_nonpreemptive_segment /lengths_of_segments
            /job_preemption_points /job_preemptable /fully_nonpreemptive_model.
    case: (posnP (job_cost j)) => [ZERO|POS].
    { by rewrite ZERO; compute. }
    have ->: forall n, n>0 -> [seq ρ <- index_iota 0 n.+1 | (ρ == 0) || (ρ == n)] = [:: 0; n].
    { clear; simpl; intros.
      apply/eqP; rewrite eqseq_cons; apply/andP; split; first by done.
      have ->:  forall xs P1 P2, (forall x, x \in xs -> ~~ P1 x) -> [seq x <- xs | P1 x || P2 x] = [seq x <- xs | P2 x].
      { clear; intros.
        apply eq_in_filter.
        intros ? IN. specialize (H _ IN).
          by destruct (P1 x), (P2 x).
      }
      rewrite filter_pred1_uniq; first by done.
      - by apply iota_uniq. 
      - by rewrite mem_iota; apply/andP; split; [done | rewrite add1n].
      - intros x; rewrite mem_iota; move => /andP [POS _].
          by rewrite -lt0n.
    } 
      by rewrite /distances; simpl; rewrite subn0 /last0; simpl. 
      by done.
  Qed.
  
End FullyNonPreemptiveModel.
Hint Resolve valid_fully_nonpreemptive_model : basic_facts.
