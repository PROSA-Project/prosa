Require Export prosa.model.aggregate.workload.
Require Export prosa.model.aggregate.service_of_jobs.
Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.facts.model.ideal_schedule.
Require Import prosa.model.processor.ideal.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** * Lemmas about Service Received by Sets of Jobs *)
(** In this file, we establish basic facts about the service received by _sets_ of jobs. *)

(** To begin with, we provide some basic properties of service
   of a set of jobs in case of a generic scheduling model. *)
Section GenericModelLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence with consistent arrivals, .... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and any schedule of this arrival sequence ...*)
  Variable sched : schedule PState.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let P be any predicate over jobs. *)
  Variable P : Job -> bool.

  (** Let's define some local names for clarity. *)
  Let arrivals_between := arrivals_between arr_seq.

  (** In this section, we prove that the service received by any set of jobs
     is upper-bounded by the corresponding workload. *)
  Section ServiceBoundedByWorkload.

    (** Let jobs denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** Assume that the processor model is a unit service model. I.e.,
       no job ever receives more than one unit of service at any time. *)
    Hypothesis H_unit_service : unit_service_proc_model PState.

    (** Then, we prove that the service received by those jobs is no larger than their workload. *)
    Lemma service_of_jobs_le_workload:
      forall t1 t2,
        service_of_jobs sched P jobs t1 t2 <= workload_of_jobs P jobs.
    Proof.
      intros t1 t2.
      apply leq_sum; intros j _.
        by apply cumulative_service_le_job_cost.
    Qed.

  End ServiceBoundedByWorkload.

  (** In this section we prove a few facts about splitting
     the total service of a set of jobs. *)
  Section ServiceCat.

    (** We show that the total service of jobs released in a time interval <<[t1,t2)>>
       during [t1,t2) is equal to the sum of:
       (1) the total service of jobs released in time interval [t1, t) during time [t1, t)
       (2) the total service of jobs released in time interval [t1, t) during time [t, t2)
       and (3) the total service of jobs released in time interval [t, t2) during time [t, t2). *)
    Lemma service_of_jobs_cat_scheduling_interval :
      forall t1 t2 t,
        t1 <= t <= t2 ->
        service_of_jobs sched P (arrivals_between t1 t2) t1 t2
        = service_of_jobs sched P (arrivals_between t1 t) t1 t
          + service_of_jobs sched P (arrivals_between t1 t) t t2
          + service_of_jobs sched P (arrivals_between t t2) t t2.
    Proof.
      move => t1 t2 t /andP [GEt LEt].
      rewrite /arrivals_between (arrivals_between_cat _ _ t) //.
      rewrite {1}/service_of_jobs big_cat //=.
      rewrite exchange_big //= (@big_cat_nat _ _ _ t) //=;
              rewrite [in X in X + _ + _]exchange_big //= [in X in _ + X + _]exchange_big //=.
      apply/eqP; rewrite -!addnA eqn_add2l eqn_add2l.
      rewrite exchange_big //= (@big_cat_nat _ _ _ t) //= [in X in _ + X]exchange_big //=.
      rewrite -[service_of_jobs _ _ _ _ _]add0n /service_of_jobs eqn_add2r.
      rewrite big_nat_cond big1 //.
      move => x /andP [/andP [GEi LTi] _].
      rewrite big_seq_cond big1 //.
      move => j /andP [ARR Ps].
      apply service_before_job_arrival_zero with H0; auto.
      eapply in_arrivals_implies_arrived_between in ARR; eauto 2.
        by move: ARR => /andP [N1 N2]; apply leq_trans with t.
    Qed.

    (** We show that the total service of jobs released in a time interval <<[t1,t2)>>
       during [t,t2) is equal to the sum of:
       (1) the total service of jobs released in a time interval [t1,t) during [t,t2)
       and (2) the total service of jobs released in a time interval [t,t2) during [t,t2). *)
    Lemma service_of_jobs_cat_arrival_interval :
      forall t1 t2 t,
        t1 <= t <= t2 ->
        service_of_jobs sched P (arrivals_between t1 t2) t t2 =
        service_of_jobs sched P (arrivals_between t1 t) t t2 +
        service_of_jobs sched P (arrivals_between t t2) t t2.
    Proof.
      move => t1 t2 t /andP [GEt LEt].
      apply/eqP;rewrite eq_sym; apply/eqP.
      rewrite /arrivals_between [in X in _ = X](arrivals_between_cat _ _ t) //.
        by rewrite {3}/service_of_jobs -big_cat //=.
    Qed.

  End ServiceCat.

End GenericModelLemmas.

(** In this section, we prove some properties about service
   of sets of jobs for ideal uni-processor model. *)
Section IdealModelLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
    
  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let P be any predicate over jobs. *)
  Variable P : Job -> bool.

  (** Let's define some local names for clarity. *)
  Let arrivals_between := arrivals_between arr_seq.
  Let completed_by := completed_by sched.

  (** We prove that if the total service within some time interval <<[t1,t2)>> 
      is smaller than [t2-t1], then there is an idle time instant t ∈ [[t1,t2)]. *)
  Lemma low_service_implies_existence_of_idle_time :
    forall t1 t2,
      service_of_jobs sched predT (arrivals_between 0 t2) t1 t2 < t2 - t1 ->
      exists t, t1 <= t < t2 /\ is_idle sched t.
  Proof.
    intros ? ? SERV.
    destruct (t1 <= t2) eqn:LE; last first.
    { move: LE => /negP/negP; rewrite -ltnNge.
      move => LT; apply ltnW in LT; rewrite -subn_eq0 in LT.
        by rewrite (eqbool_to_eqprop LT) ltn0 in SERV.
    }
    have EX: exists δ, t2 = t1 + δ.
    { by exists (t2 - t1); rewrite subnKC // ltnW. }
    move: EX => [δ EQ]; subst t2; clear LE.
    rewrite {3}[t1 + δ]addnC -addnBA // subnn addn0 in SERV.
    rewrite /service_of_jobs exchange_big //= in SERV.
    apply sum_le_summation_range in SERV.
    move: SERV => [x [/andP [GEx LEx] L]].
    exists x; split; first by apply/andP; split.
    apply/negPn; apply/negP; intros NIDLE.
    unfold is_idle in NIDLE.
    destruct(sched x) eqn:SCHED; last by done.
    move: SCHED => /eqP SCHED; clear NIDLE; rewrite -scheduled_at_def/= in SCHED.
    move: L => /eqP; rewrite -sum_nat_eq0_nat; move => /allP L.
    specialize (L s); feed L. 
    { unfold arrivals_between.
      eapply arrived_between_implies_in_arrivals; eauto 2.
        by apply H_jobs_must_arrive_to_execute in SCHED; apply leq_ltn_trans with x.
    } 
      by move: L; simpl;rewrite eqb0; move => /eqP EQ.
  Qed.
  
  (** In this section, we prove that the service received by any set of jobs
     is upper-bounded by the corresponding interval length. *)
  Section ServiceOfJobsIsBoundedByLength.

    (** Let [jobs] denote any (finite) set of jobs. *)
    Variable jobs : seq Job.

    (** Assume that the sequence of [jobs] is a set. *)
    Hypothesis H_no_duplicate_jobs : uniq jobs.

    (** We prove that the overall service of [jobs] at a single time instant is at most [1]. *)
    Lemma service_of_jobs_le_1:
      forall t, \sum_(j <- jobs | P j) service_at sched j t <= 1.
    Proof.
      intros t.
      case SCHED: (sched t) => [j | ]; simpl.
      { case ARR: (j \in jobs).
        { rewrite (big_rem j) //=; simpl.
          rewrite /service_at /scheduled_at SCHED; simpl.
          rewrite -[1]addn0 leq_add //.
          - by rewrite eq_refl; case (P j).
          - rewrite leqn0 big1_seq; first by done.
            move => j' /andP [_ ARRj'].
            apply/eqP; rewrite eqb0.
            apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
            inversion CONTR; subst j'; clear CONTR.
            rewrite rem_filter in ARRj'; last by done.
            move: ARRj'; rewrite mem_filter; move => /andP [/negP CONTR _].
              by apply: CONTR.
        }
        { apply leq_trans with 0; last by done.
          rewrite leqn0 big1_seq; first by done.
          move => j' /andP [_ ARRj'].
          apply/eqP; rewrite eqb0.
          rewrite /scheduled_at SCHED.
          apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
          inversion CONTR; clear CONTR.
            by subst j'; rewrite ARR in ARRj'.
        }
      }
      { apply leq_trans with 0; last by done.
        rewrite leqn0 big1_seq; first by done.
        move => j' /andP [_ ARRj'].
          by rewrite /service_at /scheduled_at SCHED.
      }
    Qed.

    (** Then, we prove that the service received by those jobs is no larger than their workload. *)
    Corollary service_of_jobs_le_length_of_interval:
      forall (t : instant) (Δ : duration),
        service_of_jobs sched P jobs t (t + Δ) <= Δ.
    Proof.
      intros.
      have EQ: \sum_(t <= x < t + Δ) 1 = Δ.
      { by rewrite big_const_nat iter_addn mul1n addn0 -{2}[t]addn0 subnDl subn0. }
      rewrite -{2}EQ {EQ}.
      rewrite /service_of_jobs/service_during/service_at exchange_big //=.
      rewrite leq_sum //.
      move => t' _.
        by apply service_of_jobs_le_1.
    Qed.

    (** Similar lemma holds for two instants. *)
    Corollary service_of_jobs_le_length_of_interval':
      forall (t1 t2 : instant),
        service_of_jobs sched P jobs t1 t2 <= t2 - t1.
    Proof.
      intros.
      have <-: \sum_(t1 <= x < t2) 1 = t2 - t1.
      { by rewrite big_const_nat iter_addn mul1n addn0. } 
      rewrite /service_of_jobs exchange_big //=.
      rewrite leq_sum //.
      move => t' _.
      have SE :=  service_of_jobs_le_1 t'.
      eapply leq_trans; last by eassumption.
        by rewrite leq_sum //.
    Qed.
    
  End ServiceOfJobsIsBoundedByLength.

  (** In this section, we introduce a connection between the cumulative
     service, cumulative workload, and completion of jobs. *)
  Section WorkloadServiceAndCompletion.

    (** Consider an arbitrary time interval <<[t1, t2)>>. *)
    Variables t1 t2 : instant.

    (** Let jobs be a set of all jobs arrived during <<[t1, t2)>>. *)
    Let jobs := arrivals_between t1 t2.

    (** Next, we consider some time instant [t_compl]. *)
    Variable t_compl : instant.

    (** And state the proposition that all jobs are completed by time
       [t_compl]. Next we show that this proposition is equivalent to
       the fact that [workload of jobs = service of jobs]. *)
    Let all_jobs_completed_by t_compl :=
      forall j, j \in jobs -> P j -> completed_by j t_compl.

    (** First, we prove that if the workload of [jobs] is equal to the service
       of [jobs], then any job in [jobs] is completed by time [t_compl]. *)
    Lemma workload_eq_service_impl_all_jobs_have_completed:
      workload_of_jobs P jobs =
      service_of_jobs sched P jobs t1 t_compl ->
      all_jobs_completed_by t_compl.
    Proof.
      unfold jobs; intros EQ j ARR Pj; move: (ARR) => ARR2.
      apply in_arrivals_implies_arrived_between in ARR; last by done.
      move: ARR => /andP [T1 T2].
      have F1: forall a b, (a < b) || (a >= b).
      { by intros; destruct (a < b) eqn:EQU; apply/orP;
          [by left |right]; apply negbT in EQU; rewrite leqNgt. }
      move: (F1 t_compl t1) => /orP [LT | GT].
      { rewrite /service_of_jobs /service_during in EQ.
        rewrite exchange_big big_geq //= in EQ; last by rewrite ltnW.
        rewrite /workload_of_jobs in EQ.
        rewrite (big_rem j) ?Pj //= in EQ.
        move: EQ => /eqP; rewrite addn_eq0; move => /andP [CZ _].
        unfold completed_by, service.completed_by.
          by move: CZ => /eqP CZ; rewrite CZ.
      }
      { unfold workload_of_jobs, service_of_jobs in EQ; unfold completed_by, service.completed_by.
        rewrite /service -(service_during_cat _ _ _ t1); last by apply/andP; split.
        rewrite cumulative_service_before_job_arrival_zero // add0n.
        rewrite <- sum_majorant_eqn with (F1 := fun j => service_during sched j t1 t_compl)
                                        (xs := arrivals_between t1 t2) (P := P); try done.
        intros; apply cumulative_service_le_job_cost; auto using ideal_proc_model_provides_unit_service.
      }
    Qed.

    (** And vice versa, the fact that any job in [jobs] is completed by time [t_compl]
       implies that the workload of [jobs] is equal to the service of [jobs]. *)
    Lemma all_jobs_have_completed_impl_workload_eq_service:
      all_jobs_completed_by t_compl ->
      workload_of_jobs P jobs =
      service_of_jobs sched P jobs t1 t_compl.
    Proof.
      unfold jobs; intros COMPL.
      have F: forall j t, t <= t1 -> j \in arrivals_between t1 t2 -> service_during sched j 0 t = 0.
      { intros j t LE ARR.
        eapply in_arrivals_implies_arrived_between in ARR; eauto 2; move: ARR => /andP [GE LT].
        eapply cumulative_service_before_job_arrival_zero; eauto 2.
          by apply leq_trans with t1. }
      destruct (t_compl <= t1) eqn:EQ.
      { unfold service_of_jobs. unfold service_during.
        rewrite exchange_big //=.
        rewrite big_geq; last by done.
        rewrite /workload_of_jobs big1_seq //.
        move => j /andP [Pj ARR].
        specialize (COMPL _ ARR Pj).
        rewrite <- F with (j := j) (t := t_compl); try done.
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        - by apply COMPL.
        - by apply service_at_most_cost; auto using ideal_proc_model_provides_unit_service.
      }
      apply/eqP; rewrite eqn_leq; apply/andP; split; first last.
      { by apply service_of_jobs_le_workload; auto using ideal_proc_model_provides_unit_service. }
      { unfold workload_of_jobs, service_of_jobs.
        rewrite big_seq_cond [X in _ <= X]big_seq_cond.
        rewrite leq_sum //.
        move => j /andP [ARR Pj].
        specialize (COMPL _ ARR Pj).
        rewrite -[service_during _ _ _ _ ]add0n.
        rewrite -(F j t1); try done.
        rewrite -(big_cat_nat) //=; last first.
        move: EQ =>/negP /negP; rewrite -ltnNge; move => EQ.
          by apply ltnW.
      }
    Qed.

    (** Using the lemmas above, we prove equivalence. *)
    Corollary all_jobs_have_completed_equiv_workload_eq_service:
      all_jobs_completed_by t_compl <->
      workload_of_jobs P jobs =
      service_of_jobs sched P jobs t1 t_compl.
    Proof.
      split.
      - by apply all_jobs_have_completed_impl_workload_eq_service.
      - by apply workload_eq_service_impl_all_jobs_have_completed.
    Qed.

  End WorkloadServiceAndCompletion. 

End IdealModelLemmas.
