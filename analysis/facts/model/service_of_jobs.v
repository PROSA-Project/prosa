Require Export prosa.model.aggregate.workload.
Require Export prosa.model.aggregate.service_of_jobs.
Require Export prosa.analysis.facts.behavior.completion.


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
  Context {PState : ProcessorState Job}.

  (** ... any job arrival sequence with consistent arrivals, .... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** ... and any schedule of this arrival sequence ... *)
  Variable sched : schedule PState.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let P be any predicate over jobs. *)
  Variable P : pred Job.

  (** We show that the total service of jobs released in a time interval <<[t1,t2)>>
      during <<[t1,t2)>> is equal to the sum of:
      (1) the total service of jobs released in time interval <<[t1, t)>> during time <<[t1, t)>>
      (2) the total service of jobs released in time interval <<[t1, t)>> during time <<[t, t2)>>
      and (3) the total service of jobs released in time interval <<[t, t2)>> during time <<[t, t2)>>. *)
  Lemma service_of_jobs_cat_scheduling_interval :
      forall t1 t2 t,
        t1 <= t <= t2 ->
        service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t2
        = service_of_jobs sched P (arrivals_between arr_seq t1 t) t1 t
          + service_of_jobs sched P (arrivals_between arr_seq t1 t) t t2
          + service_of_jobs sched P (arrivals_between arr_seq t t2) t t2.
    Proof.
      move => t1 t2 t /andP [GEt LEt].
      rewrite (arrivals_between_cat _ _ t) //.
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
      apply: service_before_job_arrival_zero => //.
      eapply in_arrivals_implies_arrived_between in ARR; eauto 2.
      by move: ARR => /andP [N1 N2]; apply leq_trans with t.
    Qed.

    (** We show that the total service of jobs released in a time interval <<[t1, t2)>>
       during <<[t, t2)>> is equal to the sum of:
       (1) the total service of jobs released in a time interval <<[t1, t)>> during <<[t, t2)>>
       and (2) the total service of jobs released in a time interval <<[t, t2)>> during <<[t, t2)>>. *)
    Lemma service_of_jobs_cat_arrival_interval :
      forall t1 t2 t,
        t1 <= t <= t2 ->
        service_of_jobs sched P (arrivals_between arr_seq t1 t2) t t2 =
        service_of_jobs sched P (arrivals_between arr_seq t1 t) t t2 +
        service_of_jobs sched P (arrivals_between arr_seq t t2) t t2.
    Proof.
      move => t1 t2 t /andP [GEt LEt].
      apply/eqP;rewrite eq_sym; apply/eqP.
      rewrite [in X in _ = X](arrivals_between_cat _ _ t) //.
      by rewrite {3}/service_of_jobs -big_cat //=.
    Qed.

    (** In the following, we consider an arbitrary sequence of jobs [jobs]. *)
    Variable jobs : seq Job.

    (** Also, consider an interval <<[t1, t2)>>... *)
    Variable t1 t2 : instant.

    (** ...and two additional predicates [P1] and [P2]. *) 
    Variable P1 P2 : pred Job.

    (** For brevity, in the following comments we denote a subset of [jobs]
        satisfying a predicate [P] by [{jobs | P}]. *)

    (** First, we prove that the service received by [{jobs | P1}] can be split
        into: (1) the service received by [{jobs | P1 ∧ P2}] and (2) the service
        received by the a subset [{jobs | P1 ∧ ¬ P2}]. *)
    Lemma service_of_jobs_case_on_pred :
      service_of_jobs sched P1 jobs t1 t2 =
        service_of_jobs sched (fun j => P1 j && P2 j) jobs t1 t2
        + service_of_jobs sched (fun j => P1 j && ~~ P2 j) jobs t1 t2.
    Proof.
      rewrite /service_of_jobs big_mkcond //=.
      rewrite [in X in _ = X + _]big_mkcond //=.
      rewrite [in X in _ = _ + X]big_mkcond //=.
      rewrite -big_split; apply eq_big_seq; intros j IN.
      by destruct (P1 _), (P2 _); simpl; lia.
    Qed.

    (** We show that the service received by [{jobs | P}] is equal to the
        difference between the total service received by [jobs] and the service
        of [{jobs | ¬ P}]. *)
    Lemma service_of_jobs_negate_pred :
      service_of_jobs sched P jobs t1 t2 =
        total_service_of_jobs_in sched jobs t1 t2 - service_of_jobs sched (fun j => ~~ P j) jobs t1 t2.
    Proof.
      rewrite /total_service_of_jobs_in /service_of_jobs.
      rewrite big_mkcond [in X in _ = X - _]big_mkcond [in X in _ = _ - X]big_mkcond //=.
      rewrite -sumnB; last by move=> j _; case: (P j).
      apply: eq_big_seq => j IN.
      by case: (P j) => //=; lia.
    Qed.

    (** We show that [service_of_jobs] is monotone with respect to the
        predicate. That is, given the fact [∀ j ∈ jobs: P1 j ==> P2 j], we show
        that the service of [{jobs | P1}] is bounded by the service of [{jobs | P2}]. *)
    Lemma service_of_jobs_pred_impl :
      (forall j : Job, j \in jobs -> P1 j -> P2 j) -> 
      service_of_jobs sched P1 jobs t1 t2 <= service_of_jobs sched P2 jobs t1 t2.
    Proof. by intros IMPL; apply leq_sum_seq_pred; eauto. Qed.

    (** Similarly, we show that if [P1] is equivalent to [P2], then the service
        of [{jobs | P1}] is equal to the service of [{jobs | P2}]. *)
    Lemma service_of_jobs_equiv_pred :
      {in jobs, P1 =1 P2} -> 
      service_of_jobs sched P1 jobs t1 t2 = service_of_jobs sched P2 jobs t1 t2.
    Proof.
      intros * EQUIV.
      rewrite /service_of_jobs !big_mkcond [in X in _ = X]big_mkcond //=; apply: eq_big_seq.
      intros j IN; specialize (EQUIV j IN); simpl in EQUIV; rewrite EQUIV; clear EQUIV.
      by case: (P2 j) => //.
    Qed.

    (** Next, we show an auxiliary lemma that allows us to change the order of
        summation.

        Recall that [service_of_jobs] is defined as a sum over all jobs in
        [jobs] of <<[service_during j [t1,t2)]>>. We show that [service_of_jobs]
        over an interval <<[t1,t2)>> is equal to the sum over individual time
        instances (in <<[t1,t2)>>) of [service_of_jobs_at].

        In other words, we show that <<[∑_{j ∈ jobs} ∑_{t \in [t1,t2)} service
        of j at t]>> is equal to <<[∑_{t \in [t1,t2)} ∑_{j ∈ jobs} service of j
        at t]>>. *)
    Lemma service_of_jobs_sum_over_time_interval :
      service_of_jobs sched P jobs t1 t2
      = \sum_(t1 <= t < t2) service_of_jobs_at sched P jobs t.
    Proof. by apply exchange_big. Qed.

    (** We show that service of [{jobs | false}] is equal to 0. *) 
    Lemma service_of_jobs_pred0 :
      service_of_jobs sched pred0 jobs t1 t2 = 0.
    Proof. by apply big_pred0. Qed.

    (** More generally, if none of the jobs inside [jobs] is scheduled
        at time [t] or satisfies [P], then total service of [jobs] at
        time [t] is equal to 0. *) 
    Lemma service_of_jobs_nsched_or_unsat :
      forall (t : instant),
        (forall j, j \in jobs -> ~~ (P j && scheduled_at sched j t)) -> 
        service_of_jobs_at sched P jobs t = 0.
    Proof.
      intros ? ALL.
      elim: jobs ALL => [|a l IHl] ALL.
      - by rewrite /service_of_jobs_at big_nil.
      - feed IHl.
        { by intros j' IN; apply ALL; rewrite in_cons; apply/orP; right. }
        rewrite /service_of_jobs_at big_cons; rewrite /service_of_jobs_at in IHl.
        destruct (P a) eqn: Pa => [|//].
        rewrite IHl addn0.
        specialize (ALL a); feed ALL.
        { by rewrite in_cons; apply/orP; left. }
        rewrite Pa Bool.andb_true_l in ALL.
        by apply not_scheduled_implies_no_service.
    Qed.

End GenericModelLemmas.

(** In this section, we prove some properties about service
    of sets of jobs for unit-service processor models. *)
Section UnitServiceModelLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of unit-service processor state model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any unit-service schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let P be any predicate over jobs. *)
  Variable P : pred Job.

  (** First, we prove that the service received by any set of jobs is
      upper-bounded by the corresponding workload. *) 
  Lemma service_of_jobs_le_workload:
    forall (jobs : seq Job) (t1 t2 : instant),
      service_of_jobs sched P jobs t1 t2 <= workload_of_jobs P jobs.
  Proof.
    intros jobs t1 t2.
    apply leq_sum; intros j _.
    by apply cumulative_service_le_job_cost.
  Qed.

  (** In this section, we introduce a connection between the cumulative
      service, cumulative workload, and completion of jobs. *)
  Section WorkloadServiceAndCompletion.

    (** Consider an arbitrary time interval <<[t1, t2)>>. *)
    Variables t1 t2 : instant.

    (** Let jobs be a set of all jobs arrived during <<[t1, t2)>>. *)
    Let jobs := arrivals_between arr_seq t1 t2.

    (** Next, we consider some time instant [t_compl]. *)
    Variable t_compl : instant.

    (** And state the proposition that all jobs are completed by time
       [t_compl]. Next we show that this proposition is equivalent to
       the fact that [workload of jobs = service of jobs]. *)
    Let all_jobs_completed_by t_compl :=
      forall j, j \in jobs -> P j -> completed_by sched j t_compl.

    (** First, we prove that if the workload of [jobs] is equal to the
        service of [jobs], then any job in [jobs] is completed by time
        [t_compl]. *)
    Lemma workload_eq_service_impl_all_jobs_have_completed :
      workload_of_jobs P jobs = service_of_jobs sched P jobs t1 t_compl ->
      all_jobs_completed_by t_compl.
    Proof.
      unfold jobs; intros EQ j ARR Pj; move: (ARR) => ARR2.
      apply in_arrivals_implies_arrived_between in ARR => [|//].
      move: ARR => /andP [T1 T2].
      have F1: forall a b, (a < b) || (a >= b).
      { by move=> a b; destruct (a < b) eqn:EQU; apply/orP;
          [by left |right]; apply negbT in EQU; rewrite leqNgt. }
      move: (F1 t_compl t1) => /orP [LT | GT].
      - rewrite /service_of_jobs /service_during in EQ.
        rewrite exchange_big big_geq //= in EQ.
        rewrite /workload_of_jobs in EQ.
        rewrite (big_rem j) ?Pj //= in EQ.
        move: EQ => /eqP; rewrite addn_eq0; move => /andP [CZ _].
        unfold completed_by, service.completed_by.
        by move: CZ => /eqP CZ; rewrite CZ.
      - unfold workload_of_jobs, service_of_jobs in EQ; unfold completed_by, service.completed_by.
        rewrite /service -(service_during_cat _ _ _ t1); last by apply/andP; split.
        rewrite cumulative_service_before_job_arrival_zero // add0n.
        apply: eq_leq; have /esym/eqP := EQ; rewrite eq_sum_leq_seq.
        { move=> /allP/(_ j) + /ltac:(apply/esym/eqP); apply.
          by rewrite mem_filter Pj. }
        by intros; apply cumulative_service_le_job_cost; eauto.
    Qed.

    (** And vice versa, the fact that any job in [jobs] is completed by time [t_compl]
       implies that the workload of [jobs] is equal to the service of [jobs]. *)
    Lemma all_jobs_have_completed_impl_workload_eq_service :
      all_jobs_completed_by t_compl ->
      workload_of_jobs P jobs =
      service_of_jobs sched P jobs t1 t_compl.
    Proof.
      unfold jobs; intros COMPL.
      have F: forall j t, t <= t1 -> j \in arrivals_between arr_seq t1 t2 -> service_during sched j 0 t = 0.
      { intros j t LE ARR.
        eapply in_arrivals_implies_arrived_between in ARR; eauto 2; move: ARR => /andP [GE LT].
        eapply cumulative_service_before_job_arrival_zero; eauto 2.
        by apply leq_trans with t1.
      }
      destruct (t_compl <= t1) eqn:EQ.
      - unfold service_of_jobs. unfold service_during.
        rewrite exchange_big //=.
        rewrite big_geq => [|//].
        rewrite /workload_of_jobs big1_seq //.
        move => j /andP [Pj ARR].
        specialize (COMPL _ ARR Pj).
        rewrite <- F with (j := j) (t := t_compl) => //.
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        + by apply COMPL.
        + by apply service_at_most_cost.
      - apply/eqP; rewrite eqn_leq; apply/andP; split; first last.
        + by apply service_of_jobs_le_workload.
        + rewrite /workload_of_jobs big_seq_cond [X in _ <= X]big_seq_cond.
          rewrite leq_sum // => j /andP [ARR Pj].
          specialize (COMPL _ ARR Pj).
          rewrite -[service_during _ _ _ _ ]add0n -(F j t1) //= -(big_cat_nat) //=. 
          move: EQ =>/negP /negP; rewrite -ltnNge => EQ.
          by apply ltnW.
    Qed.

    (** Using the lemmas above, we prove the equivalence. *)
    Corollary all_jobs_have_completed_equiv_workload_eq_service :
      all_jobs_completed_by t_compl <->
      workload_of_jobs P jobs = service_of_jobs sched P jobs t1 t_compl.
    Proof.
      split.
      - by apply all_jobs_have_completed_impl_workload_eq_service.
      - by apply workload_eq_service_impl_all_jobs_have_completed.
    Qed.

  End WorkloadServiceAndCompletion.

End UnitServiceModelLemmas.

(** In this section, we prove some properties about service
    of sets of jobs for unit-service uniprocessor models. *)
Section UnitServiceUniProcessorModelLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of unit-service uniprocessor state model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_unit_service_proc_model : unit_service_proc_model PState.
  Hypothesis H_uniprocessor_model : uniprocessor_model PState.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.

  (** Next, consider any unit-service uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let [P] be any predicate over jobs. *)
  Variable P : pred Job.

  (** In this section, we prove that the service received by any set of jobs
      is upper-bounded by the corresponding interval length. *)
  Section ServiceOfJobsIsBoundedByLength.

    (** Let [jobs] denote any set of jobs. *)
    Variable jobs : seq Job.
    Hypothesis H_no_duplicate_jobs : uniq jobs.

    (** We prove that the overall service of [jobs] at a single time instant is at most [1]. *)
    Lemma service_of_jobs_le_1:
      forall t, service_of_jobs_at sched P jobs t <= 1.
    Proof.
      intros t.
      eapply leq_trans.
      { by apply leq_sum_seq_pred with (P2 := predT); intros. }
      simpl; elim: jobs H_no_duplicate_jobs => [|j js IHjs] uniq_js.
      - by rewrite big_nil.
      - feed IHjs; first by move: uniq_js; rewrite cons_uniq => /andP [_ U].
        rewrite big_cons.
        destruct (service_is_zero_or_one H_unit_service_proc_model  sched j t) as [Z | O].
        + by rewrite Z (leqRW IHjs).
        + have -> : \sum_(j <- js) service_in j (sched t) = 0; last by rewrite O.
          have POS: service_at sched j t > 0 by rewrite O.
          apply service_at_implies_scheduled_at in POS.
          apply/eqP; rewrite big_seq big1 //; intros j' IN.
          apply/eqP; rewrite -leqn0 leqNgt.
          eapply contra with (b := scheduled_at sched j' t);
            first apply service_at_implies_scheduled_at.
          apply/negP; intros SCHED.
          specialize (H_uniprocessor_model _ _ _ _ POS SCHED); subst j'.
          by move: uniq_js; rewrite cons_uniq => /andP [/negP NIN _].
    Qed.

    (** Next, we prove that the service received by those jobs is no larger 
        than their workload. *)
    Corollary service_of_jobs_le_length_of_interval:
      forall (t : instant) (Δ : duration),
        service_of_jobs sched P jobs t (t + Δ) <= Δ.
    Proof.
      move=> t Δ.
      have EQ: \sum_(t <= x < t + Δ) 1 = Δ.
      { by rewrite big_const_nat iter_addn mul1n addn0 -{2}[t]addn0 subnDl subn0. }
      rewrite -{2}EQ {EQ}.
      rewrite /service_of_jobs/service_during/service_at exchange_big //=.
      rewrite leq_sum //.
      move => t' _.
      by apply service_of_jobs_le_1.
    Qed.

    (** The same holds for two time instants. *)
    Corollary service_of_jobs_le_length_of_interval':
      forall (t1 t2 : instant),
        service_of_jobs sched P jobs t1 t2 <= t2 - t1.
    Proof.
      move=> t1 t2.
      have <-: \sum_(t1 <= x < t2) 1 = t2 - t1.
      { by rewrite big_const_nat iter_addn mul1n addn0. } 
      rewrite /service_of_jobs exchange_big //=.
      rewrite leq_sum //.
      move => t' _.
      have SE :=  service_of_jobs_le_1 t'.
      eapply leq_trans; last by eassumption.
      by rewrite leq_sum.
    Qed.

  End ServiceOfJobsIsBoundedByLength.

End UnitServiceUniProcessorModelLemmas.
