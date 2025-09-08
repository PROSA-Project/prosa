Require Export prosa.model.priority.classes.
Require Export prosa.model.aggregate.service_of_jobs.
Require Export prosa.analysis.facts.behavior.service.

(** * Service Received by Sets of Jobs in Uniprocessor Schedules *)

(** In this section, we establish a fact about the service received by
    _sets_ of jobs in the presence of idle times on a fully-consuming
    uniprocessor model. *)
Section FullyConsumingModelLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Allow for any fully-consuming uniprocessor model. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.
  Hypothesis H_fully_consuming_proc_model : fully_consuming_proc_model PState.

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let [P] be any predicate over jobs. *)
  Variable P : pred Job.

  (** We prove that, if the sum of the total blackout and the total
      service within some time interval <<[t1,t2)>> is smaller than
      [t2 - t1], then there is an idle time instant <<t ∈ [t1,t2)>>. *)
  Lemma low_service_implies_existence_of_idle_time_rs :
    forall t1 t2,
      blackout_during sched t1 t2
       + service_of_jobs sched predT (arrivals_between arr_seq 0 t2) t1 t2 < t2 - t1 ->
      exists t,
        t1 <= t < t2 /\ is_idle arr_seq sched t.
  Proof.
    move=> t1 t2 SERV.
    destruct (t1 <= t2) eqn:LE; last first.
    { move: LE => /negP/negP; rewrite -ltnNge.
      move => LT; apply ltnW in LT; rewrite -subn_eq0 in LT.
      by move: LT => /eqP -> in SERV; rewrite ltn0 in SERV.
    }
    interval_to_duration t1 t2 δ.
    rewrite {4}[t1 + δ]addnC -addnBA // subnn addn0 in SERV.
    rewrite /service_of_jobs exchange_big //= in SERV.
    rewrite -big_split //= in SERV.
    apply sum_le_summation_range in SERV.
    move: SERV => [x [/andP [GEx LEx] L]].
    exists x; split; first by apply/andP; split.
    move: L => /eqP; rewrite addn_eq0 eqb0 sum_nat_eq0_nat filter_predT => /andP [SUP /allP L].
    apply/negPn/negP; rewrite is_nonidle_iff //= => [[j SCHED]].
    have /eqP: service_at sched j x == 0.
    { apply/L/arrived_between_implies_in_arrivals => //.
      rewrite /arrived_between; apply/andP; split => //.
      have: job_arrival j <= x by apply: H_jobs_must_arrive_to_execute.
      lia. }
    move: SUP; rewrite negbK => SUP SERV.
    eapply ideal_progress_inside_supplies in SUP => //.
    by move: SUP; rewrite /receives_service_at SERV.
  Qed.

End FullyConsumingModelLemmas.

(** * Service Received by Sets of Jobs in Uniprocessor Ideal-Progress Schedules *)

(** Next, we establish a fact about the service received by sets of
    jobs in the presence of idle times on a uniprocessor under the
    ideal-progress assumption (i.e., that a scheduled job necessarily
    receives nonzero service).  *)
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
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Allow for any uniprocessor model that ensures ideal progress. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.
  Hypothesis H_ideal_progress_proc_model : ideal_progress_proc_model PState.

  (** Next, consider any ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Let [P] be any predicate over jobs. *)
  Variable P : pred Job.

  (** We prove that if the total service within some time interval <<[t1,t2)>>
      is smaller than <<[t2 - t1]>>, then there is an idle time instant <<t ∈ [t1,t2)>>. *)
  Lemma low_service_implies_existence_of_idle_time :
    forall t1 t2,
      service_of_jobs sched predT (arrivals_between arr_seq 0 t2) t1 t2 < t2 - t1 ->
      exists t,
        t1 <= t < t2 /\ is_idle arr_seq sched t.
  Proof.
    move=> t1 t2 SERV.
    destruct (t1 <= t2) eqn:LE; last first.
    { move: LE => /negP/negP; rewrite -ltnNge.
      move => LT; apply ltnW in LT; rewrite -subn_eq0 in LT.
      by move: LT => /eqP -> in SERV; rewrite ltn0 in SERV.
    }
    interval_to_duration t1 t2 δ.
    rewrite {3}[t1 + δ]addnC -addnBA // subnn addn0 in SERV.
    rewrite /service_of_jobs exchange_big //= in SERV.
    apply sum_le_summation_range in SERV.
    move: SERV => [x [/andP [GEx LEx] L]].
    exists x; split; first by apply/andP; split.
    apply/negPn/negP; rewrite is_nonidle_iff //= => [[j SCHED]].
    move: L => /eqP; rewrite sum_nat_eq0_nat filter_predT => /allP L.
    have /eqP:  service_at sched j x == 0.
    { apply/L/arrived_between_implies_in_arrivals => //.
      rewrite /arrived_between; apply/andP; split => //.
      have: job_arrival j <= x by apply: H_jobs_must_arrive_to_execute.
      lia. }
    by rewrite -no_service_not_scheduled // => /negP.
  Qed.

End IdealModelLemmas.
