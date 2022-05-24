From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Require Export prosa.model.aggregate.workload.
Require Export prosa.model.aggregate.service_of_jobs.
Require Export prosa.analysis.facts.model.service_of_jobs.
Require Export prosa.analysis.facts.behavior.completion.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.
Require Export prosa.analysis.facts.model.ideal.schedule.

(** * Service Received by Sets of Jobs in Ideal Uni-Processor Schedules *)

(** In this file, we establish a fact about the service received by _sets_ of
    jobs under ideal uni-processor schedule and the presence of idle times.  The
    lemma is currently specific to ideal uniprocessors only because of the lack
    of a general notion of idle time, which should be added in the near
    future. Conceptually, the fact holds for any [ideal_progress_proc_model].
    Once a general notion of idle time has been defined, this file should be
    generalized.  *)
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

  (** Let [P] be any predicate over jobs. *)
  Variable P : pred Job.

  (** We prove that if the total service within some time interval <<[t1,t2)>>
      is smaller than <<t2 - t1>>, then there is an idle time instant [t ∈ [t1,t2)]. *)
  Lemma low_service_implies_existence_of_idle_time :
    forall t1 t2,
      service_of_jobs sched predT (arrivals_between arr_seq 0 t2) t1 t2 < t2 - t1 ->
      exists t, t1 <= t < t2 /\ is_idle sched t.
  Proof.
    intros ? ? SERV.
    destruct (t1 <= t2) eqn:LE; last first.
    { move: LE => /negP/negP; rewrite -ltnNge.
      move => LT; apply ltnW in LT; rewrite -subn_eq0 in LT.
      by move: LT => /eqP -> in SERV; rewrite ltn0 in SERV.
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
    move: L => /eqP; rewrite sum_nat_eq0_nat filter_predT; move => /allP L.
    specialize (L s); feed L. 
    { unfold arrivals_between.
      eapply arrived_between_implies_in_arrivals; eauto 2.
      by apply H_jobs_must_arrive_to_execute in SCHED; apply leq_ltn_trans with x.
    } 
    move: SCHED L => /=.
    rewrite scheduled_at_def service_at_def => /eqP-> /eqP.
    by rewrite eqxx.
  Qed.

End IdealModelLemmas.
