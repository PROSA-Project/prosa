Require Export prosa.model.aggregate.workload.
Require Export prosa.analysis.facts.behavior.arrivals.

(** * Lemmas about Workload of Sets of Jobs *)
(** In this file, we establish basic facts about the workload of sets of jobs. *)  
Section WorkloadFacts.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Further, consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** For simplicity, let's define a local name. *)
  Let arrivals_between := arrivals_between arr_seq.
  
  (** We observe that the cumulative workload of all jobs arriving in a time
      interval <<[t1, t2)>> and respecting a predicate [P] can be split into two parts. *)
  Lemma workload_of_jobs_cat:
    forall t t1 t2 P,
      t1 <= t <= t2 ->
      workload_of_jobs P (arrivals_between t1 t2) =
      workload_of_jobs P (arrivals_between t1 t) + workload_of_jobs P (arrivals_between t t2).
  Proof.
    move => t t1 t2 P /andP [GE LE].
    rewrite /workload_of_jobs /arrivals_between.
    by rewrite (arrivals_between_cat _ _ t) // big_cat.
  Qed.

  (** Consider a job [j] ... *)
  Variable j : Job.

  (** ... and a duplicate-free sequence of jobs [jobs]. *)
  Variable jobs : seq Job.
  Hypothesis H_jobs_uniq : uniq jobs.

  (** Further, assume that [j] is contained in [jobs]. *)
  Hypothesis H_j_in_jobs : j \in jobs.

  (** To help with rewriting, we prove that the workload of [jobs]
      minus the job cost of [j] is equal to the workload of all jobs
      except [j]. To define the workload of all jobs, since
      [workload_of_jobs] expects a predicate, we use [predT], which
      is the always-true predicate. *)
  Lemma workload_minus_job_cost :
    workload_of_jobs (fun jhp : Job => jhp != j) jobs =
    workload_of_jobs predT jobs - job_cost j.
  Proof.
    rewrite /workload_of_jobs (big_rem j) //=  eq_refl //= add0n.
    rewrite [in RHS](big_rem j) //= addnC -subnBA //= subnn subn0.
    rewrite [in LHS]big_seq_cond [in RHS]big_seq_cond.
    apply eq_bigl => j'.
    rewrite Bool.andb_true_r.
    destruct (j' \in rem (T:=Job) j jobs) eqn:INjobs; last by done.
    apply /negP => /eqP EQUAL.
    by rewrite EQUAL mem_rem_uniqF in INjobs.
  Qed.

  (** In this section, we prove the relation between two different ways of constraining 
      [workload_of_jobs] to only those jobs that arrive prior to a given time. *)
  Section Subset.

    (** Assume that arrival times are consistent and that arrivals are unique. *)
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.
    Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

    (** Consider a time interval <<[t1, t2)>> and a time instant [t]. *)
    Variable t1 t2 t : instant.
    Hypothesis H_t1_le_t2 : t1 <= t2.

    (** Let [P] be an arbitrary predicate on jobs. *)
    Variable P : pred Job.

    (** Consider the window <<[t1,t2)>>. We prove that the total workload of the jobs
        arriving in this window before some [t] is the same as the workload of the jobs
        arriving in <<[t1,t)>>. Note that we only require [t1] to be less-or-equal
        than [t2]. Consequently, the interval <<[t1,t)>> may be empty. *)
    Lemma workload_equal_subset :
      workload_of_jobs (fun j => (job_arrival j <= t) && P j) (arrivals_between t1 t2)
      <= workload_of_jobs (fun j => P j) (arrivals_between t1 (t + ε)).
    Proof.
      clear H_jobs_uniq H_j_in_jobs H_t1_le_t2.
      rewrite /workload_of_jobs big_seq_cond.
      rewrite -[in X in X <= _]big_filter -[in X in _ <= X]big_filter.
      apply leq_sum_sub_uniq; first by apply filter_uniq, arrivals_uniq.
      move => j'; rewrite mem_filter => [/andP [/andP [A /andP [C D]] _]].
      rewrite mem_filter; apply/andP; split; first by done.
      apply job_in_arrivals_between; eauto.
      - by eapply in_arrivals_implies_arrived; eauto 2.
      - apply in_arrivals_implies_arrived_between in A; auto; move: A => /andP [A E].
        by unfold ε; apply/andP; split; lia.
    Qed.

  End Subset.
    
  (** In this section, we prove a few useful properties regarding the
      predicate of [workload_of_jobs]. *)
  Section PredicateProperties.

    (** First, we show that workload of jobs for an unsatisfiable
        predicate is equal to 0. *) 
    Lemma workload_of_jobs_pred0 :
      workload_of_jobs pred0 jobs = 0.
    Proof. by rewrite /workload_of_jobs; apply big_pred0. Qed.
    
    (** Next, consider two arbitrary predicates [P] and [P']. *) 
    Variable P P' : pred Job.

    (** We show that [workload_of_jobs] conditioned on [P] can be split into two summands: 
        (1) [workload_of_jobs] conditioned on [P /\ P'] and 
        (2) [workload_of_jobs] conditioned on [P /\ ~~ P']. *) 
    Lemma workload_of_jobs_case_on_pred :
      workload_of_jobs P jobs =
        workload_of_jobs (fun j => P j && P' j) jobs + workload_of_jobs (fun j => P j && ~~ P' j) jobs.
    Proof.
      rewrite /workload_of_jobs !big_mkcond [in X in _ = X]big_mkcond
              [in X in _ = _ + X]big_mkcond //= -big_split //=.
      apply: eq_big_seq => j' IN.
      by destruct (P _), (P' _); simpl; lia.
    Qed.

    (** We show that if [P] is indistinguishable from [P'] on set
        [jobs], then [workload_of_jobs] conditioned on [P] is equal to
        [workload_of_jobs] conditioned on [P']. *) 
    Lemma workload_of_jobs_equiv_pred :
      {in jobs, P =1 P'} -> 
      workload_of_jobs P jobs = workload_of_jobs P' jobs.
    Proof.
      intros * EQUIV.
      rewrite /workload_of_jobs !big_mkcond [in X in _ = X]big_mkcond //=.
      by apply: eq_big_seq => j' IN; rewrite EQUIV.
    Qed.

  End PredicateProperties.
  
End WorkloadFacts.
