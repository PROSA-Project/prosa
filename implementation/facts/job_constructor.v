Require Export prosa.implementation.definitions.job_constructor.

(** In this file, we prove facts about the job-constructor function when used in
    pair with the concrete arrival sequence. *)
Section JobConstructor.

  (** Assume that an arrival curve based on a concrete prefix is given. *)
  #[local] Existing Instance ConcreteMaxArrivals.

  (** Consider a task set [ts] with non-duplicate tasks. *)
  Variable ts : seq Task.
  Hypothesis H_ts_uniq : uniq ts.

  (** First, we show that [generate_jobs_at tsk n t] generates n jobs ... *)
  Lemma job_generation_valid_number :
    forall tsk n t,
      tsk \in ts -> size (generate_jobs_at tsk n t) = n.
  Proof.
    move=> tsk n t IN.
    by rewrite size_map size_iota.
  Qed.

  (** ... and that each generated job is unique. *)
  Lemma generate_jobs_at_unique :
    forall tsk n t,
      uniq (generate_jobs_at tsk n t).
  Proof.
    move=> tsk n t.
    rewrite /generate_jobs_at //= /generate_job_at map_inj_uniq //=;
      first by apply iota_uniq.
    by move=> x1 x2 /eqP /andP [/andP [/andP [/andP [//= /eqP EQ _] _] _] _].
  Qed.

  (** Next, for convenience, we define [arr_seq] as the concrete arrival
      sequence used with the job constructor.  *)
  Let arr_seq := concrete_arrival_sequence generate_jobs_at ts.

  (** We start by proving that the arrival time of a job is consistent with its
      positioning inside the arrival sequence. *)
  Lemma job_arrival_consistent :
    forall j t,
      j \in arrivals_at arr_seq t -> job_arrival j = t.
  Proof. by move=> j t /mem_bigcat_exists [tsk [TSK_IN /mapP [i INi] ->]]. Qed.

  (** Next, we show that the list of arrivals at any time [t] is unique ... *)
  Lemma arrivals_at_unique :
    forall t,
      uniq (arrivals_at arr_seq t).
  Proof.
    move=> t.
    apply bigcat_uniq => //=;
      first by move=> tau _; apply: generate_jobs_at_unique.
    move=> j task1 task2 /mapP[i1 IN1 EQj1] /mapP[i2 IN2 EQj2].
    by move: EQj1 EQj2 => -> [_].
  Qed.

  (** ... and generalize the above result to arbitrary time intervals. *)
  Lemma arrivals_between_unique :
    forall t1 t2,
      uniq (arrivals_between arr_seq t1 t2).
  Proof.
    move=> t1 t2.
    rewrite /arrivals_between.
    apply bigcat_nat_uniq.
    - by apply arrivals_at_unique.
    - move=> j jt1 jt2 IN1 IN2.
      by move: (job_arrival_consistent j jt1 IN1)
                 (job_arrival_consistent j jt2 IN2) => <- <-.
  Qed.

  (** Finally, we observe that [generate_jobs_at tsk n t] indeed generates jobs
      of task [tsk] that arrive at [t] *)
  Corollary job_generation_valid_jobs :
    forall tsk n t j,
      j \in generate_jobs_at tsk n t ->
            job_task j = tsk
            /\ job_arrival j = t
            /\ job_cost j <= task_cost tsk.
  Proof. by move=> tsk n t j /mapP [i INi] ->. Qed.

End JobConstructor.
