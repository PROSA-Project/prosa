Require Export prosa.analysis.definitions.job_properties.
Require Export prosa.analysis.facts.behavior.all.
Require Export prosa.analysis.abstract.definitions.

(** * Lemmas About Abstract Busy Intervals *)

(** In this file we prove a few basic lemmas about the notion of
    an abstract busy interval. *)
Section LemmasAboutAbstractBusyInterval.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** Consider an arbitrary task [tsk]. *)
  Variable tsk : Task.

  (** Next, consider any work-conserving schedule of this arrival sequence
      ... *)
  Variable sched : schedule PState.
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** ... where jobs do not execute before their arrival. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** Consider an arbitrary job [j] with positive cost. Notice that a
      positive-cost assumption is required to ensure that one cannot
      construct a busy interval without any workload inside of it. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** Consider a busy interval <<[t1, t2)>> of job [j]. *)
  Variable t1 t2 : instant.
  Hypothesis H_busy_interval : busy_interval sched j t1 t2.

  (** First, we prove that job [j] completes by the end of the busy
      interval. Note that the busy interval contains the execution of
      job [j]; in addition, time instant [t2] is a quiet time. Thus by
      the definition of a quiet time the job must be completed
      before time [t2]. *)
  Lemma job_completes_within_busy_interval :
    completed_by sched j t2.
  Proof.
    move: (H_busy_interval) => [[/andP [_ LT] [_ _]] [_ QT2]].
    unfold pending, has_arrived in QT2.
    move: QT2; rewrite  /pending negb_and; move => /orP [QT2|QT2].
    { by move: QT2 => /negP QT2; exfalso; apply QT2, ltnW. }
    by rewrite Bool.negb_involutive in QT2.
  Qed.

  (** We show that, similarly to the classical notion of busy
      interval, the job does not receive service before the busy
      interval starts. *)
  Lemma no_service_before_busy_interval :
    forall t, service sched j t = service_during sched j t1 t.
  Proof.
    move => t; move : (H_busy_interval) => [[/andP [LE1 LE2] [QT1 AQT]] QT2].
    destruct (leqP t1 t) as [NEQ1|NEQ1]; first destruct (leqP t2 t) as [NEQ2|NEQ2].
    - apply/eqP; rewrite eqn_leq; apply/andP; split.
      + rewrite /service -(service_during_cat _ _ _ t1);
          [ | by apply/andP; split; lia].
        by rewrite cumulative_service_before_job_arrival_zero; eauto 2.
      + rewrite /service -[in X in _ <= X](service_during_cat _ _ _ t1);
          [ | by apply/andP; split; lia].
        by (erewrite cumulative_service_before_job_arrival_zero with (t1 := 0)
           || erewrite cumulative_service_before_job_arrival_zero with (t3 := 0)).
    - rewrite /service -(service_during_cat _ _ _ t1);
        [ | by apply/andP; split; lia].
      by rewrite cumulative_service_before_job_arrival_zero; eauto 2.
    - rewrite service_during_geq; last by lia.
      by rewrite /service cumulative_service_before_job_arrival_zero//; lia.
  Qed.

  (** Since the job cannot arrive before the busy interval starts and
      completes by the end of the busy interval, it receives at least
      [job_cost j] units of service within the interval. *)
  Lemma service_within_busy_interval_ge_job_cost :
    job_cost j <= service_during sched j t1 t2.
  Proof.
    move : (H_busy_interval) => [[/andP [LE1 LE2] [QT1 AQT]] QT2].
    rewrite -[service_during _ _ _ _]add0n.
    rewrite -(cumulative_service_before_job_arrival_zero sched j _ 0 _ LE1)//.
    rewrite service_during_cat; last by apply/andP; split; lia.
    rewrite  -/(completed_by sched j t2).
    exact: job_completes_within_busy_interval.
  Qed.

End LemmasAboutAbstractBusyInterval.
