Require Export prosa.analysis.facts.busy_interval.carry_in.
Require Export prosa.analysis.facts.busy_interval.ideal.busy_interval.

(** The following lemma conceptually belongs in
    [prosa.analysis.facts.busy_interval.carry_in], but still has dependencies
    with a baked-in ideal uniprocessor assumption. When these dependencies get
    generalized, then this lemma should be generalized as well and moved elsewhere. *)

Section BusyWindowExistence.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context {Arrival: JobArrival Job}.
  Context {Cost : JobCost Job}.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arr_seq : valid_arrival_sequence arr_seq.

  (** Next, consider any well-behaved ideal uni-processor schedule of this
      arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

    (** Assume a given reflexive JLFP policy. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive: reflexive_job_priorities JLFP.

  (** Further, allow for any work-bearing notion of job readiness ... *)
  Context `{@JobReady Job (ideal.processor_state Job) Cost Arrival}.
  Hypothesis H_job_ready : work_bearing_readiness arr_seq sched.

  (** ... and assume that the schedule is work-conserving. *)
  Hypothesis H_work_conserving : work_conserving arr_seq sched.

  (** Recall the notion of workload of all jobs released in a given interval
       <<[t1, t2)>>. *)
  Let total_workload t1 t2 :=
    workload_of_jobs predT (arrivals_between arr_seq t1 t2).

  (** Assume that for some positive [Δ], the sum of requested workload
      at time [t + Δ] is bounded by [Δ] (i.e., the supply). Note that
      this assumption bounds the total workload of jobs released in a
      time interval <<[t, t + Δ)>> regardless of their priorities. *)
  Variable Δ : duration.
  Hypothesis H_delta_positive : Δ > 0.
  Hypothesis H_workload_is_bounded : forall t, total_workload t (t + Δ) <= Δ.

  (** Consider an arbitrary job [j] with positive cost. *)
  Variable j : Job.
  Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
  Hypothesis H_job_cost_positive : job_cost_positive j.

  (** We show that there must exist a busy interval <<[t1, t2)>> that
      contains the arrival time of [j]. *)
  Corollary exists_busy_interval_from_total_workload_bound :
    exists t1 t2,
      t1 <= job_arrival j < t2 /\
      t2 <= t1 + Δ /\
      busy_interval arr_seq sched j t1 t2.
  Proof.
    rename H_from_arrival_sequence into ARR, H_job_cost_positive into POS.
    have CONSIST: consistent_arrival_times arr_seq by [].
    edestruct (exists_busy_interval_prefix
                 arr_seq CONSIST
                 sched j ARR H_priority_is_reflexive (job_arrival j))
      as [t1 [PREFIX GE]]; first by apply job_pending_at_arrival.
    move: GE => /andP [GE1 _].
    exists t1.
    have [δ [LE QT]]:  exists δ : nat, δ < Δ /\ no_carry_in arr_seq sched (t1.+1 + δ).
      exact: processor_is_not_too_busy.
    eapply no_carry_in_implies_quiet_time with (j := j) in QT.
    have EX: exists t2, ((t1 < t2 <= t1.+1 + δ) && quiet_time_dec arr_seq sched j t2).
    { exists (t1.+1 + δ); apply/andP; split.
      - by apply/andP; split; first rewrite addSn ltnS leq_addr.
      - exact/quiet_time_P. }
    move: (ex_minnP EX) => [t2 /andP [/andP [GTt2 LEt2] QUIET] MIN]; clear EX.
    have NEQ: t1 <= job_arrival j < t2.
    { apply/andP; split=> [//|].
      rewrite ltnNge; apply/negP; intros CONTR.
      move: (PREFIX) => [_ [_ [NQT _]]].
      move: (NQT t2); clear NQT; move  => NQT.
      feed NQT; first by (apply/andP; split; [|rewrite ltnS]).
      by apply: NQT; apply/quiet_time_P.
    }
    exists t2; split=> [//|]; split.
    { by apply leq_trans with (t1.+1 + δ); [|rewrite addSn ltn_add2l]. }
    { move: PREFIX => [_ [QTt1 [NQT _]]]; repeat split=> //; last first.
        exact/quiet_time_P.
      move => t /andP [GEt LTt] QTt.
      feed (MIN t); last first.
        by move: LTt; rewrite ltnNge; move => /negP LTt; apply: LTt.
      apply/andP; split.
      + by apply/andP; split; last (apply leq_trans with t2; [apply ltnW | ]).
      + exact/quiet_time_P.
    }
  Qed.

End BusyWindowExistence.
