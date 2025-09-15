Require Export prosa.model.readiness.suspension.

(** In this file, we establish some basic facts related to self-suspensions. *)

Section Suspensions.

  (** Consider any kind of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  (** Suppose that the jobs can exhibit self-suspensions. *)
  Context `{JobSuspension Job}.

  (** Consider any valid arrival sequence of jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and assume the notion of readiness for self-suspending jobs. *)
  #[local] Existing Instance suspension_ready_instance.

  (** Consider any kind of processor model. *)
  Context `{PState : ProcessorState Job}.

  (** Consider any valid schedule. *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.

  (** First, we establish some basic lemmas regarding self-suspending jobs. *)
  Section BasicLemmas.

    (** We show that a self-suspended job cannot be ready, ... *)
    Lemma suspended_implies_job_not_ready :
      forall j t,
        suspended sched j t ->
        ~~ job_ready sched j t.
    Proof.
      move=> j t /andP[SUS PEND].
      rewrite /job_ready /suspension_ready_instance.
      by rewrite negb_and; apply /orP; left.
    Qed.

    (** ... which trivially implies that the job cannot be scheduled. *)
    Lemma suspended_implies_not_scheduled :
      forall j t,
        suspended sched j t ->
        ~~ scheduled_at sched j t.
    Proof.
      move=> j t /suspended_implies_job_not_ready SUS.
      by move: SUS; apply contra.
    Qed.

    (** Next, we observe that a self-suspended job has already arrived. *)
    Lemma suspended_implies_arrived :
      forall j t,
        suspended sched j t ->
        has_arrived j t.
    Proof.
      by move=> j t /andP [? /andP [? ?]].
    Qed.

    (** By definition, only pending jobs can be self-suspended. *)
    Lemma suspended_implies_pending :
      forall j t,
        suspended sched j t ->
        pending sched j t.
    Proof.
      by move=> j t /andP [? ?].
    Qed.

    (** Next, we note that self-suspended jobs are not backlogged. *)
    Lemma suspended_implies_not_backlogged :
      forall j t,
        suspended sched j t ->
        ~~ backlogged sched j t.
    Proof.
      move=> j t /suspended_implies_job_not_ready SUS.
      by rewrite /backlogged negb_and; apply /orP; left.
    Qed.

    (** Further, we prove that if a job is pending and not self-suspended then
        it is ready. *)
    Lemma pending_and_not_suspended_implies_ready :
      forall j t,
        pending sched j t ->
        ~~ suspended sched j t ->
        job_ready sched j t.
    Proof.
      move=> j t; rewrite /suspended => PEND NOTSUS.
      rewrite PEND andbT negbK in NOTSUS.
      move: PEND => /andP [ARR NOTCOMP].
      by rewrite /job_ready /suspension_ready_instance; apply /andP; split.
    Qed.

  End BasicLemmas.

  (** Next, we focus on bounding the self-suspension period of a job after receiving
      some amount of service. *)
  Section SuspensionBoundedinInterval.

    (** Consider any job [j] ... *)
    Variable j : Job.

    (** ... and any time interval <<[t1, t2)>>. *)
    Variable t1 t2 : instant.

    (** Now consider any amount of work [ρ]. *)
    Variable ρ : work.

    (** Our aim is to prove a bound on the self-suspension period of [j] after receiving
        an amount of service [ρ].
        Note that it is possible that the job may not self-suspend after receiving [ρ]
        amount of service in which case [job_suspension j ρ = 0].

        Additionally, it is also important to note that the job may self-suspend multiple
        times within an interval, and these self-suspension intervals are separated by an
        interval where the job gets serviced. We can refer each such self-suspension interval as
        a segment, and each such segment is characterized by the amount of service received by the job.

        Essentially here we are establishing a bound on the length of the self-suspension segment of [j]
        characterized by [ρ]. *)

    (** Note that we can have two cases here, either the job [j] starts a suspension segment within
        the interval <<[t1, t2)>>, or the job is already suspended at [t1]. *)
    Section Step1.

      (** Consider a point [tf] inside <<[t1, t2)>>. *)
      Variable tf : instant.
      Hypothesis INtf : t1 <= tf < t2.
      
      (** Let [tf] be the first point in the interval <<[t1, t2)>> that is also inside
         the self-suspension segment. *)
      Hypothesis H_suspended_tf : suspended sched j tf.
      Hypothesis H_service_at_tf : service sched j tf = ρ.
      Hypothesis H_before_tf :
        forall to, 
          t1 <= to < tf ->
          ~~ (suspended sched j to && (service sched j to == ρ)).

      (** First, we prove a trivial result that the total suspension before [tf] is zero. *)
      Local Lemma suspension_zero_before :
        \sum_(t1 <= t < tf | service sched j t == ρ) suspended sched j t = 0.
      Proof.
        apply /eqP; rewrite sum_nat_eq0_nat.
        apply /allP => [to /[!mem_filter]/andP[SERVto /[!mem_index_iota]INto]].
        move: (H_before_tf to INto); rewrite SERVto andbT.
        by move => /negPf ->.
      Qed.

      (** Next we consider the trivial case when the suspension period exceeds the interval <<[tf, t2)>>. *)
      Section TrivialCase.
        Hypothesis H_LEQ : t2 - tf <= job_suspension j ρ.

        Lemma suspension_bounded_trivial :
          \sum_(tf <= t < t2 | service sched j t == ρ) suspended sched j t <= job_suspension j ρ.
        Proof.
          apply: leq_trans; 
            first by apply sum_majorant_constant with (c := 1) => ? ? ?; lia.
          rewrite mul1n -sum1_size big_filter.
          apply leq_trans with (n := \sum_(t0 <- index_iota tf t2) 1); first by apply leq_sum_seq_pred.
          by rewrite sum1_size size_iota. 
        Qed.

      End TrivialCase.
      
      (** Next, we consider the case when the suspension period is within the interval <<[tf, t2)>>. *)
      Section IntervalLengthLonger.
        Hypothesis H_GT : t2 - tf > job_suspension j ρ.

        Lemma suspension_bounded_longer_interval :
          \sum_(tf <= t < t2 | service sched j t == ρ) suspended sched j t <= job_suspension j ρ.
        Proof.
        have ARRj : job_arrival j <= tf by apply suspended_implies_arrived.
        have PENDj : pending sched j tf by apply suspended_implies_pending.
        erewrite big_cat_nat with (n := tf + job_suspension j ρ); rewrite //=; try by lia.
        have ->: \sum_(tf + job_suspension j ρ <= t < t2 | service sched j t == ρ) suspended sched j t = 0.
        { apply /eqP; rewrite sum_nat_eq0_nat //=.
          apply /negP => /negP /allPn[to INto NOTSUSto].
          have A : forall b : bool, b > 0 -> b by lia.
          move: NOTSUSto; rewrite -lt0n => /A NOTSUSto.
          move: INto; rewrite mem_filter mem_index_iota => /andP[/eqP SERVto /andP[INgt INlt]].
          move: NOTSUSto; rewrite /suspended.
          have ->//=: suspension_has_passed sched j to.
          { rewrite /suspension_has_passed SERVto; apply /andP; split.
            { have LT : job_suspension j ρ <= to - tf by apply leq_subRL_impl.
              by move: (leq_add ARRj LT); rewrite subnKC //=; lia. }
            { rewrite /no_progress_for /no_progress.
              have SERVGT : service sched j (to - job_suspension j ρ) >= ρ
                by rewrite -[in leqLHS]H_service_at_tf; apply service_monotonic; lia.
              have SERVLT : ρ >= service sched j (to - job_suspension j ρ)
               by rewrite -[in leqRHS]SERVto; apply service_monotonic; lia.
              by apply /eqP; lia. } } }
          rewrite addn0.
          apply: leq_trans; first by apply sum_majorant_constant with (c := 1) => ? ? ?; lia.
          rewrite mul1n -sum1_size big_filter.
          apply leq_trans with (n := \sum_(t0 <- index_iota tf (tf + job_suspension j ρ)) 1);
            first by apply leq_sum_seq_pred.
          by rewrite sum1_size size_iota; lia.
        Qed.
      
      End IntervalLengthLonger.

      (** Now we prove the required bound in case a point like [tf] exists. This helps to simplify
          our final proof. *)
      Lemma suspension_bounded_in_interval_aux :
        \sum_(t1 <= t < t2 | service sched j t == ρ) suspended sched j t <= job_suspension j ρ.
      Proof.
        have ARRj : job_arrival j <= tf by apply suspended_implies_arrived.
        have PENDj : pending sched j tf by apply suspended_implies_pending.
        erewrite big_cat_nat with (n := tf) => //=; try by lia.
        rewrite suspension_zero_before add0n.
        have [LEQ | GT] := boolP(t2 - tf <= job_suspension j ρ).
        - by apply suspension_bounded_trivial.
        - by apply suspension_bounded_longer_interval; lia.
      Qed.          

    End Step1.

    Section Step2.

      (** Now we prove that the point [tf], as used in the above lemmas, always exists if [suspended]
          is true at some point inside <<[t1, t2)>>. *)
      Hypothesis H_exists : (exists2 t, t \in index_iota t1 t2 & (suspended sched j t && (service sched j t == ρ))).

      Lemma exists_some_point :
        exists t',
          t1 <= t' < t2 /\
          suspended sched j t' /\
          service sched j t' = ρ /\
          forall to,
            t1 <= to < t' ->
            ~~ (suspended sched j to && (service sched j to == ρ)).
      Proof.
        set P := (fun t => suspended sched j t && (service sched j t == ρ)).
        set ind := find P (index_iota t1 t2).
        set t' := nth 0 (index_iota t1 t2) ind.
        move /hasP: H_exists; rewrite has_find //= => indLT.
        have INt' : t1 <= t' < t2 by rewrite -mem_index_iota mem_nth.
        have /andP[SUSt' /eqP SERVt'] :  P t' by apply (@nth_find _ 0 P (index_iota t1 t2)); apply /hasP.
        exists t'; do 3![split; eauto].
        move=> to; rewrite -mem_index_iota => INto.
        have LT : index to (iota t1 (t' - t1)) < size (iota t1 (t' - t1)) by rewrite index_mem.
        have indexLT: index to (index_iota t1 t2) < ind.
        { rewrite /index_iota.
          have SPLIT: t2 - t1 = (t' - t1) + (t2 - t') by rewrite addBnAC; lia.
          rewrite SPLIT iotaD index_cat. 
          have ->: to \in iota t1 (t' - t1) by [].
          have NOTINt': t' \notin iota t1 (t' - t1) by apply /negP; rewrite mem_index_iota; lia.
          have GT: index t' (index_iota t1 t2) >= size (iota t1 (t' - t1)).
          { rewrite /index_iota SPLIT iotaD index_cat.
            have ->: t' \in iota t1 (t' - t1) = false; try by lia.
            rewrite size_iota; by lia. }
          move: LT; rewrite size_iota => LT.
          move: GT; rewrite size_iota {2}/t' index_uniq; try by lia.
          { by rewrite /ind /P. }
          { by apply iota_uniq. } }
        have : P to = false.
        { apply (@before_find _ 0 P (index_iota t1 t2) _) in indexLT.
          rewrite nth_index in indexLT => //=.
          move: INto; rewrite mem_index_iota => INto.
          rewrite mem_index_iota; lia. }
        by rewrite /P => ->.
      Qed.

    End Step2.

    (** Finally we prove the required result. *)
    Lemma suspension_bounded_in_interval : 
      \sum_(t1 <= t < t2 | service sched j t == ρ) suspended sched j t <= job_suspension j ρ.
    Proof.
      have [/hasP HAS|/hasPn NOTHAS] := boolP(has (fun t => (suspended sched j t && (service sched j t == ρ))) (index_iota t1 t2)).
      { move: (exists_some_point HAS) => [tf [INtf [SUStf [SERVtf tfFirst]]]].
        by apply: suspension_bounded_in_interval_aux. }
      have ->: \sum_(t1 <= t < t2 | service sched j t == ρ) suspended sched j t = 0 => //=.
      apply /eqP; rewrite sum_nat_eq0_nat.
      apply /allP => [to INto].
      move: INto; rewrite mem_filter => /andP[SERVto INto].
      move: (NOTHAS to INto); rewrite SERVto andbT.
      by move => /negPf ->.
    Qed.

  End SuspensionBoundedinInterval.

End Suspensions.
