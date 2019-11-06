Require Import rt.util.all rt.model.arrival.basic.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(* In this file we provide extra definitions for job arrival sequences with jitter. *)
Module ArrivalSequenceWithJitter.

  Export ArrivalSequence.
  
  (* First, we identify the actual arrival time of a job. *)
  Section ActualArrival.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_jitter: Job -> time.

    (* Let j be any job. *)
    Variable j: Job.

    (* We define the actual arrival of job j as the time when the jitter ends. *)
    Definition actual_arrival := job_arrival j + job_jitter j.

    (* Next, we state whether the actual arrival of job j occurs in some interval [0, t], ... *)
    Definition jitter_has_passed (t: time) := actual_arrival <= t.

    (* ...along with the variants for interval [0, t), ... *)
    Definition actual_arrival_before (t: time) := actual_arrival < t.

    (* ...and interval [t1, t2). *)
    Definition actual_arrival_between (t1 t2: time) :=
      t1 <= actual_arrival < t2.

  End ActualArrival.

  (* In this section, we show how to compute the list of arriving jobs. *)
  Section ArrivingJobs.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_jitter: Job -> time.
    Variable arr_seq: arrival_sequence Job.

    (* For simplicity, let's define some local names. *)
    Let actual_job_arrival := actual_arrival job_arrival job_jitter.
    Let actual_job_arrival_between := actual_arrival_between job_arrival job_jitter.
    Let actual_job_arrival_before := actual_arrival_before job_arrival job_jitter.
    Let arrivals_before := jobs_arrived_before arr_seq.

    (* First, we define the actual job arrivals in the interval [t1, t2). *)
    Definition actual_arrivals_between (t1 t2: time) :=
      [seq j <- arrivals_before t2 | t1 <= actual_job_arrival j < t2].

    (* Similarly, we define the actual job arrivals up to time t... *)
    Definition actual_arrivals_up_to (t: time) := actual_arrivals_between 0 t.+1.

    (* ...and the actual job arrivals strictly before time t. *)
    Definition actual_arrivals_before (t: time) := actual_arrivals_between 0 t.

    (* In this section, we prove some lemmas about the arrival sequence prefixes. *)
    Section Lemmas.

      (* Assume that job arrival times are consistent. *)
      Hypothesis H_arrival_times_are_consistent:
        arrival_times_are_consistent job_arrival arr_seq.

      (* We begin with basic lemmas for manipulating the sequences. *)
      Section Basic.

        (* First, we show that the set of arriving jobs can be split
           into disjoint intervals. *)
        Lemma actual_arrivals_between_mem_cat:
          forall j t1 t t2,
            t1 <= t ->
            t <= t2 ->
            j \in actual_arrivals_between t1 t2 =
            (j \in actual_arrivals_between t1 t ++ actual_arrivals_between t t2).
        Proof.
          unfold actual_arrivals_between; intros j t1 t t2 GE LE.
          apply/idP/idP.
          {
            intros IN.
            rewrite mem_filter in IN; move: IN => /andP [/andP [GE1 LT2] IN].
            rewrite mem_cat; apply/orP.
            rewrite 2!mem_filter.
            case (ltnP (actual_job_arrival j) t) => [BEFORE | AFTER]; last by right; rewrite LT2.
            left; rewrite GE1 /=.
            have INarr: arrives_in arr_seq j by apply in_arrivals_implies_arrived in IN.
            apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival);
              try (by done).
            by apply: (leq_ltn_trans _ BEFORE); apply leq_addr.
          }
          {
            rewrite mem_cat; move => /orP [LEFT | RIGHT].
            {
              rewrite mem_filter in LEFT; move: LEFT => /andP [ /andP [GE0 LT0] IN0].
              rewrite mem_filter GE0 /=.
              apply/andP; split; first by apply: (leq_trans _ LE).
              have INarr: arrives_in arr_seq j by apply in_arrivals_implies_arrived in IN0.
              apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival);
                try (by done).
              rewrite /arrived_between /=.
              by apply: (leq_trans _ LE); apply: (leq_ltn_trans _ LT0); apply leq_addr.
            }
            {
              rewrite mem_filter in RIGHT; move: RIGHT => /andP [/andP [GE0 LT0] IN0].
              rewrite mem_filter LT0 /= andbT.
              apply/andP; split; first by apply: (leq_trans GE).
              have INarr: arrives_in arr_seq j by apply in_arrivals_implies_arrived in IN0.
              apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival);
                try (by done).
              by apply: (leq_ltn_trans _ LT0); apply leq_addr.
            }
          }
        Qed.

        Lemma actual_arrivals_between_sub:
          forall j t1 t1' t2 t2',
            t1' <= t1 ->
            t2 <= t2' ->
            j \in actual_arrivals_between t1 t2 ->
            j \in actual_arrivals_between t1' t2'.
        Proof.
          intros j t1 t1' t2 t2' GE1 LE2 IN.
          rewrite mem_filter in IN; move: IN => /andP [/andP [GE LE] IN].
          move: (leq_total t1 t2) => /orP [BEFORE | AFTER]; last first.
          {
            suff BUG: t2 < t2 by rewrite ltnn in BUG.
            by apply: (leq_ltn_trans AFTER); apply: (leq_ltn_trans GE).
          }
          rewrite -> actual_arrivals_between_mem_cat with (t := t1);
            [| by done | by apply: (leq_trans BEFORE)].
          rewrite mem_cat; apply/orP; right.
          rewrite -> actual_arrivals_between_mem_cat with (t := t2);
            [| by done | by done].
          rewrite mem_cat; apply/orP; left.
          by rewrite mem_filter; repeat (apply/andP; split).
        Qed.

      End Basic.

      (* Next, we relate the arrival prefixes with job arrival times. *)
      Section ArrivalTimes.
        
        (* First, we prove that if a job belongs to the prefix (actual_arrivals_before t),
         then it arrives in the arrival sequence. *)
        Lemma in_actual_arrivals_between_implies_arrived:
          forall j t1 t2,
            j \in actual_arrivals_between t1 t2 ->
            arrives_in arr_seq j.
        Proof.
          rename H_arrival_times_are_consistent into CONS.
          intros j t1 t2 IN.
          rewrite mem_filter in IN; move: IN => /andP [_ IN].
          apply mem_bigcat_nat_exists in IN.
          by move: IN => [t0 /= [IN _]]; exists t0.
        Qed.

        Lemma in_actual_arrivals_before_implies_arrived:
          forall j t,
            j \in actual_arrivals_before t ->
            arrives_in arr_seq j.
        Proof.
          rename H_arrival_times_are_consistent into CONS.
          intros j t IN.
          rewrite mem_filter in IN; move: IN => /andP [_ IN].
          apply mem_bigcat_nat_exists in IN.
          by move: IN => [t0 /= [IN _]]; exists t0.
        Qed.
        
        (* Next, we prove that if a job belongs to the prefix (actual_arrivals_before t),
         then its actual job arrival occured before t. *)
        Lemma in_actual_arrivals_implies_arrived_before:
          forall j t,
            j \in actual_arrivals_before t ->
            actual_job_arrival_before j t.
        Proof.
          intros j t IN.
          by rewrite mem_filter /= in IN; move: IN => /andP [LTt _].
        Qed.

        (* We also prove that if a job belongs to the prefix (actual_arrivals_between t1 t2),
           then its actual job arrival occured between t1 and t2. *)
        Lemma in_actual_arrivals_implies_arrived_between:
          forall j t1 t2,
            j \in actual_arrivals_between t1 t2 ->
            actual_job_arrival_between j t1 t2.
        Proof.
          intros j t1 t2 IN.
          by rewrite mem_filter /= in IN; move: IN => /andP [LTt _].
        Qed.
        
        (* Similarly, we prove that if a job from the arrival sequence has actual arrival
         before time t, then it belongs to the sequence (actual_arrivals_before t). *)
        Lemma arrived_between_implies_in_actual_arrivals:
          forall j t1 t2,
            arrives_in arr_seq j ->
            actual_job_arrival_between j t1 t2 ->
            j \in actual_arrivals_between t1 t2.
        Proof.
          intros j t1 t2 IN BEFORE.
          rewrite mem_filter; apply/andP; split; first by done.
          eapply arrived_between_implies_in_arrivals; [by eauto | by done |].
          rewrite /arrived_between /=.
          move: BEFORE => /andP [_ LE].
          by apply: (leq_ltn_trans _ LE); apply leq_addr.
        Qed.

        (* Next, we prove that if the arrival sequence doesn't contain duplicate jobs,
         the same applies for any of its prefixes. *)
        Lemma actual_arrivals_uniq :
          arrival_sequence_is_a_set arr_seq ->
          forall t1 t2, uniq (actual_arrivals_between t1 t2).
        Proof.
          intros SET t1 t2.
          by eapply filter_uniq, arrivals_uniq, SET; eauto 1.
        Qed.

      End ArrivalTimes.

    End Lemmas.
    
  End ArrivingJobs.

End ArrivalSequenceWithJitter.