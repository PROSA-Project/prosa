Require Import prosa.classic.util.all prosa.classic.model.arrival.basic.task prosa.classic.model.time.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(* Definitions and properties of job arrival sequences. *)
Module ArrivalSequence.

  Export Time.
  
  (* We begin by defining a job arrival sequence. *)
  Section ArrivalSequenceDef.

    (* Given any job type with decidable equality, ... *)
    Variable Job: eqType.

    (* ..., an arrival sequence is a mapping from any time to a (finite) sequence of jobs. *)
    Definition arrival_sequence := time -> seq Job.

  End ArrivalSequenceDef.

  (* Next, we define properties of jobs in a given arrival sequence. *)
  Section JobProperties.

    (* Consider any job arrival sequence. *)
    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.

    (* First, we define the sequence of jobs arriving at time t. *)
    Definition jobs_arriving_at (t: time) := arr_seq t.

    (* Next, we say that job j arrives at a given time t iff it belongs to the
       corresponding sequence. *)
    Definition arrives_at (j: Job) (t: time) := j \in jobs_arriving_at t.

    (* Similarly, we define whether job j arrives at some (unknown) time t, i.e.,
       whether it belongs to the arrival sequence. *)
    Definition arrives_in (j: Job) := exists t, j \in jobs_arriving_at t.

  End JobProperties.
  
  (* Next, we define properties of a valid arrival sequence. *)
  Section ArrivalSequenceProperties.

    (* Assume that job arrival times are known. *)
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.

    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.

    (* We say that arrival times are consistent if any job that arrives in the sequence
       has the corresponding arrival time. *)
    Definition arrival_times_are_consistent :=
      forall j t,
        arrives_at arr_seq j t -> job_arrival j = t.
    
    (* We say that the arrival sequence is a set iff it doesn't contain duplicate jobs
       at any given time. *)
    Definition arrival_sequence_is_a_set := forall t, uniq (jobs_arriving_at arr_seq t).

  End ArrivalSequenceProperties.

  (* Next, we define properties of job arrival times. *)
  Section PropertiesOfArrivalTime.

    (* Assume that job arrival times are known. *)
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.

    (* Let j be any job. *)
    Variable j: Job.

    (* We say that job j has arrived at time t iff it arrives at some time t_0 with t_0 <= t. *)
    Definition has_arrived (t: time) := job_arrival j <= t.

    (* Next, we say that job j arrived before t iff it arrives at some time t_0 with t_0 < t. *)
    Definition arrived_before (t: time) := job_arrival j < t.

    (* Finally, we say that job j arrives between t1 and t2 iff it arrives at some time t with
       t1 <= t < t2. *)
    Definition arrived_between (t1 t2: time) := t1 <= job_arrival j < t2.

  End PropertiesOfArrivalTime.

  (* In this section, we define arrival sequence prefixes, which are useful
     to define (computable) properties over sets of jobs in the schedule. *)
  Section ArrivalSequencePrefix.

    (* Assume that job arrival times are known. *)
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.

    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.

    (* By concatenation, we construct the list of jobs that arrived in the interval [t1, t2). *)
    Definition jobs_arrived_between (t1 t2: time) :=
      \cat_(t1 <= t < t2) jobs_arriving_at arr_seq t.

    (* Based on that, we define the list of jobs that arrived up to time t, ...*)
    Definition jobs_arrived_up_to (t: time) := jobs_arrived_between 0 t.+1.

    (* ...and the list of jobs that arrived strictly before time t. *)
    Definition jobs_arrived_before (t: time) := jobs_arrived_between 0 t.

    (* In this section, we prove some lemmas about arrival sequence prefixes. *)
    Section Lemmas.

      (* We begin with basic lemmas for manipulating the sequences. *)
      Section Basic.

        (* First, we show that the set of arriving jobs can be split
           into disjoint intervals. *)
        Lemma job_arrived_between_cat:
          forall t1 t t2,
            t1 <= t ->
            t <= t2 -> 
            jobs_arrived_between t1 t2 = jobs_arrived_between t1 t ++ jobs_arrived_between t t2.
        Proof.
          unfold jobs_arrived_between; intros t1 t t2 GE LE.
            by rewrite (@big_cat_nat _ _ _ t).
        Qed.

        Lemma jobs_arrived_between_mem_cat:
          forall j t1 t t2,
            t1 <= t ->
            t <= t2 ->
            j \in jobs_arrived_between t1 t2 =
            (j \in jobs_arrived_between t1 t ++ jobs_arrived_between t t2).
        Proof.
            by intros j t1 t t2 GE LE; rewrite (job_arrived_between_cat _ t).
        Qed.

        Lemma jobs_arrived_between_sub:
          forall j t1 t1' t2 t2',
            t1' <= t1 ->
            t2 <= t2' ->
            j \in jobs_arrived_between t1 t2 ->
            j \in jobs_arrived_between t1' t2'.
        Proof.
          intros j t1 t1' t2 t2' GE1 LE2 IN.
          move: (leq_total t1 t2) => /orP [BEFORE | AFTER];
            last by rewrite /jobs_arrived_between big_geq // in IN.
          rewrite /jobs_arrived_between.
          rewrite -> big_cat_nat with (n := t1); [simpl | by done | by apply: (leq_trans BEFORE)].
          rewrite mem_cat; apply/orP; right.
          rewrite -> big_cat_nat with (n := t2); [simpl | by done | by done].
          by rewrite mem_cat; apply/orP; left.
        Qed.
        
      End Basic.

      (* Next, we relate the arrival prefixes with job arrival times. *)
      Section ArrivalTimes.
        
        (* Assume that job arrival times are consistent. *)
        Hypothesis H_arrival_times_are_consistent:
          arrival_times_are_consistent job_arrival arr_seq.

        (* First, we prove that if a job belongs to the prefix (jobs_arrived_before t),
         then it arrives in the arrival sequence. *)
        Lemma in_arrivals_implies_arrived:
          forall j t1 t2,
            j \in jobs_arrived_between t1 t2 ->
            arrives_in arr_seq j.
        Proof.
          rename H_arrival_times_are_consistent into CONS.
          intros j t1 t2 IN.
          apply mem_bigcat_nat_exists in IN.
          move: IN => [arr [IN _]].
          by exists arr.
        Qed.

        (* Next, we prove that if a job belongs to the prefix (jobs_arrived_between t1 t2),
         then it indeed arrives between t1 and t2. *)
        Lemma in_arrivals_implies_arrived_between:
          forall j t1 t2,
            j \in jobs_arrived_between t1 t2 ->
            arrived_between job_arrival j t1 t2.
        Proof.
          rename H_arrival_times_are_consistent into CONS.
          intros j t1 t2 IN.
          apply mem_bigcat_nat_exists in IN.
          move: IN => [t0 [IN /= LT]].
          by apply CONS in IN; rewrite /arrived_between IN.
        Qed.

        (* Similarly, if a job belongs to the prefix (jobs_arrived_before t),
           then it indeed arrives before time t. *)
        Lemma in_arrivals_implies_arrived_before:
          forall j t,
            j \in jobs_arrived_before t ->
            arrived_before job_arrival j t.
        Proof.
          intros j t IN.
          suff: arrived_between job_arrival j 0 t by rewrite /arrived_between /=.
          by apply in_arrivals_implies_arrived_between.
        Qed.

        (* Similarly, we prove that if a job from the arrival sequence arrives before t,
         then it belongs to the sequence (jobs_arrived_before t). *)
        Lemma arrived_between_implies_in_arrivals:
          forall j t1 t2,
            arrives_in arr_seq j ->
            arrived_between job_arrival j t1 t2 ->
            j \in jobs_arrived_between t1 t2.
        Proof.
          rename H_arrival_times_are_consistent into CONS.
          move => j t1 t2 [a_j ARRj] BEFORE.
          have SAME := ARRj; apply CONS in SAME; subst a_j.
          by apply mem_bigcat_nat with (j := (job_arrival j)).
        Qed.

        (* Next, we prove that if the arrival sequence doesn't contain duplicate jobs,
         the same applies for any of its prefixes. *)
        Lemma arrivals_uniq :
          arrival_sequence_is_a_set arr_seq ->
          forall t1 t2, uniq (jobs_arrived_between t1 t2).
        Proof.
          rename H_arrival_times_are_consistent into CONS.
          unfold jobs_arrived_up_to; intros SET t1 t2.
          apply bigcat_nat_uniq; first by done.
          intros x t t' IN1 IN2.
          by apply CONS in IN1; apply CONS in IN2; subst.
        Qed.

      End ArrivalTimes.
      
    End Lemmas.
    
  End ArrivalSequencePrefix.

End ArrivalSequence.