Require Export prosa.model.priority.classes.
Require Export prosa.analysis.facts.behavior.completion.

(** Throughout this file, we assume ideal uniprocessor schedules. *)
Require Import prosa.model.processor.ideal.

(** * Busy Interval for JLFP-models *)
(** In this file we define the notion of busy intervals for uniprocessor for JLFP schedulers. *)
Section BusyIntervalJLFP.
  
  (** Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.    

  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  
  (** Next, consider any ideal uniprocessor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).
  
  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}. 

  (** In this section, we define the notion of a busy interval. *)
  Section BusyInterval.
    
    (** Consider any job j. *)
    Variable j : Job.
    Hypothesis H_from_arrival_sequence : arrives_in arr_seq j.
    
    (** We say that t is a quiet time for j iff every higher-priority job from
         the arrival sequence that arrived before t has completed by that time. *)
    Definition quiet_time (t : instant) :=
      forall (j_hp : Job),
        arrives_in arr_seq j_hp ->
        hep_job j_hp j ->
        arrived_before j_hp t ->
        completed_by sched j_hp t.
    
    (** Based on the definition of quiet time, we say that interval
         <<[t1, t_busy)>> is a (potentially unbounded) busy-interval prefix
         iff the interval starts with a quiet time where a higher or equal 
         priority job is released and remains non-quiet. We also require
         job j to be released in the interval. *)    
    Definition busy_interval_prefix (t1 t_busy : instant) :=
      t1 < t_busy /\
      quiet_time t1 /\
      (forall t, t1 < t < t_busy -> ~ quiet_time t) /\
      t1 <= job_arrival j < t_busy.

    (** Next, we say that an interval <<[t1, t2)>> is a busy interval iff
         [t1, t2) is a busy-interval prefix and t2 is a quiet time. *)
    Definition busy_interval (t1 t2 : instant) :=
      busy_interval_prefix t1 t2 /\
      quiet_time t2.

  End BusyInterval.

  (** In this section we define the computational
      version of the notion of quiet time. *)
  Section DecidableQuietTime.

    (** We say that t is a quiet time for j iff every higher-priority job from
        the arrival sequence that arrived before t has completed by that time. *)
    Definition quiet_time_dec (j : Job) (t : instant) :=
      all
        (fun j_hp => hep_job j_hp j ==> (completed_by sched j_hp t))
        (arrivals_before arr_seq t).

    (** We also show that the computational and propositional definitions are equivalent. *)
    Lemma quiet_time_P :
      forall j t, reflect (quiet_time j t) (quiet_time_dec j t).
    Proof.
      intros; apply/introP.
      - intros QT s ARRs HPs BEFs.
        move: QT => /allP QT.
        specialize (QT s); feed QT.
        eapply arrived_between_implies_in_arrivals; eauto 2.
          by move: QT => /implyP Q; apply Q in HPs.
      - move => /negP DEC; intros QT; apply: DEC.
        apply/allP; intros s ARRs.
        apply/implyP; intros HPs.
        apply QT; try done.
        + by apply in_arrivals_implies_arrived in ARRs.
        + by eapply in_arrivals_implies_arrived_between in ARRs; eauto 2.
    Qed.

  End DecidableQuietTime.

End BusyIntervalJLFP.