Require Import prosa.classic.util.all.
Require Import prosa.classic.model.time prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.arrival.jitter.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we prove additional definitions and lemmas about jitter-aware schedules. *)
Module UniprocessorScheduleWithJitter.

  (* To formalize jitter, we import the original uniprocessor schedule and
     redefine some of the properties. *)
  Export ArrivalSequenceWithJitter UniprocessorSchedule.
  
  (* In this section we redefine properties that depend on the arrival time. *)
  Section RedefiningProperties.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Consider any uniprocessor schedule. *)
    Variable arr_seq: arrival_sequence Job.
    Variable sched: schedule Job.

    (* First, we redefine some job properties. *)
    Section JobProperties.
      
      (* Let j be any job in the arrival sequence. *)
      Variable j: Job.

      (* Then, we say that job j is pending at time t iff the jitter has passed but
         j has not completed by time t. *)
      Definition pending (t: time) :=
        jitter_has_passed job_arrival job_jitter j t && ~~ completed_by job_cost sched j t.

      (* Finally, we say that job j is backlogged at time t iff it is pending and not scheduled. *)
      Definition backlogged (t: time) :=
        pending t && ~~ scheduled_at sched j t.

    End JobProperties.

    (* Next, we define properties of a valid jitter-aware schedule. *)
    Section ValidSchedules.

      (* In any jitter-aware schedule, a job can only be scheduled after
         the jitter has passed. *)
      Definition jobs_execute_after_jitter :=
        forall j t,
          scheduled_at sched j t -> jitter_has_passed job_arrival job_jitter j t.

    End ValidSchedules.
  
    (* In this section, we prove some basic lemmas about jitter-aware schedules. *)   
    Section Lemmas.

      (* For simplicity, let's define some local names. *)
      Let has_actually_arrived := jitter_has_passed job_arrival job_jitter.
      Let actual_job_arrival := actual_arrival job_arrival job_jitter.
      
      (* We begin by proving properties related to job arrivals. *)
      Section Arrival.

        (* Assume that jobs only execute after the jitter has passed. *)
        Hypothesis H_jobs_execute_after_jitter: jobs_execute_after_jitter.

        (* First, we show that every job in the schedule only executes after its arrival time. *)
        Lemma jobs_with_jitter_must_arrive_to_execute:
          jobs_must_arrive_to_execute job_arrival sched.
        Proof.
          intros j t SCHED.
          apply leq_trans with (n := actual_arrival job_arrival job_jitter j);
            first by apply leq_addr.
          by apply H_jobs_execute_after_jitter.
        Qed.

        (* Now, let j be any job. *)
        Variable j: Job.

        (* First, we show that if the jitter has passed, then the job must have arrived. *)
        Lemma jitter_has_passed_implies_arrived:
          forall t,
            has_actually_arrived j t ->
            has_arrived job_arrival j t.
        Proof.
          by intros t PASS; apply: leq_trans PASS; apply leq_addr.
        Qed.
        
        (* Now we prove that job j does not receive service at any time t before
           its actual arrival time. *)
        Lemma service_before_jitter_is_zero :
          forall t,
            t < actual_job_arrival j ->
            service_at sched j t = 0.
        Proof.
          rename H_jobs_execute_after_jitter into ARR; red in ARR; intros t LT.
          specialize (ARR j t).
          apply contra with (c := scheduled_at sched j t)
                            (b := jitter_has_passed job_arrival job_jitter j t) in ARR;
            last by rewrite -ltnNge.
          by apply/eqP; rewrite eqb0.
        Qed.

        (* Note that the same property applies to the cumulative service. *)
        Lemma cumulative_service_before_jitter_is_zero :
          forall t1 t2,
            t2 <= actual_job_arrival j ->
            \sum_(t1 <= i < t2) service_at sched j i = 0.
        Proof.
          intros t1 t2 LE; apply/eqP; rewrite -leqn0.
          apply leq_trans with (n := \sum_(t1 <= i < t2) 0);
            last by rewrite big_const_nat iter_addn mul0n addn0.
          rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
          apply leq_sum; intro i; rewrite andbT; move => /andP LTi; des.
          rewrite service_before_jitter_is_zero; first by ins.
            by apply leq_trans with (n := t2); ins.
        Qed.

        (* Hence, one can ignore the service received by a job before the jitter. *)
        Lemma ignore_service_before_jitter:
          forall t1 t2,
            t1 <= actual_job_arrival j <= t2 ->
            \sum_(t1 <= t < t2) service_at sched j t =
            \sum_(actual_job_arrival j <= t < t2) service_at sched j t.
        Proof.
          move => t1 t2 /andP [LE1 GE2].
          rewrite -> big_cat_nat with (n := actual_job_arrival j); try (by done).
          by rewrite /= cumulative_service_before_jitter_is_zero; [rewrite add0n | apply leqnn].
        Qed.

      End Arrival.

      (* In this section, we prove properties about pending jobs. *)
      Section Pending.

        (* Assume that jobs only execute after the jitter has passed... *)
        Hypothesis H_jobs_execute_after_jitter: jobs_execute_after_jitter.

        (* ...and that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.

        (* Let j be any job. *)
        Variable j: Job.

        (* First, we show that if job j is scheduled, then it must be pending. *)
        Lemma scheduled_implies_pending:
          forall t,
            scheduled_at sched j t -> pending j t.
        Proof.
          rename H_jobs_execute_after_jitter into ARR,
          H_completed_jobs into COMP.
          unfold jobs_must_arrive_to_execute, completed_jobs_dont_execute in *.
          intros t SCHED.
          unfold pending; apply/andP; split; first by apply ARR.
          apply/negP; unfold not; intro COMPLETED.
          have BUG := COMP j t.+1.
          rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
          unfold service, service_during; rewrite -addn1 big_nat_recr // /=.
            by apply leq_add; last rewrite /service_at SCHED.
        Qed.

      End Pending.

    End Lemmas.

  End RedefiningProperties.

End UniprocessorScheduleWithJitter.