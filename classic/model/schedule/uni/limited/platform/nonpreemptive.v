Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task 
               prosa.classic.model.priority
               prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.
Require Export prosa.classic.model.schedule.uni.limited.platform.definitions.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Platform for fully nonpreemptive model *)
(** In module uni.limited.platform we introduce the notion of whether a job can be preempted 
   at a given time (using a predicate can_be_preempted). In this section, we instantiate 
   can_be_preempted for the fully nonpreemptive model and prove its correctness. *)
Module FullyNonPreemptivePlatform.

  Import Job SporadicTaskset UniprocessorSchedule Priority
         Service LimitedPreemptionPlatform.
  
  Section FullyNonPreemptiveModel.
    
    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any arrival sequence with consistent, non-duplicate arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.
    
    (* Next, consider any uniprocessor nonpreemptive schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.
    Hypothesis H_nonpreemptive_sched:
      NonpreemptiveSchedule.is_nonpreemptive_schedule job_cost sched.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
    
    (* For simplicity, let's define some local names. *)
    Let job_pending := pending job_arrival job_cost sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_scheduled_at := scheduled_at sched.

    (* Assume that a job cost cannot be larger than a task cost. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq.
    
    (* We say that the model is fully nonpreemptive 
       iff every job cannot be preempted until its completion. *)
    Definition can_be_preempted_for_fully_nonpreemptive_model (j: Job) (progr: time) :=
      (progr == 0) || (progr == job_cost j).

    (* Since in a fully nonpreemptive model a job cannot be preempted after 
       it starts the execution, job_max_nps is equal to job_cost. *) 
    Let job_max_nps (j: Job) := job_cost j.

    (* In order to bound job_max_nps, task_max_nps should be equal to task_cost. *)
    Let task_max_nps (tsk: Task) := task_cost tsk.
    
    (* Then, we prove that fully_nonpreemptive_model is a correct preemption model... *)
    Lemma fully_nonpreemptive_model_is_correct:
      correct_preemption_model arr_seq sched can_be_preempted_for_fully_nonpreemptive_model.
    Proof.
      intros j; split.
      { move => t. 
        rewrite /can_be_preempted_for_fully_nonpreemptive_model Bool.negb_orb -lt0n. 
        move => /andP [POS NCOMPL].
        unfold NonpreemptiveSchedule.is_nonpreemptive_schedule in *. 
        move: (incremental_service_during _ _ _ _ _ POS) => [ft [/andP [_ LT] [SCHED SERV]]].
        apply H_nonpreemptive_sched with ft.
        { by apply ltnW. }
        { by done. } 
        { rewrite /completed_by -ltnNge.
          move: NCOMPL; rewrite neq_ltn; move => /orP [LE|GE]; [by done | exfalso].
          move: GE; rewrite ltnNge; move => /negP GE; apply: GE.
            by eauto 2.
        }
      }
      { intros t NSCHED SCHED.
        rewrite /can_be_preempted_for_fully_nonpreemptive_model. 
        apply/orP; left. 
        apply/negP; intros CONTR. 
        move: CONTR => /negP; rewrite -lt0n; intros POS. 
        move: (incremental_service_during _ _ _ _ _ POS) => [ft [/andP [_ LT] [SCHEDn SERV]]].
        move: NSCHED => /negP NSCHED; apply: NSCHED.
        apply H_nonpreemptive_sched with ft.
        { by rewrite -ltnS. }
        { by done. }
        { rewrite /completed_by -ltnNge.
          apply leq_ltn_trans with (service sched j t.+1).  
          { by rewrite /service /service_during big_nat_recr //= leq_addr. }
          { rewrite -addn1.
            apply leq_trans with (service sched j t.+2).
            - unfold service, service_during.
              have EQ: (service_at sched j t.+1) = 1.
              { by apply/eqP; rewrite eqb1. }
                by rewrite -EQ -big_nat_recr //=.
            - by eauto 2.
          }
        } 
      }
    Qed.

    (* ... and has bounded nonpreemptive regions. *)
    Lemma fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions:
      model_with_bounded_nonpreemptive_segments
        job_cost job_task arr_seq can_be_preempted_for_fully_nonpreemptive_model job_max_nps task_max_nps.
    Proof. 
      have F: forall n, n = 0 \/ n > 0.
      { by intros n; destruct n; [left | right]. }
      intros j; split; last split; last split.
      { by done. }
      { by apply/orP; right. }
      { intros ARR.
        rewrite /job_max_nps /task_max_nps.
          by eauto 2.
      } 
      { intros progr.
        move: (F (progr)) => [EQ | GT].
        { exists progr; split.
          - by apply/andP; split; [done | rewrite leq_addr].
          - by rewrite /can_be_preempted_for_fully_nonpreemptive_model EQ. }
        { exists (maxn progr (job_cost j)).
          have POS: 0 < job_cost j.
          { by apply leq_trans with progr; last move: H0 => /andP [_ H0]. } 
          split.
          { apply/andP; split; first by rewrite leq_maxl. 
            rewrite /job_max_nps addnBA; last eauto 2.
            rewrite geq_max; apply/andP; split.
            - rewrite -addnBA; last by eauto 2.
                  by rewrite leq_addr.
            - by rewrite addnC -addnBA // leq_addr.
          }
          { unfold can_be_preempted_for_fully_nonpreemptive_model.
            apply/orP; right.
            move: H0 => /andP [_ LE].
            rewrite eqn_leq; apply/andP; split.
            - by rewrite geq_max; apply/andP; split.
            - by rewrite leq_max; apply/orP; right.
          }
        }
      }
    Qed.

  End FullyNonPreemptiveModel.

End FullyNonPreemptivePlatform.