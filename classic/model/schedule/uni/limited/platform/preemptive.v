Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task
               prosa.classic.model.priority
               prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.basic.platform.
Require Export prosa.classic.model.schedule.uni.limited.platform.definitions.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Platform for fully premptive model *)
(** In module uni.limited.platform we introduce the notion of whether a job can be preempted 
   at a given time (using a predicate can_be_preempted). In this section, we instantiate 
   can_be_preempted for the fully preemptive model and prove its correctness. *)
Module FullyPreemptivePlatform.

  Import Job SporadicTaskset UniprocessorSchedule Priority
         Service LimitedPreemptionPlatform.
  
  Section FullyPreemptiveModel.
    
    Context {Task: eqType}.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence ...*)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule of these jobs. *)  
    Variable sched: schedule Job. 

    (* For simplicity, let's define some local names. *)
    Let job_pending := pending job_arrival job_cost sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_scheduled_at := scheduled_at sched.

    (* In the fully preemptive model any job can be preempted at any time. *)
    Definition can_be_preempted_for_fully_preemptive_model (j: Job) (progr: time) := true.
    
    (* Since in a fully preemptive model a job can be preempted at 
       any time job_max_nps cannot be greater than ε. *) 
    Let job_max_nps (j: Job) := ε.

    (*  In order to bound job_max_nps, we can choose task_max_nps that is equal to ε for any task. *)
    Let task_max_nps (tsk: Task) := ε.
    
    (* Then, we prove that fully_preemptive_model is a correct preemption model... *)
    Lemma fully_preemptive_model_is_correct:
      correct_preemption_model arr_seq sched can_be_preempted_for_fully_preemptive_model.
    Proof. by intros j; split; intros t CONTR. Qed.

    (* ... and has bounded nonpreemptive regions. *)
    Lemma fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions:
      model_with_bounded_nonpreemptive_segments
        job_cost job_task arr_seq can_be_preempted_for_fully_preemptive_model job_max_nps task_max_nps.
    Proof.
      intros j; repeat split; try done. 
      intros t; exists t; split.
      { by apply/andP; split; [ done | rewrite subnn addn0]. }
      { by done. }
    Qed.

  End FullyPreemptiveModel.

End FullyPreemptivePlatform.