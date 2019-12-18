Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
 
Module NonpreemptivePlatform.

  Import Job SporadicTaskset UniprocessorSchedule Priority.

  (* In this section, we define properties of the processor platform. *)
  Section Properties.
    
    Context {sporadic_task: eqType}.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any job arrival sequence ...*)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* For simplicity, let's define some local names. *)
    Let job_completed_by := completed_by job_cost sched.
    Let job_scheduled_at := scheduled_at sched.

    (* First, we define the notion of a preemption point. *)
    Section PreemptionPoint.

      (* We say that t is a preemption point iff (a) t is equal to 0 
         or (b) there is no scheduling job at time t or 
         (c) a job that was scheduled at time (t - 1) and 
         has completed by t exists. *)
      Definition is_preemption_point' (t: time) :=
        t = 0
        \/ sched (t-1) = None
        \/ exists j, scheduled_at sched j (t - 1) /\ job_completed_by j t.

      (* Moreover, we provide a shorter definition, more convenient for the proofs. *)
      Definition is_preemption_point (t: time) :=
        t = 0 \/ forall j, job_scheduled_at j (t - 1) -> job_completed_by j t.

      (* Let's prove that the definitions above are equal. *)
      Lemma defitions_of_preemption_point_are_equal:
        forall t, is_preemption_point t <-> is_preemption_point' t.
      Proof.
        unfold is_preemption_point, is_preemption_point'.
        intros; split; intros.
        {
          destruct H as [H | H]; [by left | right].
          destruct (sched (t-1)) eqn:SCHED; [right; exists s | by left].
          move: SCHED => /eqP SCHED.
          by split; last by apply H in SCHED.
        }
        {
          destruct H as [H | [H | H]]; [by left| | ]; right; intros.
          unfold job_scheduled_at, scheduled_at in H0. rewrite H in H0. inversion H0.
          inversion H as [j' [H1 H2]]. unfold job_scheduled_at in H0.
          have EQ: j = j'. by apply (only_one_job_scheduled sched) with (t := t-1).
            by subst j'.
        }           
        Qed.

    End PreemptionPoint.
    
    (* Next, we define properties related to execution. *)
    Section Execution.

      (* We say that a scheduler is work-conserving iff whenever a job j
         is backlogged, the processor is always busy with another job. *)
      (* Imported from the preemptive schedule. *)
      Definition work_conserving := Platform.work_conserving job_cost.

    End Execution.

    (* Next, we define properties related to FP scheduling. *)
    Section FP.

      (* We say that an FP policy...*)
      Variable higher_eq_priority: FP_policy sporadic_task.
      
      (* ...is respected by the schedule iff a scheduled task has
         higher (or same) priority than (as) any backlogged task at 
         every preemption point. *)
      Definition respects_FP_policy_at_preemption_point :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_at sched j_hp t ->
          is_preemption_point t ->
          higher_eq_priority (job_task j_hp) (job_task j).
      
    End FP.
    
    (* Next, we define properties related to JLFP policies. *)
    Section JLFP.

      (* We say that a JLFP policy ...*)
      Variable higher_eq_priority: JLFP_policy Job.

      (* ... is respected by the scheduler iff a scheduled job has
         higher (or same) priority than (as) any backlogged job at
         every preemption point. *)      
      Definition respects_JLFP_policy_at_preemption_point :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_at sched j_hp t ->
          is_preemption_point t ->
          higher_eq_priority j_hp j.
      
    End JLFP.

  End Properties.
  
End NonpreemptivePlatform.