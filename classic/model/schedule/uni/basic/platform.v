Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.schedule.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import Job SporadicTaskset UniprocessorSchedule Priority.

  (* In this section, we define properties of the processor platform. *)
  Section Properties.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any job arrival sequence ...*)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* First, we define properties related to execution. *)
    Section Execution.

      (* We say that a scheduler is work-conserving iff whenever a job j
         is backlogged, the processor is always busy with another job. *)
      Definition work_conserving :=
        forall j t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          exists j_other, scheduled_at sched j_other t.

    End Execution.

    (* Next, we define properties related to FP scheduling. *)
    Section FP.

      (* We say that an FP policy...*)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* ...is respected by the schedule iff a scheduled task has
         higher (or same) priority than (as) any backlogged task. *)
      Definition respects_FP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority (job_task j_hp) (job_task j).

    End FP.
    
    (* Next, we define properties related to JLFP policies. *)
    Section JLFP.

      (* We say that a JLFP policy ...*)
      Variable higher_eq_priority: JLFP_policy Job.

      (* ... is respected by the scheduler iff a scheduled job has
         higher (or same) priority than (as) any backlogged job. *)
      Definition respects_JLFP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority j_hp j.
      
    End JLFP.

    (* Next, we define properties related to JLDP policies. *)
    Section JLDP.

      (* We say that a JLFP/JLDP policy ...*)
      Variable higher_eq_priority: JLDP_policy Job.

      (* ... is respected by the scheduler iff at any time t, a scheduled job
         has higher (or same) priority than (as) any backlogged job. *)
      Definition respects_JLDP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority t j_hp j.
      
    End JLDP.

  End Properties.

  (* In this section, we prove some lemmas about the processor platform. *)
  Section Lemmas.
      
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Consider any job arrival sequence ...*)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* For simplicity, let's define some local names. *)
    Let job_backlogged_at := backlogged job_arrival job_cost sched.
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_completed_by := completed_by job_cost sched.

    (* First we prove that if a job is never backlogged, then it doesn't take longer
       than its actual cost to complete. *)
    Section JobNeverBacklogged.

      (* Assume that jobs only execute after they arrive and no longer
         than their execution costs. *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched.
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.
      
      (* Assume that the schedule is work-conserving. *)
      Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
      
      (* Let j be any job... *)
      Variable j: Job.

      (* ...that j is never backlogged during its execution. *)
      Hypothesis H_j_is_never_backlogged:
        forall t,
          job_arrival j <= t < job_arrival j + job_cost j ->
          ~ job_backlogged_at j t.

      (* Then, any response-time bound no smaller than the job cost is safe. *)
      Lemma job_never_backlogged_response_time_holds:
        forall R,
          R >= job_cost j ->
          job_completed_by j (job_arrival j + R).
      Proof.
        rename H_j_is_never_backlogged into NEVER,
               H_work_conserving into WORK.
        intros R GECOST.
        rewrite /job_completed_by /completed_by /service /service_during.
        rewrite (ignore_service_before_arrival job_arrival);
          [ | by done | by done | by apply leq_addr].
        apply leq_trans with (n := \sum_(job_arrival j <= t < job_arrival j + job_cost j) 1);
          first by simpl_sum_const; rewrite addKn leqnn.
        apply leq_trans with (n := \sum_(job_arrival j <= t < job_arrival j + job_cost j)
                                      service_at sched j t);
          last by apply extend_sum; rewrite // leq_add2l.
        apply leq_sum_nat; move => t /andP [GEt LTt] _.
        rewrite lt0n eqb0; apply/negP; intro NOTSCHED.
        have BACK := NEVER t; feed BACK.
        {
          apply/andP; split; first by done.
          by apply leq_trans with (n := job_arrival j + job_cost j);
            [by done | by rewrite leq_add2l].
        }
        apply BACK; apply/andP; split; last by done.
        apply/andP; split; first by done.
        rewrite -ltnNge. 
        rewrite /service /service_during.
        rewrite -> big_cat_nat with (n := job_arrival j);
          [simpl | by done | by done].
        rewrite (cumulative_service_before_job_arrival_zero job_arrival);
          [rewrite add0n | by done | by apply leqnn].
        apply leq_ltn_trans with (n := \sum_(job_arrival j <= i < t) 1);
          first by apply leq_sum; ins; apply leq_b1.
        simpl_sum_const; rewrite -(ltn_add2r 1). 
        rewrite [job_cost j + 1]addn1 ltnS.
        by rewrite subh1 // leq_subLR addn1.
      Qed. 

    End JobNeverBacklogged.

  End Lemmas.
  
End Platform.