Require Import Arith.
Require Import  prosa.classic.util.all
                prosa.classic.model.arrival.basic.job
                prosa.classic.model.arrival.basic.task_arrival
                prosa.classic.model.schedule.uni.schedulability
                prosa.classic.model.schedule.uni.schedule_of_task 
                prosa.classic.model.schedule.uni.response_time
                prosa.classic.analysis.uni.basic.tdma_wcrt_analysis.
Require Import  prosa.classic.model.schedule.uni.basic.platform_tdma
                prosa.classic.model.schedule.uni.end_time.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

Set Bullet Behavior "Strict Subproofs".

Module ResponseTimeAnalysisTDMA.
  
  Import Job  TaskArrival ScheduleOfTask  ResponseTime Platform_TDMA end_time Schedulability
        WCRT_OneJobTDMA.

  (* In this section, we establish that the computed value WCRT of the exact response-time analysis
     yields an upper bound on the response time of a task under TDMA scheduling policy on an uniprocessor, 
     assuming that such value is no larger than the task period. *)

  Section ResponseTimeBound.

    (** System model *)
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_sporadic_tasks:
    sporadic_task_model task_period job_arrival job_task arr_seq.

    (* ...and any uniprocessor... *)
    Variable sched: schedule Job.
    (* ... where jobs do not execute before their arrival times nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Consider any TDMA slot assignment... *)
    Variable task_time_slot: TDMA_slot sporadic_task.
    (* ... and any slot order. *)
    Variable slot_order: TDMA_slot_order sporadic_task.

    (* Consider any task set ts. *)
    Variable ts: {set sporadic_task}.
    Hypothesis H_valid_task_parameters:
    valid_sporadic_taskset task_cost task_period task_deadline ts.

    (* Consider any task in task set. *)
    Variable tsk:sporadic_task.
    Hypothesis H_task_in_task_set: tsk \in ts.

    (* For simplicity, let us use local names for some definitions and refer them to local variables. *)
    (* Recall definition: whether a job can be scheduled at time t *)
    Let is_scheduled_at j t:= 
      scheduled_at sched j t.
    (* Recall definition: whether a task is in its own time slot at time t *)
    Let in_time_slot_at j t:= 
        Task_in_time_slot ts slot_order (job_task j) task_time_slot t.

   (* Recall the definition of response-time bound. *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched. 

    (* Let (RT j) denote the computed response-time of job j according to the TDMA analysis.
       Note that this computation assumes that there is only one pending job of each task.
       Still, this assumption doesn't break the generality of the proof. There cannot be
       multiple jobs of the same task because:
       (a) assumption: the computed value WCRT is bounded by its task's period; and
       (b) the lemma: "jobs_finished_before_WCRT" in file tdma_wcrt_analysis.v. *)
    Hypothesis WCRT_le_period:
      WCRT task_cost task_time_slot ts tsk <= task_period tsk.
    Let RT j:= job_response_time_tdma_in_at_most_one_job_is_pending job_arrival job_cost
         task_time_slot slot_order ts tsk j.

    (* Next, recall the definition of deadline miss of tasks and jobs. *)
    Let no_deadline_missed_by_task :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.
    Let no_deadline_missed_by_job :=
      job_misses_no_deadline job_arrival job_cost job_deadline sched.

    (* Then, we define a valid TDMA bound. *)
    (* Bound is valid bound iff it is less than or equal to task's deadline *)
    Definition is_valid_tdma_bound bound :=
         (bound <= task_deadline tsk).

    (* Now, let's assume that the schedule respects TDMA scheduling policy... *)
    Hypothesis TDMA_policy:
      Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order.

    (* ..., that task time slot is valid... *)
    Hypothesis H_valid_time_slot:
      is_valid_time_slot tsk task_time_slot.

    (* ... and that any job in arrival sequence is a valid job. *)
    Hypothesis H_valid_job_parameters:
      forall j, arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Assume that job cost is less than or equal to its task cost. *)
    Hypothesis H_job_cost_le_task_cost: 
      forall j, arrives_in arr_seq j ->
      job_cost_le_task_cost task_cost job_cost job_task j.

    (* Let BOUND be the computed WCRT of tsk. *)
    Let BOUND := WCRT task_cost task_time_slot ts tsk.

    (** Two basic lemmas  *)
    (* Having assumed that the computed BOUND <= task_period tsk, we first prove that
       any job of task tsk must have completed by its period. *)
    Lemma any_job_completed_before_period:
      forall j,
        arrives_in arr_seq j ->
        job_task j = tsk ->
        completed_by job_cost sched j (job_arrival j + task_period  (job_task j) ).
    Proof.
      intros j [t ARR]. generalize dependent j.
      induction t as [ t IHt ] using (well_founded_induction lt_wf).
      case t eqn:GT;intros. 
      - have INJ: arrives_in arr_seq j by exists 0.
        (apply completion_monotonic with (t0:=job_arrival j + WCRT task_cost task_time_slot ts tsk )
        ;trivial;try by rewrite leq_add2l H); apply job_completed_by_WCRT
        with (task_deadline0:=task_deadline)
                 (arr_seq0:=arr_seq)(job_deadline0:=job_deadline)
                 (job_task0:=job_task)(slot_order0:=slot_order);eauto 2.
        intros. apply H_arrival_times_are_consistent in ARR. ssromega.
      - have INJ: arrives_in arr_seq j by exists n.+1.
        apply completion_monotonic 
          with (t0:=job_arrival j + WCRT task_cost task_time_slot ts tsk);auto.
        by rewrite leq_add2l H. apply job_completed_by_WCRT
        with (task_deadline0:=task_deadline)
                 (arr_seq0:=arr_seq)(job_deadline0:=job_deadline)
                 (job_task0:=job_task)(slot_order0:=slot_order);auto. 
        intros.
        have PERIOD: job_arrival j_other + task_period (job_task j_other)<= job_arrival j.
        apply H_sporadic_tasks;auto. case (j==j_other)eqn: JJ;move/eqP in JJ;last auto.
        have JO:job_arrival j_other = job_arrival j by f_equal. ssromega.
        apply completion_monotonic with (t0:= job_arrival j_other +
           task_period (job_task j_other)); auto.
        have ARRJ: job_arrival j = n.+1 by auto.
        apply (IHt (job_arrival j_other));auto. ssromega.
        destruct H0 as [tj AAJO]. have CONSIST: job_arrival j_other =tj by auto.
        by subst. by subst.
    Qed.

    (* Based on the lemma above and the fact that jobs arrive sporadically, we can conclude that
       all the previous jobs of task tsk must have completed before the analyzed job j. *)
    Lemma all_previous_jobs_of_same_task_completed :
      forall j j_other,
        arrives_in arr_seq j ->
        job_task j = tsk ->
        arrives_in arr_seq j_other ->
        job_task j = job_task j_other ->
        job_arrival j_other < job_arrival j ->
        completed_by job_cost sched j_other (job_arrival j).
    Proof.
      intros.
      have PERIOD: job_arrival j_other + task_period (job_task j_other)<= job_arrival j.
      apply H_sporadic_tasks;auto. case (j==j_other)eqn: JJ;move/eqP in JJ;last auto. 
      have JO:job_arrival j_other = job_arrival j by f_equal. ssromega.
      apply completion_monotonic with (t:=job_arrival j_other + task_period (job_task j_other));auto.
      apply any_job_completed_before_period;auto. by subst.
    Qed.

    (** Main Theorem *)
    (* Therefore, we proved that the reponse time of task tsk is bouned by the 
       BOUND i.e., the computed value WCRT according to TDMA scheduling policy on an uniprocessor.
      ( for more details, see
        response_time_le_WCRT: .
        completed_by_end_time: model/schedule/uni/end_time.v
        completes_at_end_time: model/schedule/uni/end_time.v
      ) *)
    Theorem uniprocessor_response_time_bound_TDMA: response_time_bounded_by tsk BOUND.
    Proof.
      intros j arr_seq_j JobTsk.
      apply completion_monotonic with (t:=job_arrival j + RT j); try done. 
      - rewrite leq_add2l /BOUND. 
        apply (response_time_le_WCRT) 
        with (task_cost0:=task_cost) (task_deadline0:=task_deadline)(sched0:=sched)
             (job_arrival0:=job_arrival)(job_cost0:=job_cost)(job_deadline0:=job_deadline)
             (job_task0:=job_task)(ts0:=ts)(arr_seq0:=arr_seq)
             (slot_order0:=slot_order)(Job0:=Job)(tsk0:=tsk); try done;auto;try (intros; 
        by apply all_previous_jobs_of_same_task_completed).
      - apply completed_by_end_time 
        with (sched0:=sched)(job_arrival0:=job_arrival)
             (job_cost0:=job_cost); first exact.
        apply completes_at_end_time
        with 
             (job_arrival0:=job_arrival)(task_cost0:=task_cost)(arr_seq0:=arr_seq)
             (job_task0:=job_task)(job_deadline0:=job_deadline)(task_deadline0:=task_deadline)
             (sched0:=sched)(ts0:=ts)(slot_order0:=slot_order)
             (tsk0:=tsk) (j0:=j); try auto;try (intros; 
        by apply all_previous_jobs_of_same_task_completed).
    Qed. 

    (** Sufficient Analysis *)
    (* Finally, we show that the RTA is a sufficient schedulability analysis. *)
    Section AnalysisIsSufficient.

      (* Assume that BOUND is a valid tdma bound *)
      Hypothesis H_is_valid_bound:
        is_valid_tdma_bound BOUND.

      (* We can prove the theorem: there is no deadline miss of task tsk *)
      Theorem taskset_schedulable_by_tdma : no_deadline_missed_by_task tsk.
      Proof.
        apply task_completes_before_deadline with (task_deadline0:=task_deadline) (R:=BOUND)
        ;try done.
        move => j arr_seqJ.
        - by apply H_valid_job_parameters.
        - apply uniprocessor_response_time_bound_TDMA.
      Qed.

      (* Based on the theorem above, we can prove that
         any job of the arrival sequence are spawned by task tsk won't miss its deadline. *)
      Theorem jobs_schedulable_by_tdma_rta :
        forall j,
          arrives_in arr_seq j /\ job_task j =tsk -> 
          no_deadline_missed_by_job j.
      Proof.
        intros j [arr_seqJ Jtsk].
        by apply taskset_schedulable_by_tdma.
      Qed.

    End AnalysisIsSufficient.

  End ResponseTimeBound.

End ResponseTimeAnalysisTDMA.



