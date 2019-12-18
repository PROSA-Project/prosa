Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.limited.schedule
               prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Lock-in service of a job *)
(** In this module, we provide a sufficient condition under which a job 
    receives enough service to become nonpreemptive. *)
Module AbstractRTALockInService. 

  Import Job UniprocessorSchedule Service  AbstractRTADefinitions.

  (* Previously we defined the notion of lock-in service (see limited.schedule.v file). 
     Lock-in service is the amount of service after which a job cannot be preempted until 
     its completion. In this section we prove that if cumulative interference inside a 
     busy interval is bounded by a certain constant then a job executes long enough to 
     reach its lock-in service and become nonpreemptive. *)
  Section LockInService.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.    
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any arrival sequence with consistent arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    
    (* Next, consider any uniprocessor schedule of this arrival sequence. *)
    Variable sched: schedule Job.

    (* Assume that the job costs are no larger than the task costs. *)
    Hypothesis H_job_cost_le_task_cost:
      cost_of_jobs_from_arrival_sequence_le_task_cost
        task_cost job_cost job_task arr_seq. 

    (* Let tsk be any task that is to be analyzed. *)
    Variable tsk: Task.
    
    (* Assume we are provided with abstract functions for interference and interfering workload. *)
    Variable interference: Job -> time -> bool.
    Variable interfering_workload: Job -> time -> time.

    (* For simplicity, let's define some local names. *)
    Let work_conserving := work_conserving job_arrival job_cost job_task arr_seq sched tsk.
    Let cumul_interference := cumul_interference interference.
    Let cumul_interfering_workload := cumul_interfering_workload interfering_workload.
    Let busy_interval := busy_interval job_arrival job_cost sched interference interfering_workload.
    
    (* We assume that the schedule is work-conserving. *)
    Hypothesis H_work_conserving: work_conserving interference interfering_workload.

    (* Let j be any job of task tsk with positive job cost. *)
    Variable j: Job. 
    Hypothesis H_j_arrives: arrives_in arr_seq j.
    Hypothesis H_job_of_tsk: job_task j = tsk.
    Hypothesis H_job_cost_positive: job_cost_positive job_cost j.

    (* Next, consider any busy interval [t1, t2) of job j. *)
    Variable t1 t2: time.
    Hypothesis H_busy_interval: busy_interval j t1 t2.

    (* First, we prove that job j completes by the end of the busy interval. 
       Note that the busy interval contains the execution of job j, in addition
       time instant t2 is a quiet time. Thus by the definition of a quiet time
       the job should be completed before time t2. *)
    Lemma job_completes_within_busy_interval:
      completed_by job_cost sched j t2.
    Proof.
      move: (H_busy_interval) => [[/andP [_ LT] [_ _]] [_ QT2]].
      unfold pending, has_arrived in QT2.
      move: QT2; rewrite  /pending negb_and; move => /orP [QT2|QT2].
      { by move: QT2 => /negP QT2; exfalso; apply QT2, ltnW. }
        by rewrite Bool.negb_involutive in QT2.
    Qed.

    (* In this section we show that the cumulative interference is a complement to 
       the total time where job j is scheduled inside the busy interval. *)
    Section InterferenceIsComplement.

      (* Consider any subinterval [t, t + delta) inside the busy interval [t1, t2). *)
      Variable t delta: time.
      Hypothesis H_greater_than_or_equal: t1 <= t.
      Hypothesis H_less_or_equal: t + delta <= t2.
      
      (* We prove that sum of cumulative service and cumulative interference 
         in the interval [t, t + delta) is equal to delta. *)
      Lemma interference_is_complement_to_schedule:
        service_during sched j t (t + delta) + cumul_interference j t (t + delta) = delta.
      Proof. 
        rewrite /service_during /cumul_interference.  
        rewrite -big_split //=.
        rewrite -{2}(sum_of_ones t delta).
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        - rewrite [X in X <= _]big_nat_cond [X in _ <= X]big_nat_cond.
          apply leq_sum; move => x /andP [/andP [GE2 LT2] _ ].
          case IJX: (interference j x); last by rewrite addn0 /service_at; case scheduled_at. 
          rewrite addn1 ltnNge; apply/negP; intros CONTR.
          specialize (H_work_conserving j t1 t2 x).
          feed_n 5 H_work_conserving; try done.
          { apply/andP; split.
            apply leq_trans with t; try done.
            apply leq_trans with (t + delta); try done.
          }
          move: H_work_conserving => [H1 H2].
          feed H2. rewrite lt0b in CONTR. by done.
            by rewrite IJX in H2.
        - rewrite [X in X <= _]big_nat_cond [X in _ <= X]big_nat_cond.
          apply leq_sum; move => x /andP [/andP [GE2 LT2] _ ].
          case IJX: (interference j x); first by rewrite addn1.
          rewrite addn0.
          specialize (H_work_conserving j t1 t2 x); feed_n 5 H_work_conserving; try done.
          { apply/andP; split.
            apply leq_trans with t; try done.
            apply leq_trans with (t + delta); try done. }
          move: H_work_conserving => [H1 H2].
          feed H1; first by rewrite IJX.
            by rewrite lt0b.
      Qed.

    End InterferenceIsComplement.

    (* In this section, we prove a sufficient condition under which job j receives enough service. *)
    Section InterferenceBoundedImpliesEnoughService.

      (* Let progress_of_job be the desired service of job j. *)
      Variable progress_of_job: time.
      Hypothesis H_progress_le_job_cost: progress_of_job <= job_cost j.
      
      (* Assume that for some delta, the sum of desired progress and cumulative 
         interference is bounded by delta (i.e., the supply). *)
      Variable delta: time.
      Hypothesis H_total_workload_is_bounded:
        progress_of_job + cumul_interference j t1 (t1 + delta) <= delta.

      (* Then, it must be the case that the job has received no less service than progress_of_job. *)
      Theorem j_receives_at_least_lock_in_service: 
        service sched j (t1 + delta) >= progress_of_job.
      Proof.
        case NEQ: (t1 + delta <= t2); last first.
        { intros.
          have L8 := job_completes_within_busy_interval.
          apply leq_trans with (job_cost j); first by done.
          rewrite /service.
          rewrite (service_during_cat _ _ t2).
          apply leq_trans with (service_during sched j 0 t2); [by done | by rewrite leq_addr].
            by apply/andP; split; last (apply negbT in NEQ; apply ltnW; rewrite ltnNge).
        } 
        { move: H_total_workload_is_bounded => BOUND.
          apply subh3 in BOUND.
          apply leq_trans with (delta - cumul_interference j t1 (t1 + delta)); first by done.
          apply leq_trans with (service_during sched j t1 (t1 + delta)).
          { rewrite -{1}[delta](interference_is_complement_to_schedule t1) //. 
            rewrite -addnBA // subnn addn0 //.
          }
          { unfold service.
            rewrite [X in _ <= X](service_during_cat _ _ t1).
            rewrite leq_addl //.
              by apply/andP; split; last rewrite leq_addr.
          }
        }
      Qed.
      
    End InterferenceBoundedImpliesEnoughService.

    (* In this section we prove a simple lemma about completion of 
       a job after is reaches lock-in service. *)
    Section CompletionOfJobAfterLockInService.

      (* Assume that completed jobs do not execute. *)
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.
      
      (* Consider a proper job lock-in service function, i.e... *)
      Variable job_lock_in_service: Job -> time.

      (* ...(1) for any job j the lock-in service of job j is positive... *)
      Hypothesis H_lock_in_service_positive:
        job_lock_in_service_positive job_cost arr_seq job_lock_in_service.
      
      (* ...(2) it also less-than-or-equal to the job_cost... *)
      Hypothesis H_lock_in_service_le_job_cost:
        job_lock_in_service_le_job_cost job_cost arr_seq job_lock_in_service.

      (* ..., and (3) we assume that the scheduler respects the notion of the lock-in service. *)
      Hypothesis H_job_nonpreemptive_after_lock_in_service:
        job_nonpreemptive_after_lock_in_service job_cost arr_seq sched job_lock_in_service.

      (* Then, job j must complete in [job_cost j - job_lock_in_service j] time 
         units after it reaches lock-in service. *)
      Lemma job_completes_after_reaching_lock_in_service:
        forall t,
          job_lock_in_service j <= service sched j t -> 
          completed_by job_cost sched j (t + (job_cost j - job_lock_in_service j)).
      Proof. 
        move => t ES.
        set (job_cost j - job_lock_in_service j) as job_last.
        move: (H_job_nonpreemptive_after_lock_in_service j t) => LSNP. 
        apply negbNE; apply/negP; intros CONTR.
        have SCHED: forall t', t <= t' <= t + job_last -> scheduled_at sched j t'.
        { move => t' /andP [GE LT].
          rewrite -[t'](@subnKC t) //.
          apply LSNP; [ by apply H_j_arrives | by rewrite leq_addr | by done | ].
          rewrite subnKC //.
          apply/negP; intros COMPL.
          move: CONTR => /negP Temp; apply: Temp.
          apply completion_monotonic with (t0 := t'); try done.
        }
        have SERV: job_last + 1 <= \sum_(t <= t' < t + (job_last + 1)) service_at sched j t'.
        { rewrite -{1}[job_last + 1]addn0  -{2}(subnn t) addnBA // addnC.
          rewrite -{1}[_+_-_]addn0 -[_+_-_]mul1n -iter_addn -big_const_nat.
          rewrite big_nat_cond [in X in _ <= X]big_nat_cond.
          rewrite leq_sum //.
          move => t' /andP [NEQ _].
          rewrite /service_at lt0b.
          apply SCHED.
            by rewrite addn1 addnS ltnS in NEQ.
        }
        move: (H_completed_jobs_dont_execute j (t + job_last.+1)).
        rewrite /completed_jobs_dont_execute.
        rewrite leqNgt; move => /negP T; apply: T.
        rewrite /service (service_during_cat _ _ t); last by (apply/andP; split; last rewrite leq_addr).
        apply leq_trans with (
          job_lock_in_service j + service_during sched j t (t + job_last.+1));
          last by rewrite leq_add2r.
        apply leq_trans with  (job_lock_in_service j + job_last.+1); last by rewrite leq_add2l /service_during -addn1.
          by rewrite addnS ltnS subnKC; eauto 2.
      Qed.
 
    End CompletionOfJobAfterLockInService.
    
  End LockInService.

End AbstractRTALockInService.

