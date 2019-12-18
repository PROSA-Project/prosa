Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.arrival_sequence prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.partitioned.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Require prosa.classic.model.schedule.uni.schedule.

Module PartitionSchedulability.
  
  Module uni_sched := prosa.classic.model.schedule.uni.schedulability.Schedulability.
  Import ArrivalSequence Partitioned Schedule Schedulability.

  Section PartitionedAsUniprocessor.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any job arrival sequence that is to be scheduled. *)
    Variable arr_seq: arrival_sequence Job.
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* Assume that all jobs in the arrival sequence come from a task set ts. *)
    Variable ts: list Task.
    Hypothesis H_all_jobs_from_ts:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Also assume that every task is assigned to a processor, ... *)
    Variable assigned_cpu: Task -> processor num_cpus.

    (* ...forming a partitioned schedule. *)
    Hypothesis H_partitioned: partitioned_schedule job_task sched ts assigned_cpu.

    (* Next, we related total service with per-processor service received by each job. *)
    Section SameService.

      (* Consider the partition where each job is assigned to. *)
      Let partition_of j := assigned_cpu (job_task j).

      (* Let j be any job. *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      
      (* We prove that the service received by job j (on the multiprocessor)
         is the same as the service received by job j in its partition. *)
      Lemma same_per_processor_service :
        forall t1 t2,
          service_during sched j t1 t2 =
          uni.service_during (sched (partition_of j)) j t1 t2.
      Proof.
        intros t1 t2.
        unfold partitioned_schedule, task_local_to_processor,
               job_local_to_processor, service_during, service_at,
               uni.service_during, uni.service_at,
               uni.scheduled_at, scheduled_on, partition_of in *.
        rename H_partitioned into PART, H_all_jobs_from_ts into FROMTS.
        apply eq_bigr; intros t _.
        unfold uni.service_at, uni.scheduled_at.
        feed (PART (job_task j)); first by apply FROMTS.
        feed (PART j); first by done.
        specialize (PART t).
        destruct (scheduled sched j t) eqn:SCHED; last first.
        {
          apply negbT in SCHED; rewrite negb_exists in SCHED.
          move: SCHED => /forallP SCHED.
          have SCHEDcpu := SCHED (assigned_cpu (job_task j)); apply negbTE in SCHEDcpu.
          unfold scheduled_on in *; rewrite SCHEDcpu.
          rewrite big1; first by done.
          move => cpu /eqP SCHED'.
          by specialize (SCHED cpu); rewrite SCHED' eq_refl in SCHED.
        }
        {
          move: SCHED => /existsP [cpu SCHED].
          rewrite (bigD1 cpu) /=; last by done.
          have SAME := PART cpu SCHED; rewrite -SAME.
          unfold scheduled_on in *; rewrite SCHED.
          rewrite add1n; apply/eqP; rewrite eqSS; apply/eqP.
          rewrite big1; first by done.
          move => cpu' /andP [SCHED' NEQ].
          have SAME' := (PART cpu' SCHED'); subst cpu cpu'.
          by rewrite eq_refl in NEQ.
        }
      Qed.
        
    End SameService.

    Section Schedulability.

      (* Recall the definitions of schedulability on a uniprocessor and on
         a multiprocessor. *)
      Let schedulable_on tsk cpu :=
        uni_sched.task_misses_no_deadline job_arrival job_cost job_deadline job_task
                                                               arr_seq (sched cpu) tsk.
      Let schedulable :=
        task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched.


      (* Here we prove that if every task is schedulable in their assigned processors, ...*)
      Hypothesis H_locally_schedulable:
        forall tsk,
          tsk \in ts -> schedulable_on tsk (assigned_cpu tsk).

      (* ...then every task is schedulable at the level of the multiprocessor system. *)
      Lemma schedulable_at_system_level:
        forall tsk,
          tsk \in ts -> schedulable tsk.
      Proof.
        have SAME := same_per_processor_service.
        unfold partitioned_schedule, task_local_to_processor,
               job_local_to_processor, schedulable, schedulable_on,
               task_misses_no_deadline, job_misses_no_deadline,
               completed, uni_sched.task_misses_no_deadline,
               uni_sched.job_misses_no_deadline, uni.completed_by in *.
        rename H_locally_schedulable into SCHED,
               H_partitioned into PART.
        intros tsk IN j ARRj JOBtsk.
        specialize (SCHED tsk IN j ARRj JOBtsk).
        unfold service, uni.service, service_during, uni.service_during in *.
          by rewrite SAME // JOBtsk.
      Qed.

    End Schedulability.

  End PartitionedAsUniprocessor.
  
End PartitionSchedulability.