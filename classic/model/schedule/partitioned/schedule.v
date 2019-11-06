Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.task rt.model.arrival.basic.job.
Require Import rt.model.schedule.global.schedulability.
Require Import rt.model.schedule.global.basic.schedule.
Require rt.model.schedule.uni.schedule rt.model.schedule.uni.schedulability.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Partitioned.

  Module uni := rt.model.schedule.uni.schedule.UniprocessorSchedule.
  Module uni_sched := rt.model.schedule.uni.schedulability.Schedulability.
  Import SporadicTaskset Schedule Schedulability.
  Export Time.
  
  Section PartitionedDefs.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.

    (* Given any multiprocessor schedule of these jobs, ... *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* ... we define a notion of "partitioned scheduling" (= no migrations) on
      a per-job, per-task, and finally whole-schedule level. *)

    Section NoJobMigration.

      (* A job is "partitioned" iff it never migrates, i.e., it
       * executes on the same processor whenever it is scheduled. *)

      (* So any job j... *)
      Variable j: Job.

      (* ... never migrates iff the following holds: ... *)
      Definition never_migrates :=
        (* ...for any point in time t... *)
        forall t,
          (* ...and any processor cpu... *)
        forall cpu,
          (* ... if job j is scheduled at time t on processor cpu... *)
          scheduled_on sched j cpu t ->
          (* ...then at any other time... *)
          forall t',
            (* ...if the same job is scheduled, it must be scheduled on
             * the same processor. *)
            forall cpu',
              scheduled_on sched j cpu' t' -> cpu' = cpu.

      (* Furthermore, we say that the job is assigned to processor assigned_cpu
       * if it executes only on that processor. *)
      Variable assigned_cpu : processor num_cpus.
      Definition job_local_to_processor :=
        forall t, forall cpu,
          scheduled_on sched j cpu t -> cpu = assigned_cpu.

    End NoJobMigration.
    
    (* Having defined a notiont of 'partitioned' for individual jobs, let us
     * now turn to tasks. *)

    Section NoTaskMigration.

      (* Given any task tsk in ts, ... *)
      Variable tsk: Task.

      (* ...we say that tsk is assigned to processor assigned_cpu ... *)
      Variable assigned_cpu : processor num_cpus.

      (* ...iff every job of tsk executes exclusively on assigned_cpu. *)
      Definition task_local_to_processor :=
        forall j,
          job_task j = tsk ->
          job_local_to_processor j assigned_cpu.

    End NoTaskMigration.

    (* Finally, a schedule is fully partitioned iff every task is assigned
       to some processor. *)
    Section PartitionedSchedule.

      (* Consider a task set ts to be scheduled. *)
      Variable ts: list Task.
      
      (* Given an assignment from every task in ts to a processor, ...*)
      Variable assigned_cpu: Task -> processor num_cpus.

      (* ...we say that a schedule is partitioned iff every task is local
         to the corresponding processor. *)
      Definition partitioned_schedule :=
        forall tsk,
          tsk \in ts ->
          task_local_to_processor tsk (assigned_cpu tsk).
      
    End PartitionedSchedule.

  End PartitionedDefs.

  Section SimpleProperties.

    Context {Job: eqType}.

    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    Section NoJobMigrationLemmas.

      Variable j: Job.

      Lemma local_jobs_dont_migrate:
        forall cpu,
          job_local_to_processor sched j cpu -> never_migrates sched j.
      Proof.
        rewrite /job_local_to_processor /never_migrates
             =>  cpu H_is_local t cpu' H_sched_at_t t' cpu'' H_sched_at_t'.
        apply H_is_local in H_sched_at_t.
        apply H_is_local in H_sched_at_t'.
        by rewrite H_sched_at_t H_sched_at_t'.
      Qed.

    End NoJobMigrationLemmas.

  End SimpleProperties.

End Partitioned.