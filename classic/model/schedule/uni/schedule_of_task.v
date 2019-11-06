Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence.
Require Import rt.model.schedule.uni.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ScheduleOfTask.

  Export SporadicTaskset UniprocessorSchedule.

  (* In this section, we define properties about schedules of tasks. *)
  Section ScheduleProperties.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any uniprocessor schedule. *)
    Variable sched: schedule Job.

    Section TaskProperties.

      (* Let tsk be any task. *)
      Variable tsk: Task.

      (* Next we define whether a task is scheduled at time t, ... *)
      Definition task_scheduled_at (t: time) :=
        if sched t is Some j then
          job_task j == tsk
        else false.

      (* ...which also corresponds to the instantaneous service it receives. *)
      Definition task_service_at (t: time) : time := task_scheduled_at t.

      (* Based on the notion of instantaneous service, we define the
         cumulative service received by tsk during any interval [t1, t2)... *)
      Definition task_service_during (t1 t2: time) :=
        \sum_(t1 <= t < t2) task_service_at t.

      (* ...and the cumulative service received by tsk up to time t2,
         i.e., in the interval [0, t2). *)
      Definition task_service (t2: time) := task_service_during 0 t2.

    End TaskProperties.

  End ScheduleProperties.

End ScheduleOfTask.