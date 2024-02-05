Require Export prosa.analysis.abstract.abstract_rta.
Require Export prosa.analysis.abstract.IBF.supply.
Require Export prosa.analysis.abstract.IBF.task.

(** In this module, we define a _task-intra-supply_-interference-bound
    function ([task_intra_IBF]). Function [task_intra_IBF] bounds
    interference ignoring interference due to lack of supply _and_ due
    to self-interference. *)
Section TaskIntraInterferenceBound.

  (** Consider any type of job associated with any type of tasks ... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs. *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk : Task.

  (** Assume we are provided with abstract functions characterizing
      interference and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Next, we introduce the notions of "task intra-supply
      interference" and "task intra-supply IBF". Using these notions,
      one can separate the interference due to the lack of supply or
      due to self-interference from all the other sources of
      interference. *)

  (** Let us define a predicate stating that (1) there is supply at
      time [t] and (2) the task of a job [j] is _not_ scheduled at a
      time instant [t]. *)
  Definition nonself_intra (j : Job) (t : instant) :=
    (nonself arr_seq sched j t) && has_supply sched t.

  (** We define _task intra-supply interference_ as interference
      conditioned on the fact that there is supply and there is no
      self-interference. *)
  Definition task_intra_interference (j : Job) (t : instant) :=
    cond_interference nonself_intra j t.

  (** Consider an interference bound function [task_intra_IBF]. *)
  Variable task_intra_IBF : duration -> duration -> work.

  (** We say that task intra-supply interference is bounded by
      [task_intra_IBF] iff, for any job [j] of task [tsk], the
      cumulative task intra-supply interference within the interval
      <<[t1, t1 + R)>> is bounded by [task_intra_IBF(A, R)]. *)
  Definition task_intra_interference_is_bounded_by :=
    cond_interference_is_bounded_by
      arr_seq sched tsk task_intra_IBF
      (relative_arrival_time_of_job_is_A sched) nonself_intra.

End TaskIntraInterferenceBound.
