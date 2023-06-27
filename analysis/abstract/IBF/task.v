Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.abstract.abstract_rta.

(** In this section, we define a notion of _task_ interference-bound
    function [task_IBF]. Function [task_IBF] bounds interference that
    excludes interference due to self-interference. *)
Section TaskInterferenceBound.

  (** Consider any type of job associated with any type of tasks... *)
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

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Next we introduce the notion of _task_ interference.
      Intuitively, task [tsk] incurs interference when some of the
      jobs of task [tsk] incur interference. As a result, [tsk] cannot
      make any progress.

      More formally, consider a job [j] of task [tsk]. The task
      experiences interference at time [t] if job [j] experiences
      interference ([interference j t = true]) and task [tsk] is not
      scheduled at time [t]. *)

  (** Let us define a predicate stating that the task of a job [j] is
      _not_ scheduled at a time instant [t]. *)
  Definition non_self (j : Job) (t : instant) :=
    ~~ task_scheduled_at arr_seq sched (job_task j) t.

  (** We define task interference as conditional interference where
      [non_self] is used as the predicate. This way,
      [task_interference j t] is [false] if the interference to a job
      [j] is caused by a job of the same task. *)
  Definition task_interference (j : Job) (t : instant) :=
    cond_interference non_self j t.

  (** Next, we define the cumulative task interference. *)
  Definition cumul_task_interference j t1 t2 :=
    cumul_cond_interference non_self j t1 t2.

  (** Consider an interference bound function [task_IBF]. *)
  Variable task_IBF : Task -> duration -> duration -> work.

  (** We say that task interference is bounded by [task_IBF] iff for
      any job [j] of task [tsk] cumulative _task_ interference within
      the interval <<[t1, t1 + R)>> is bounded by function [task_IBF(tsk, A, R)]. *)
  Definition task_interference_is_bounded_by :=
    cond_interference_is_bounded_by
      arr_seq sched tsk task_IBF (relative_arrival_time_of_job_is_A sched) non_self.

End TaskInterferenceBound.
