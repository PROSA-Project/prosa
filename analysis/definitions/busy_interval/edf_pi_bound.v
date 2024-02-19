Require Export prosa.model.task.preemption.parameters.
Require Export prosa.analysis.definitions.sbf.sbf.
Require Export prosa.analysis.definitions.request_bound_function.

(** * Bound for a Busy-Interval Starting with Priority Inversion under EDF Scheduling *)

(** In this file, we define a bound on the length of a busy interval
    that starts with priority inversion (w.r.t. a job of a given task
    under analysis) under the EDF scheduling policy. *)
Section BoundedBusyIntervalUnderEDF.

  (** Consider any type of tasks. *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{TaskDeadline Task}.
  Context `{TaskMaxNonpreemptiveSegment Task}.

  (** Consider an arrival curve [max_arrivals]. *)
  Context `{MaxArrivals Task}.

  (** For brevity, let's denote the relative deadline of a task as [D]. *)
  Let D tsk := task_deadline tsk.

  (** Consider an arbitrary task set [ts] ... *)
  Variable ts : seq Task.

  (** ... and let [tsk] be any task to be analyzed. *)
  Variable tsk : Task.

  (** Assume that there is a job [j] of task [tsk] and that job [j]'s
      busy interval starts with priority inversion. Then, the busy
      interval can be bounded by a constant
      [longest_busy_interval_with_pi]. *)

  (** Intuitively, such a bound holds because of the following two
      observations. (1) The presence of priority inversion implies an
      upper bound on the job arrival offset [A < D tsk_o - D tsk],
      where [A] is the time elapsed between the arrival of [j] and the
      beginning of the corresponding busy interval. (2) An upper bound
      on the offset implies an upper bound on the
      higher-or-equal-priority workload of each task. *)
  Definition longest_busy_interval_with_pi :=

    (** Let [lp_interference tsk_lp] denote the maximum service
        inversion caused by task [tsk_lp]. *)
    let lp_interference tsk_lp :=
      task_max_nonpreemptive_segment tsk_lp - ε in

    (** Let [hep_interference tsk_lp] denote the maximum higher-or-equal
        priority workload released within [D tsk_lp]. *)
    let hep_interference tsk_lp :=
      \sum_(tsk_hp <- ts | D tsk_hp <= D tsk_lp)
       task_request_bound_function tsk_hp (D tsk_lp - D tsk_hp) in

    (** Then, the amount of interfering workload incurred by a job of
        task [tsk] is bounded by maximum of [lp_interference tsk_lp +
        hep_interference tsk_lp], where [tsk_lp] is such that [D
        tsk_lp > D tsk]. *)
    \max_(tsk_lp <- ts | D tsk_lp > D tsk)
     (lp_interference tsk_lp + hep_interference tsk_lp).

End BoundedBusyIntervalUnderEDF.
