Require Export prosa.model.priority.classes.
Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.definitions.service.
Require Export prosa.analysis.definitions.service_inversion.pred.
Require Export prosa.analysis.abstract.definitions.

(** * Service Inversion Bounded *)
(** In this section, we define the notion of bounded cumulative
    service inversion in an abstract busy interval prefix. *)
Section ServiceInversion.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Next, consider _any_ kind of processor state model, ... *)
  Context {PState : ProcessorState Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** Assume a given JLFP policy. *)
  Context `{JLFP_policy Job}.

  (** If the priority inversion experienced by job [j] depends on its
      relative arrival time w.r.t. the beginning of its busy interval
      at a time [t1], we say that the service inversion of job [j] is
      bounded by a function [B : duration -> duration] if the
      cumulative service inversion within any (abstract) busy interval
      prefix is bounded by [B (job_arrival j - t1)]. *)
  Definition service_inversion_of_job_is_bounded_by (j : Job) (B : duration -> duration) :=
    pred_service_inversion_of_job_is_bounded_by
      arr_seq sched (busy_interval_prefix sched) j B.

  (** We say that task [tsk] has bounded service inversion if all its
      jobs have cumulative service inversion bounded by function [B :
      duration -> duration], where [B] may depend on jobs' relative
      arrival times w.r.t. the beginning of an abstract busy interval
      prefix. *)
  Definition service_inversion_is_bounded_by (tsk : Task) (B : duration -> duration) :=
    pred_service_inversion_is_bounded_by
      arr_seq sched (busy_interval_prefix sched) tsk B.

End ServiceInversion.
