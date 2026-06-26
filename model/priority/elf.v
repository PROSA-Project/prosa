Require Export prosa.util.int.
Require Export prosa.model.priority.gel.

(** * ELF Priority Policy  *)

(** We define the class of "EDF-Like-within-Fixed-priority (ELF)" scheduling
    policies. ELF scheduling is a (large) subset of the class of JLFP scheduling
    policies that can be structurally viewed as a combination of fixed-priority
    and GEL scheduling policies. In ELF scheduling, we take an FP policy as an
    argument, and each task has a constant "priority-point offset." Each job's
    absolute priority point is given by its arrival time plus its task's
    priority-point offset.

    Given two jobs, their relative priority order is first determined by the
    fixed-priority policy, i.e., the priority order of their respective tasks.
    If their tasks have equal fixed priority, then it is determined by the
    jobs' priority points, with the interpretation that an earlier priority
    point implies higher priority. *)

(** We define what it means for an abstract job-level fixed-priority policy to
    behave as an ELF policy. *)
Section ELFPolicy.

  (** Consider any type of tasks with relative priority points ... *)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ... and jobs of these tasks. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task}.

  (** Given an underlying FP policy, a JLFP policy is ELF if it gives a job
      priority whenever its task has strictly higher priority, or whenever the
      tasks have equal priority and the job has an earlier absolute priority
      point. *)
  Definition policy_is_ELF (FP : FP_policy Task) (JLFP : JLFP_policy Job) :=
    forall j1 j2,
      hep_job j1 j2
      = (hp_task (job_task j1) (job_task j2)
         || (hep_task (job_task j1) (job_task j2)
             && (job_priority_point j1 <= job_priority_point j2)%R)).

End ELFPolicy.
