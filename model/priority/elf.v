Require Export prosa.util.int.
Require Export prosa.model.priority.classes.
Require Export prosa.model.priority.gel.

(** * ELF Priority Policy  *)

(** We define the class of "EDF-Like-within-Fixed-priority (ELF)" scheduling
    policies. ELF scheduling is a (large) subset of the class of JLFP scheduling
    policies that can be structurally viewed as a combination of the fixed-priority
    and GEL scheduling policies. In ELF scheduling, we take an FP policy as an
    argument, and each task has a constant "priority-point offset". Each job's
    (absolute) "priority point" is given by its arrival time plus its task's
    priority-point offset.

    Given two jobs, their relative priority order is first determined by the fixed-
    priority policy, i.e., the priority order of their respective tasks. However,
    if their tasks have equal fixed priority, then it is determined by the jobs'
    priority points (GEL), with the interpretation that an earlier priority
    point implies higher priority. It can be viewed as an FP Policy with the GEL
    scheduling policy employed to resolve ties.

    The FP policy is a particular case of ELF if all the tasks are assigned distinct
    priorities. GEL (and hence, FIFO and EDF) are special cases of ELF if all tasks
    have equal priority according to the FP policy.  *)

(** In order to define the policy, we introduce the required context. *)
Section ELF.

  (** Consider any type of tasks with relative priority points...*)
  Context {Task : TaskType} `{PriorityPoint Task}.

  (** ...and jobs of these tasks. *)
  Context {Job : JobType} `{JobArrival Job} `{JobTask Job Task} .
  (** We parameterize the ELF priority policy based on a fixed-priority policy.
      Job [j1] is assigned a higher priority than job [j2] if either the task
      associated with [j1] has a strictly higher priority than the task
      associated with [j2], or if their tasks have equal priorities and the
      relative priority point of [j1] is less than or equal to the relative
      priority point of [j2], similar to the GEL policy.

      NB: The <<| 0>> at the end of the next line is a priority hint for
          type-class resolution, meaning this type class should be picked with
          highest priority in ambiguous contexts. *)
  #[export] Instance ELF (fp : FP_policy Task) : JLFP_policy Job | 0:=
  {
      hep_job (j1 j2 : Job) :=
        (** Recall the notion of a higher-priority job under the GEL policy as
            [gel_hep_job]. *)
        let gel_hep_job := @hep_job _ (GEL Job Task) in
        (** Under the ELF policy, job [j1] has higher-or-equal priority than job
            [j2] if (1) [j1]'s task has higher priority than [j2]'s task... *)
          hp_task (job_task j1) (job_task j2)
              (** ...or (2) if the two tasks have the same priority and [j1] has
                  higher priority than [j2] according to the GEL policy. *)
            || (hep_task (job_task j1) (job_task j2)
               && gel_hep_job j1 j2)
  }.

End ELF.
