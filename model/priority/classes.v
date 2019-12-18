Require Export prosa.model.task.concept.
Require Export prosa.util.rel.
Require Export prosa.util.list.

From mathcomp Require Export seq.

(** * The FP, JLFP, and JLDP Priority Classes *)

(** In this module, we define the three well-known classes of priority
    relations: (1) fixed-priority (FP) policies, (2) job-level fixed-priority
    (JLFP) polices, and (3) job-level dynamic-priority (JLDP) policies, where
    (2) is a subset of (3), and (1) a subset of (2). *)

(** As a convention, we use "hep" to mean "higher or equal priority." *)

(** We define an FP policy as a relation among tasks, ... *)
Class FP_policy (Task: TaskType) := hep_task : rel Task.

(** ... a JLFP policy as a relation among jobs, and ... *)
Class JLFP_policy (Job: JobType) := hep_job : rel Job.

(** ... a JLDP policy as a relation among jobs that may vary over time. *)
Class JLDP_policy (Job: JobType) := hep_job_at : instant -> rel Job.

(** NB: The preceding definitions currently make it difficult to express
        priority policies in which the priority of a job at a given time varies
        depending on the preceding schedule prefix (e.g., least-laxity
        first). That is, there is room for an even more general notion of a
        schedule-dependent JLDP policy, where the priority relation among jobs
        may vary depending both on time and the schedule prefix prior to a
        given time. This is left to future work.  *)

(** ** Automatic FP ➔ JLFP ➔ JLDP Conversion *)

(** Since there are natural interpretations of FP and JLFP policies as JLFP and
    JLDP policies, respectively, we define conversions that express these
    generalizations. In practice, this means that Coq will be able to
    automatically satisfy a JLDP assumption if a JLFP or FP policy is in
    scope. *)

(** First, any FP policy can be interpreted as an JLFP policy by comparing jobs
    according to the priorities of their respective tasks. *)
Instance FP_to_JLFP (Job: JobType) (Task: TaskType)
         `{JobTask Job Task} `{FP_policy Task} : JLFP_policy Job :=
  fun j1 j2 => hep_task (job_task j1) (job_task j2).

(** Second, any JLFP policy implies a JLDP policy that simply ignores the time
    parameter. *)
Instance JLFP_to_JLDP (Job: JobType) `{JLFP_policy Job} : JLDP_policy Job :=
  fun _ j1 j2 => hep_job j1 j2.

(** ** Properties of Priority Policies *)

(** In the following section, we define key properties of common priority
    policies that proofs often depend on. *)

Section Priorities.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks, ... *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.

  (** .. and assume that jobs have a cost and an arrival time. *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In the following section, we define properties of JLDP policies, and by
      extension also properties of FP and JLFP policies. *)
  Section JLDP.

    (** Consider any JLDP policy. *)
    Context `{JLDP_policy Job}.

    (** We define what it means for a JLDP policy to be reflexive, transitive,
        and total. Note that these definitions, although phrased in terms of a
        given JLDP policy, can also be used for JLFP and FP policies due to the
        above-defined conversion instances. *)

    (** A JLDP policy is reflexive if the relation among jobs is reflexive at
        every point in time. *)
    Definition reflexive_priorities := forall t, reflexive (hep_job_at t).

     (** A JLDP policy is transitive if the relation among jobs is transitive at
        every point in time. *)
    Definition transitive_priorities := forall t, transitive (hep_job_at t).

    (** A JLDP policy is total if the relation among jobs is total at
        every point in time. *)
    Definition total_priorities := forall t, total (hep_job_at t).

  End JLDP.

  (** Next, we define a property of JLFP policies. *)
  Section JLFP.

    (** Consider any JLFP policy. *)
    Context `{JLFP_policy Job}.

    (** Recall that jobs of a sequential task are necessarily executed in the
        order that they arrive.

        An arbitrary JLFP policy, however, can violate the sequential tasks
        hypothesis.  For example, consider two jobs [j1], [j2] of the same task
        such that [job_arrival j1 < job_arrival j2]. It is possible that a JLFP
        priority policy [π] will assign a higher priority to the second job [π
        j2 j1 = true]. But such a situation would contradict the natural
        execution order of sequential tasks. It is therefore sometimes
        necessary to restrict the space of JLFP policies to those that assign
        priorities in a way that is consistent with sequential tasks.

        To this end, we say that a policy respects sequential tasks if, for any
        two jobs [j1], [j2] of the same task, [job_arrival j1 <= job_arrival j2]
        implies [π j1 j2 = true]. *)
    Definition policy_respects_sequential_tasks :=
      forall j1 j2,
        job_task j1 == job_task j2 ->
        job_arrival j1 <= job_arrival j2 ->
        hep_job j1 j2.

  End JLFP.

  (** Finally, we we define and observe two properties of FP policies. *)
  Section FP.

    (** Consider any FP policy. *)
    Context `{FP_policy Task}.

    (** To express the common assumption that task priorities are unique, we
        define whether the given FP policy is antisymmetric over a task set
        [ts]. *)
    Definition antisymmetric_over_taskset (ts : seq Task) :=
      antisymmetric_over_list hep_task ts.

    (** Further, we observe that any [FP_policy] respects the sequential tasks
        hypothesis, meaning that later-arrived jobs of a task don't have higher
        priority than earlier-arrived jobs of the same task (assuming that task
        priorities are reflexive). *)
    Remark respects_sequential_tasks :
      reflexive_priorities -> policy_respects_sequential_tasks.
    Proof.
      move => REFL j1 j2 /eqP EQ LT.
      rewrite /hep_job /FP_to_JLFP EQ.
        by eapply (REFL 0).
    Qed.

  End FP.

End Priorities.

(** We add the above observation into the "Hint Database" basic_facts, so Coq
    will be able to apply it automatically. *)
Hint Resolve respects_sequential_tasks : basic_facts.
