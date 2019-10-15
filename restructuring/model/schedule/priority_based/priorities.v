From rt.restructuring.model Require Export task.
From rt.util Require Export list.
From mathcomp Require Export seq.

(** Definitions of FP, JLFP and JLDP priority relations. *)

(** In the following, "hep" means "higher or equal priority". We define an FP
   policy as a relation among tasks, ... *)
Class FP_policy (Task: TaskType) := hep_task : rel Task.

(** ... a JLFP policy as a relation among jobs, a ... *)
Class JLFP_policy (Job: JobType) := hep_job : rel Job.

(** ... a JLDP policy as a relation among jobs that may vary over time. *)
Class JLDP_policy (Job: JobType) := hep_job_at : instant -> rel Job.

(** Since FP policies are also JLFP and JLDP policies, we define
   conversions that express the generalization. *)
Instance FP_to_JLFP (Job: JobType) (Task: TaskType)
         `{JobTask Job Task} `{FP_policy Task} : JLFP_policy Job :=
  fun j1 j2 => hep_task (job_task j1) (job_task j2).

Instance JLFP_to_JLDP (Job: JobType) `{JLFP_policy Job} : JLDP_policy Job :=
  fun _ j1 j2 => hep_job j1 j2.

Section Priorities.
  Context {Job: eqType}.

  Section JLDP.
    (** Consider any JLDP policy. *)
    Context `{JLDP_policy Job}.

    (** We define common properties of the policy. Note that these definitions
       can also be used for JLFP and FP policies *)
    Definition reflexive_priorities := forall t, reflexive (hep_job_at t).

    Definition transitive_priorities := forall t, transitive (hep_job_at t).

    Definition total_priorities := forall t, total (hep_job_at t).

  End JLDP.

  Section FP.
    (** Consider any FP policy. *)
    Context {Task : TaskType}.
    Context `{FP_policy Task}.

    (** We define whether the policy is antisymmetric over a taskset ts. *)
    Definition antisymmetric_over_taskset (ts : seq Task) :=
      antisymmetric_over_list hep_task ts.
  End FP.
End Priorities.

