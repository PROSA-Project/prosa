From rt.restructuring.model Require Export task.
From rt.util Require Export rel list.

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

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In this section we define properties of JLDP policy. *)
  Section JLDP.

    (** Consider any JLDP policy. *)
    Context `{JLDP_policy Job}.

    (** We define common properties of the policy. Note that these definitions
       can also be used for JLFP and FP policies *)
    Definition reflexive_priorities := forall t, reflexive (hep_job_at t).

    Definition transitive_priorities := forall t, transitive (hep_job_at t).

    Definition total_priorities := forall t, total (hep_job_at t).

  End JLDP.

  (** In this section we define properties of JLFP policy. *)
  Section JLFP.
    
    (** Consider any JLFP policy. *)
    Context `{JLFP_policy Job}.

    (** Recall that a task is sequential if its jobs are executed in
        the order that they arrive.
       
       An arbitrary JLFP can violate the sequential tasks hypothesis.
       For example, consider two jobs j1, j2 of the same task such
       that [job_arrival j1 < job_arrival j2]. It is possible that the
       policy will assign a higher priority to the second job [i.e.,
       π(j1) < π(j2)].  But this situation contradicts the sequential
       tasks hypothesis.

       We say that a policy respects sequential tasks if for any two
       jobs j1, j2 from the same task the fact that [job_arrival j1 <=
       job_arrival j2] implies [π(j1) >= π(j2)]. *)
    Definition policy_respects_sequential_tasks :=
      forall j1 j2,
        job_task j1 == job_task j2 ->
        job_arrival j1 <= job_arrival j2 ->
        hep_job j1 j2.
    
  End JLFP.

  (** In this section we define properties of FP policy. *)
  Section FP.
    
    (** Consider any FP policy. *)
    Context `{FP_policy Task}.

    (** We define whether the policy is antisymmetric over a taskset ts. *)
    Definition antisymmetric_over_taskset (ts : seq Task) :=
      antisymmetric_over_list hep_task ts.    
    
    (** Note that any FP_policy respects sequential tasks hypothesis,
        meaning that later-arrived jobs of a task don't have higher
        priority than earlier-arrived jobs of the same task. *)
    Remark respects_sequential_tasks :
      reflexive_priorities -> 
      policy_respects_sequential_tasks. 
    Proof.
      move => REFL j1 j2 /eqP EQ LT.
      rewrite /hep_job /FP_to_JLFP EQ.
        by eapply (REFL 0).
    Qed.

  End FP.
  
End Priorities.

(** We add the above lemma into a "Hint Database" basic_facts, so Coq 
    will be able to apply them automatically. *)
Hint Resolve respects_sequential_tasks : basic_facts.