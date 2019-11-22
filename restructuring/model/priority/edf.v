Require Export rt.restructuring.model.job_deadline.
Require Import rt.restructuring.model.priority.classes.
From mathcomp Require Export seq.

(** In this section we introduce the notion of EDF priorities. *)
Program Instance EDF (Task : TaskType) (Job : JobType)
        `{TaskDeadline Task} `{JobArrival Job} `{JobTask Job Task} : JLFP_policy Job :=
  { 
    hep_job (j1 j2 : Job) := job_deadline j1 <= job_deadline j2
  }.

(** In this section, we prove a few properties about EDF policy. *)
Section PropertiesOfEDF.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskDeadline Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  
  (** EDF is reflexive. *)
  Lemma EDF_is_reflexive : reflexive_priorities.
  Proof. by intros t j; unfold hep_job_at, JLFP_to_JLDP, hep_job, EDF. Qed.

  (** EDF is transitive. *)
  Lemma EDF_is_transitive : transitive_priorities.
  Proof. by intros t y x z; apply leq_trans. Qed.
  
  (** EDF respects sequential tasks hypothesis. *)
  Lemma EDF_respects_sequential_tasks:
    policy_respects_sequential_tasks.
  Proof.
    intros j1 j2 TSK ARR.
    move: TSK => /eqP TSK.
    unfold hep_job, EDF, job_deadline, job_deadline_from_task_deadline; rewrite TSK.
      by rewrite leq_add2r.
  Qed.

End PropertiesOfEDF.

(** We add the above lemmas into a "Hint Database" basic_facts, so Coq 
    will be able to apply them automatically. *)
Hint Resolve
     EDF_is_reflexive
     EDF_is_transitive
     EDF_respects_sequential_tasks : basic_facts.
