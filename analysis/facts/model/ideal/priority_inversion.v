Require Export prosa.analysis.facts.priority.inversion.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.
Require Export prosa.analysis.facts.model.ideal.schedule.

(** * Lemmas about Priority Inversion for ideal uni-processors *)
(** In this section, we prove a few useful properties about the notion
    of priority inversion for ideal uni-processors. *)
Section PIIdealProcessorModelLemmas.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** Next, consider any ideal uni-processor schedule of this arrival sequence ... *)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.

  (** ... where jobs do not execute before their arrival or after completion. *)
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Hypothesis H_completed_jobs_dont_execute : completed_jobs_dont_execute sched.

  (** Consider a JLFP-policy that indicates a higher-or-equal priority relation,
     and assume that this relation is reflexive. *)
  Context {JLFP : JLFP_policy Job}.
  Hypothesis H_priority_is_reflexive : reflexive_job_priorities JLFP.

  (** Let [tsk] be any task to be analyzed. *)
  Variable tsk : Task.

  (** Consider a job [j] of task [tsk]. In this subsection, job [j] is
      deemed to be the main job with respect to which the priority
      inversion is computed. *)
  Variable j : Job.
  Hypothesis H_j_tsk : job_of_task tsk j.

  (** Consider a time instant [t]. *)
  Variable t : instant.

  (** We prove that if the processor is idle at time [t], then there
      is no priority inversion. *)
  Lemma idle_implies_no_priority_inversion :
    ideal_is_idle sched t ->
    ~~ priority_inversion arr_seq sched j t.
  Proof.
    move=> IDLE.
    apply: no_priority_inversion_when_idle => //.
    by rewrite is_idle_def.
  Qed.

  (** Next, consider an additional job [j'] and assume it is scheduled
      at time [t]. *)
  Variable j' : Job.
  Hypothesis H_j'_sched : scheduled_at sched j' t.

  (** Then, we prove that from point of view of job [j], priority
      inversion appears iff [s] has lower priority than job [j]. *)
  Lemma priority_inversion_equiv_sched_lower_priority :
    priority_inversion arr_seq sched j t = ~~ hep_job j' j.
  Proof. exact: priority_inversion_hep_job. Qed.

  (** Assume that [j'] has higher-or-equal priority than job [j], then
      we prove that there is no priority inversion for job [j]. *)
  Lemma sched_hep_implies_no_priority_inversion :
    hep_job j' j ->
    priority_inversion arr_seq sched j t = false.
  Proof. by rewrite  priority_inversion_equiv_sched_lower_priority => ->. Qed.

  (** Assume that [j'] has lower priority than job [j], then
      we prove that [j] incurs priority inversion. *)
  Lemma sched_lp_implies_priority_inversion :
    ~~ hep_job j' j ->
    priority_inversion arr_seq sched j t.
  Proof. by move=> NHEP; apply/uni_priority_inversion_P. Qed.

End PIIdealProcessorModelLemmas.
