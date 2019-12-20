Require Export prosa.model.task.preemption.parameters.

(** Furthermore, we assume the fully preemptive job model. *)
Require Import prosa.model.preemption.fully_preemptive.

(** * Preemptions in Fully Preemptive Model *)
(** In this section, we prove that instantiation of predicate
    [job_preemptable] to the fully preemptive model indeed defines
    a valid preemption model. *)
Section FullyPreemptiveModel.

  (**  Consider any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched : schedule PState.

  (** Then, we prove that fully_preemptive_model is a valid preemption model. *)
  Lemma valid_fully_preemptive_model:
    valid_preemption_model arr_seq sched.
  Proof.
      by intros j ARR; repeat split; intros t CONTR.
  Qed.

  (** We also prove that under the fully preemptive model
      [job_max_nonpreemptive_segment j] is equal to 0, when [job_cost
      j = 0] ... *)
  Lemma job_max_nps_is_0:
    forall j,
      job_cost j = 0 -> 
      job_max_nonpreemptive_segment j = 0.
  Proof.
    intros.
    rewrite /job_max_nonpreemptive_segment /lengths_of_segments
            /job_preemption_points. 
      by rewrite H2; compute.
  Qed.

  (** ... or ε when [job_cost j > 0]. *)  
  Lemma job_max_nps_is_ε:
    forall j,
      job_cost j > 0 -> 
      job_max_nonpreemptive_segment j = ε.
  Proof.
    intros ? POS.
    rewrite /job_max_nonpreemptive_segment /lengths_of_segments
            /job_preemption_points.
    rewrite /job_preemptable /fully_preemptive_model.
    rewrite filter_predT.
    apply max0_of_uniform_set.
    - rewrite /range /index_iota subn0.
      rewrite [size _]pred_Sn -[in X in _ <= X]addn1 -size_of_seq_of_distances size_iota.
      + by rewrite -pred_Sn.
      + by rewrite ltnS.
    - by apply distances_of_iota_ε.
  Qed.    
  
End FullyPreemptiveModel.
Hint Resolve valid_fully_preemptive_model : basic_facts. 