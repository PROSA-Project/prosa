From rt.util Require Import epsilon sum tactics search_arg.
From rt.restructuring.behavior Require Export all.
From rt.restructuring.analysis.basic_facts Require Import completion.
From rt.restructuring.model Require Import job task.
From rt.restructuring.model.preemption Require Import preemption_model task.parameters.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** * Run-to-completion threshold *) 
(** In this file, we provide definition and properties 
   of run-to-completion-threshold-compilant schedules. *)
Section RunToCompletionThreshold.
 
  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** In addition, we assume existence of a function
     maping jobs to theirs preemption points ... *)
  Context `{JobPreemptable Job}.

  (** ...and a function mapping tasks to theirs
     run-to-completion threshold. *)
  Context `{TaskRunToCompletionThreshold Task}.

  (** Consider any kind of processor state model, ... *)
  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** ... any job arrival sequence, ... *)
  Variable arr_seq: arrival_sequence Job.

  (** ... and any given schedule. *)
  Variable sched: schedule PState. 

  (** In this section we define the notion of a run-to-completion threshold for a job. *)
  Section JobRunToCompletionThreshold.
    
    (** We define the notion of job's run-to-completion threshold: run-to-completion threshold 
       is the amount of service after which a job cannot be preempted until its completion. *)
    Definition runs_to_completion_from (j : Job) (ρ : duration) :=
      all (fun (δ : duration) => ~~ job_preemptable j δ) (index_iota ρ (job_cost j)).

    (** Note that a run-to-completion threshold exists for any job. *)
    Lemma eventually_runs_to_completion:
      forall (j : Job), exists (ρ : duration), runs_to_completion_from j ρ.
    Proof.
      intros; exists (job_cost j).
      apply/allP.
      intros t; rewrite mem_index_iota; move => /andP [GE LT]; exfalso.
        by move: GE; rewrite leqNgt; move => /negP GE; apply: GE.
    Qed.    

    (** We define run-to-completion threshold of a job as the minimal progress 
       the job should reach to become non-preemptive until completion. *)
    Definition job_run_to_completion_threshold (j : Job) : duration :=
      ex_minn (eventually_runs_to_completion j).

    (** In this section we prove a few simple lemmas
       about run-to-completion threshold for a job. *)
    Section Lemmas.

      (** Assume that the preemption model is valid. *)
      Hypothesis H_valid_preemption_model:
        valid_preemption_model arr_seq sched.

      (** Consider an arbitrary job j from the arrival sequence. *)
      Variable j : Job.
      Hypothesis H_j_in_arrival_seq : arrives_in arr_seq j.

      (** First, we prove that a job cannot be preempted 
         during execution of the last segment. *)
      Lemma job_cannot_be_preempted_within_last_segment:
        forall (ρ : duration), 
          job_run_to_completion_threshold j <= ρ < job_cost j ->
          ~~ job_preemptable j ρ.
      Proof.
        move => ρ /andP [GE LT].
        pattern (job_run_to_completion_threshold j) in GE; apply prop_on_ex_minn in GE.
        move: GE => [n [LE [RUNS MIN]]].
        move: RUNS => /allP RUNS.
          by apply RUNS; rewrite mem_index_iota; apply/andP; split.
      Qed.
      
      (** We prove that the run-to-completion threshold is positive for any job. I.e., in order
         to become non-preemptive a job must receive at least one unit of service. *)
      Lemma job_run_to_completion_threshold_positive:
        job_cost_positive j ->
        0 < job_run_to_completion_threshold j.
      Proof.
        intros COST.
        rewrite lt0n; apply/neqP; intros F.
        pattern (job_run_to_completion_threshold j) in F;
          apply prop_on_ex_minn in F; move: F => [n [EQ [RUNS _]]]; subst n.
        move: RUNS => /allP F; specialize (F 0); feed F.
        { rewrite mem_iota; apply/andP; split; auto.
          rewrite subn0 add0n //. }
        move: F => /negP F; apply: F.
          by apply H_valid_preemption_model.
      Qed.

      (** Next we show that the run-to-completion threshold
         is at most the cost of a job. *)
      Lemma job_run_to_completion_threshold_le_job_cost:
        job_cost_positive j -> 
        job_run_to_completion_threshold j <= job_cost j.
      Proof.
        intros COST.
        apply ex_minn_le_ex.
        apply/allP.
        intros t; rewrite mem_index_iota; move => /andP [GE LT]; exfalso.
          by move: GE; rewrite leqNgt; move => /negP GE; apply: GE.
      Qed.
      
      (** In order to get a consistent schedule, the scheduler should respect 
         the notion of run-to-completion threshold. We assume that, after 
         a job reaches its run-to-completion threshold, it cannot be preempted
         until its completion. *)
      Lemma job_nonpreemptive_after_run_to_completion_threshold: 
        forall t t',
          t <= t' ->
          job_run_to_completion_threshold j <= service sched j t ->
          ~~ completed_by sched j t' ->
          scheduled_at sched j t'.
      Proof.
        intros ? ? LE TH COM.
        apply H_valid_preemption_model; first by done.
        apply job_cannot_be_preempted_within_last_segment; apply/andP; split.
        - by apply leq_trans with (service sched j t); last apply service_monotonic.
        - by rewrite ltnNge.
      Qed.

    End Lemmas.

  End JobRunToCompletionThreshold.

  (** Since a task model may not provide exact information about preemption point of 
     a task run-to-completion, task's run-to-completion threshold cannot be defined in
     terms of preemption points of a task (unlike job's run-to-completion threshold).   
     Therefore, one can assume the existence of a function that maps a task to 
     its run-to-completion threshold. In this section we define the notion 
     of a valid run-to-completion threshold of a task. *)
  Section ValidTaskRunToCompletionThreshold.
        
    (** A task's run-to-completion threshold should be at most the cost of the task. *)
    Definition task_run_to_completion_threshold_le_task_cost tsk :=
      task_run_to_completion_threshold tsk <= task_cost tsk.
    
    (** We say that the run-to-completion threshold of a task tsk
       bounds the job run-to-completionthreshold iff for any job j
       of task tsk the job run-to-completion threshold is less than 
       or equal to the task run-to-completion threshold. *) 
    Definition task_run_to_completion_threshold_bounds_job_run_to_completion_threshold tsk :=
      forall j,
        arrives_in arr_seq j ->
        job_task j = tsk ->
        job_run_to_completion_threshold j <= task_run_to_completion_threshold tsk.

    (** We say that task_run_to_completion_threshold is a valid task run-to-completion 
       threshold for a task tsk iff [task_run_to_completion_threshold tsk] is (1) no 
       bigger than tsk's cost, (2) for any job of task tsk job_run_to_completion_threshold
       is bounded by task_run_to_completion_threshold. *)
    Definition valid_task_run_to_completion_threshold tsk :=
      task_run_to_completion_threshold_le_task_cost tsk /\
      task_run_to_completion_threshold_bounds_job_run_to_completion_threshold tsk.

  End ValidTaskRunToCompletionThreshold. 

End RunToCompletionThreshold.