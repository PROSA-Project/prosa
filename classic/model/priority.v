Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

(* Definitions of FP, JLFP and JLDP priority relations. *)
Module Priority.

  Import SporadicTaskset ArrivalSequence.

  Section PriorityDefs.

    Variable Task: eqType.
    Variable Job: eqType.
    
    (* We define an FP policy as a relation between tasks, ... *)
    Definition FP_policy := rel Task.

    (* ...JLFP policy as a relation between jobs, ... *)
    Definition JLFP_policy := rel Job.

    (* ...and JLDP as any time-dependent relation between jobs. *)
    Definition JLDP_policy := time -> rel Job.

  End PriorityDefs.

  (* Since FP policies are also JLFP and JLDP policies, we define
     next conversion functions to do the generalization. *)
  Section Generalization.

    (* Consider any arrival sequence of jobs spawned by tasks. *)
    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> Task.

    (* We show how to convert FP to JLFP,... *)
    Definition FP_to_JLFP (task_hp: FP_policy Task) :=
      fun (jhigh jlow: Job) =>
        task_hp (job_task jhigh) (job_task jlow).
    
    (* ...FP to JLDP, ... *)
    Definition FP_to_JLDP (task_hp: FP_policy Task) :=
      fun (t: time) => FP_to_JLFP task_hp.

    (* ...and JLFP to JLDP. *)
    Definition JLFP_to_JLDP (job_hp: JLFP_policy Job) :=
      fun (t: time) => job_hp.
    
  End Generalization.

  (* Next we define properties of an FP policy. *)
  Section PropertiesFP.

    (* Assume that jobs are spawned by tasks. *)
    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> Task.

    (* Let task_priority be any FP policy. *)
    Variable task_priority: FP_policy Task.

    (* Now we define the properties. *)
    
    (* Whether the FP policy is reflexive. *)
    Definition FP_is_reflexive := reflexive task_priority.

    (* Whether the FP policy is irreflexive. *)
    Definition FP_is_irreflexive := irreflexive task_priority.

    (* Whether the FP policy is transitive. *)
    Definition FP_is_transitive := transitive task_priority.
    
    Section Antisymmetry.

      (* Consider any task set ts. *)
      Variable ts: seq Task.

      (* First we define whether task set ts is totally ordered with
         the priority. *)
      Definition FP_is_total_over_task_set :=
        total_over_list task_priority ts. 
      
      (* Then we define whether an FP policy is antisymmetric over task set ts, i.e.,
         whether the task set has unique priorities. *)
      Definition FP_is_antisymmetric_over_task_set :=
        antisymmetric_over_list task_priority ts. 
                  
    End Antisymmetry.

  End PropertiesFP. 
    
  (* Next, we define properties of a JLFP policy. *)
  Section PropertiesJLFP.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> Task.
    Variable job_arrival: Job -> time.

    (* Consider any arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
    
    (* Consider any JLFP policy. *)
    Variable job_priority: JLFP_policy Job.

    (* Now we define the properties. *)
    
    (* Whether the JLFP policy is reflexive. *)
    Definition JLFP_is_reflexive := reflexive job_priority.

    (* Whether the JLFP policy is irreflexive. *)
    Definition JLFP_is_irreflexive := irreflexive job_priority.

    (* Whether the JLFP policy is transitive. *)
    Definition JLFP_is_transitive := transitive job_priority.

    (* Whether the JLFP policy is total over the arrival sequence. *)
    Definition JLFP_is_total :=
      forall j1 j2,
        arrives_in arr_seq j1 ->
        arrives_in arr_seq j2 ->
        job_priority j1 j2 || job_priority j2 j1.

    (* Recall that the jobs are sequential if they are executed 
       in the order they arrived (for more details see file 
       prosa.classic.model.schedule.uni.schedule.v). 
       
       An arbitrary JLFP can violate the sequential jobs hypothesis. 
       For example, consider two jobs j1, j2 of the same task such that 
       [job_arrival j1 < job_arrival j2]. It is possible that the policy
       will assign a higher priority to the second job [i.e., π(j1) < π(j2)].
       But this situation contradicts to sequential job hypothesis.

       We say that JLFP respects sequential jobs if for any two jobs 
       j1, j2 from the same task the fact that [job_arrival j1 <= job_arrival j2]
       implies [π(j1) >= π(j2)]. *)
    Definition JLFP_respects_sequential_jobs :=
      forall j1 j2,
        job_task j1 == job_task j2 ->
        job_arrival j1 <= job_arrival j2 ->
        job_priority j1 j2.

  End PropertiesJLFP.

  (* Next, we define properties of a JLDP policy. *)
  Section PropertiesJLDP.

    (* Consider any JLDP policy. *)
    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.
    
    Variable job_priority: JLDP_policy Job.

    (* Now we define the properties. *)
    
    (* Whether the JLDP policy is reflexive. *)
    Definition JLDP_is_reflexive :=
      forall t, reflexive (job_priority t).

    (* Whether the JLDP policy is irreflexive. *)
    Definition JLDP_is_irreflexive :=
      forall t, irreflexive (job_priority t).

    (* Whether the JLDP policy is transitive. *)
    Definition JLDP_is_transitive :=
      forall t, transitive (job_priority t).

    (* Whether the JLDP policy is total. *)
    Definition JLDP_is_total :=
      forall j1 j2 t,
        arrives_in arr_seq j1 ->
        arrives_in arr_seq j2 ->
        job_priority t j1 j2 || job_priority t j2 j1.

  End PropertiesJLDP.

  (* Next we define some known FP policies. *)
  Section KnownFPPolicies.

    Context {Job: eqType}.
    Context {Task: eqType}.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Rate-monotonic orders tasks by smaller periods. *)
    Definition RM (tsk1 tsk2: Task) :=
      task_period tsk1 <= task_period tsk2.

    (* Deadline-monotonic orders tasks by smaller relative deadlines. *)
    Definition DM (tsk1 tsk2: Task) :=
      task_deadline tsk1 <= task_deadline tsk2.

    Section Properties.

      (* RM is reflexive. *)
      Lemma RM_is_reflexive : FP_is_reflexive RM.
      Proof.
        unfold FP_is_reflexive, reflexive, RM.
        by intros tsk; apply leqnn.
      Qed.

      (* RM is transitive. *)
      Lemma RM_is_transitive : FP_is_transitive RM.
      Proof.
        unfold FP_is_transitive, transitive, RM.
        by intros y x z; apply leq_trans.
      Qed.

      (* DM is reflexive. *)
      Lemma DM_is_reflexive : FP_is_reflexive DM.
      Proof.
        unfold FP_is_reflexive, reflexive, DM.
        by intros tsk; apply leqnn.
      Qed.

      (* DM is transitive. *)
      Lemma DM_is_transitive : FP_is_transitive DM.
      Proof.
        unfold FP_is_transitive, transitive, DM.
        by intros y x z; apply leq_trans.
      Qed.

      (* Any FP respects sequential jobs. *)
      Lemma any_reflexive_FP_respects_sequential_jobs:
        forall job_priority: FP_policy Task,
          FP_is_reflexive job_priority ->
          JLFP_respects_sequential_jobs
            job_task job_arrival (FP_to_JLFP job_task job_priority).
      Proof.
        intros HP REFL j1 j2 TSK ARR.
        move: TSK => /eqP TSK.
        unfold FP_to_JLFP; rewrite TSK.
          by apply REFL.
      Qed.

    End Properties.

  End KnownFPPolicies.

  (* In this section, we define known JLFP policies. *)
  Section KnownJLFPPolicies.

    (* EDF policy. *)
    Section EDF.
      
      Context {Job: eqType}.
      Variable job_arrival: Job -> time.
      Variable job_deadline: Job -> time.
      
      Variable arr_seq: arrival_sequence Job.

      (* We define earliest deadline first (EDF) as ordering jobs by absolute deadlines. *)
      Definition EDF (j1 j2: Job) :=
        job_arrival j1 + job_deadline j1 <= job_arrival j2 + job_deadline j2.

      Section Properties.
        
        (* EDF is reflexive. *)
        Lemma EDF_is_reflexive : JLFP_is_reflexive EDF.
        Proof.
            by intros j; apply leqnn.
        Qed.

        (* EDF is transitive. *)
        Lemma EDF_is_transitive : JLFP_is_transitive EDF.
        Proof.
            by intros y x z; apply leq_trans.
        Qed.

        (* EDF is total. *)
        Lemma EDF_is_total : JLFP_is_total arr_seq EDF.
        Proof.
          unfold EDF; intros x y ARRx ARRy.
          case (leqP (job_arrival x + job_deadline x)
                     (job_arrival y + job_deadline y));
            [by rewrite orTb | by move/ltnW => ->].
        Qed.

      End Properties.

    End EDF.

    (* EDF in the presence of tasks. *)
    Section EDFwithTasks.
      
      Context {Task: eqType}.
      Variable task_deadline: Task -> time.

      Context {Job: eqType}.
      Variable job_arrival: Job -> time.
      Variable job_task: Job -> Task.

      (* Notice that in the presence of tasks the relative dealine 
         of a job is equal to the relative deadline of its task. *)
      Definition job_relative_dealine (j: Job) := task_deadline (job_task j).

      (* EDF respects sequential jobs.*)
      Lemma EDF_respects_sequential_jobs:
        JLFP_respects_sequential_jobs
          job_task job_arrival (EDF job_arrival job_relative_dealine).
      Proof.
        intros j1 j2 TSK ARR.
        move: TSK => /eqP TSK.
        unfold EDF, job_relative_dealine; rewrite TSK.
          by rewrite leq_add2r.
      Qed.
      
    End EDFwithTasks.
    
  End KnownJLFPPolicies.

  (* In this section, we define the notion of a possible interfering task. *)
  Section PossibleInterferingTasks.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Section FP.

      (* Assume an FP policy. *)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* Let tsk be the task to be analyzed ... *)
      Variable tsk: sporadic_task.

      (* ...and let tsk_other be another task. *)
      Variable tsk_other: sporadic_task.

      (* Under FP scheduling with constrained deadlines, tsk_other can only interfere
         with tsk if it is a different task with higher priority. *)
      Definition higher_priority_task :=
        higher_eq_priority tsk_other tsk &&
        (tsk_other != tsk).

    End FP.

    Section JLFP.

      (* Let tsk be the task to be analyzed ... *)
      Variable tsk: sporadic_task.

      (* ...and let tsk_other be another task. *)
      Variable tsk_other: sporadic_task.

      (* Under JLFP/JLDP scheduling with constrained deadlines, tsk_other can only interfere
         with tsk if it is a different task. *)
      Definition different_task := tsk_other != tsk.

    End JLFP.
    
  End PossibleInterferingTasks.  

End Priority.