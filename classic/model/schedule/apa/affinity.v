Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.arrival.basic.arrival_sequence.
Require Import rt.model.schedule.global.basic.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Definition and properties about processor affinities. *)
Module Affinity.

  Import ArrivalSequence ScheduleOfSporadicTask.
  
  Section AffinityDefs.

    Variable sporadic_task: eqType.

    (* Given the number of processors, ... *)
    Variable num_cpus: nat.
      
    (* ... let a processor affinity be a subset of these processors.
       Note: notation {set T} is just a list of type T with no duplicates. *)
    Definition affinity := {set (processor num_cpus)}.

    (* Next, we define a task affinity as the mapping from tasks to affinities. *)
    Definition task_affinity := sporadic_task -> affinity.
    
  End AffinityDefs.

  Section Properties.

    Context {sporadic_task: eqType}.    
    Context {num_cpus: nat}.

    Section JobProperties.

      (* Assume that each task has a processor affinity alpha. *)
      Variable alpha: task_affinity sporadic_task num_cpus.

      (* Then, we say that task tsk ...*)
      Variable tsk: sporadic_task.

      (* ... can execute on processor cpu ...*)
      Variable cpu: processor num_cpus.

      (* ... iff cpu is part of j's affinity. *)
      Definition can_execute_on := cpu \in alpha tsk.

    End JobProperties.

    Section ScheduleProperties.

      Context {Job: eqType}.
      Variable job_task: Job -> sporadic_task.
      
      (* Consider any schedule, ... *)
      Variable sched: schedule Job num_cpus.

      (* ... and some affinity alpha. *)
      Variable alpha: affinity num_cpus.
      
      (* We say that a task is executing on alpha at time t iff it is
         scheduled on some processor in that affinity. *)
      Definition task_scheduled_on_affinity (tsk: sporadic_task) (t: time) :=
        [exists cpu, (cpu \in alpha) && task_scheduled_on job_task sched tsk cpu t].

    End ScheduleProperties.

    Section Subset.

      (* Given two affinities alpha' and alpha, ...*)
      Variable alpha' alpha: affinity num_cpus.

      (* ... we say that alpha' is subaffinity of alpha iff
         alpha' is contained in alpha. *)
      Definition is_subaffinity := {subset alpha' <= alpha}.

      Section Lemmas.

        Hypothesis H_subaffinity: is_subaffinity.

        Lemma leq_subaffinity : #|alpha'| <= #|alpha|.
        Proof.
          assert (UNIQ: uniq (alpha)). by destruct (alpha).
          assert (UNIQ': uniq (alpha')). by destruct (alpha').
          move: (UNIQ) (UNIQ') => /card_uniqP -> /card_uniqP ->.
          by apply uniq_leq_size.
        Qed.  

      End Lemmas.
      
    End Subset.

    Section IntersectingAffinities.

      (* We say that alpha and alpha' intersect iff there exists a processor
         that belongs to both affinities. *)
      Definition affinity_intersects (alpha alpha': affinity num_cpus) :=
        [exists cpu, (cpu \in alpha) && (cpu \in alpha')].

    End IntersectingAffinities.
  
  End Properties.
  
End Affinity.