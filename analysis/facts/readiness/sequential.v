Require Export prosa.analysis.definitions.readiness.
Require Export prosa.analysis.definitions.work_bearing_readiness.
Require Export prosa.analysis.facts.behavior.completion.
Require Export prosa.analysis.facts.model.task_arrivals.

(** Throughout this file, we assume the sequential task readiness model, which
    means that a job is ready to execute only if all prior jobs of the same task
    have completed. *)
Require Export prosa.model.readiness.sequential.

(** In this section, we show some useful properties of the sequential
    task readiness model. *) 
Section SequentialTasksReadiness.

  (** Consider any type of job associated with any type of tasks ... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** ... and any kind of processor state. *)
  Context {PState : ProcessorState Job}.
  
  (** Consider any arrival sequence with consistent arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  
  (** Recall that we assume sequential tasks. *)
  #[local] Instance sequential_readiness : JobReady Job PState :=
    sequential_ready_instance arr_seq.
  
  (** Consider any valid schedule of [arr_seq]. *)
  Variable sched : schedule PState.
  Hypothesis H_valid_schedule : valid_schedule sched arr_seq.
  
  (** Consider an FP policy that indicates a reflexive 
      higher-or-equal priority relation. *) 
  Context {FP : FP_policy Task}.
  Hypothesis H_priority_is_reflexive : reflexive_priorities (FP_to_JLFP FP).

  (** First, we show that the sequential readiness model is non-clairvoyant. *) 
  Fact sequential_readiness_nonclairvoyance :
    nonclairvoyant_readiness sequential_readiness.
  Proof.
    intros sched1 sched2 ? ? ID ? LE; rewrite //=.
    erewrite identical_prefix_pending; eauto 2.
    destruct (boolP (pending sched2 j t)) as [_ | _] => //=.
    destruct (boolP (prior_jobs_complete arr_seq sched2 j t)) as [ALL | NOT_ALL]; apply/eqP.
    - rewrite eqb_id; apply/allP; intros ? IN.
      move: ALL => /allP ALL; specialize (ALL x IN).
      by erewrite identical_prefix_completed_by; eauto 2.
    - move: NOT_ALL => /allPn [x IN NCOMP].
      rewrite eqbF_neg; apply/allPn; exists x => //.
      by erewrite identical_prefix_completed_by; eauto 2.
  Qed.

  (** Next, we show that the sequential readiness model ensures that
      tasks are sequential. That is, that jobs of the same task
      execute in order of their arrival. *)
  Lemma sequential_readiness_implies_sequential_tasks :
    sequential_tasks arr_seq sched.
  Proof.
    intros j1 j2 t ARR1 ARR2 SAME LT SCHED.
    destruct (boolP (job_ready sched j2 t)) as [READY | NREADY].
    - move: READY => /andP [PEND /allP ALL]; apply: ALL.
      rewrite mem_filter; apply/andP; split; first by done.
      by apply arrived_between_implies_in_arrivals => //.
    - exfalso; apply/(negP NREADY)/job_scheduled_implies_ready => //.
      exact: (valid_schedule_jobs_must_be_ready_to_execute sched arr_seq).
  Qed.

  (** Finally, we show that the sequential readiness model is a
     work-bearing readiness model. That is, if a job [j] is pending
     but not ready at a time instant [t], then there exists another
     (earlier) job of the same task that is pending and ready at time
     [t]. *)
  Lemma sequential_readiness_implies_work_bearing_readiness :
    work_bearing_readiness arr_seq sched.
  Proof.
    intros j.
    have EX: exists k, job_arrival j <= k by (exists (job_arrival j)).
    destruct EX as [k LE]; move: j LE.
    induction k; intros ? ? ? ARR PEND.
    { destruct (boolP (job_ready sched j t)) as [READY | NREADY].
      { by exists j; repeat split; eauto using (H_priority_is_reflexive 0). }
      { move: NREADY; rewrite //= PEND Bool.andb_true_l => /allPn [jhp IN NCOMP].
        apply arrives_in_task_arrivals_before_implies_arrives_before in IN; last by done.
        by exfalso; move: LE; rewrite leqn0 => /eqP EQ; rewrite EQ in IN.
      }
    }
    { move: LE; rewrite leq_eqVlt ltnS => /orP [/eqP EQ | LE]; last by apply IHk.
      destruct (boolP (job_ready sched j t)) as [READY | NREADY].
      { by exists j; repeat split; eauto using (H_priority_is_reflexive 0). }
      { move: NREADY; rewrite //= PEND Bool.andb_true_l => /allPn [j' IN NCOMP].
        have LE' : job_arrival j' <= k.
        { by apply arrives_in_task_arrivals_before_implies_arrives_before in IN; rewrite // -ltnS -EQ. }
        have ARR' : arrives_in arr_seq j'.
        { by eapply arrives_in_task_arrivals_implies_arrived; eauto 2. }
        have PEND' : pending sched j' t.
        { apply/andP; split; last by done.
          move: PEND => /andP [LE _].
          by unfold has_arrived in *; lia.
        }
        specialize (IHk j' LE' t ARR' PEND').
        destruct IHk as [j'' [ARR'' [READY'' HEP'']]].
        exists j''; repeat split; auto.
        clear EQ; apply arrives_in_task_arrivals_implies_job_task in IN; move: IN => /eqP EQ.
        by rewrite /hep_job /FP_to_JLFP -EQ.
      }
    }
  Qed.

End SequentialTasksReadiness.
