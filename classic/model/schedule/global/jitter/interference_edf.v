Require Import rt.util.all.
Require Import rt.model.arrival.basic.task rt.model.arrival.basic.arrival_sequence rt.model.priority rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.global.jitter.job
               rt.model.schedule.global.jitter.schedule
               rt.model.schedule.global.jitter.interference
               rt.model.schedule.global.jitter.platform.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module InterferenceEDF.

  Import ScheduleWithJitter Priority Platform Interference Priority.
  
  Section Lemmas. 

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_jitter: Job -> time.
    
    (* Assume any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* Consider any schedule. *)
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    
    (* Assume that the schedule satisfies the global scheduling invariant
       for EDF, i.e., if any job of tsk is backlogged, every processor
       must be busy with jobs with no larger absolute deadline. *)
    Hypothesis H_scheduler_uses_EDF:
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched
                           (EDF job_arrival job_deadline). 

    (* Under EDF scheduling, a job only causes interference if its deadline
       is not larger than the deadline of the analyzed job. *)
    Lemma interference_under_edf_implies_shorter_deadlines :
      forall j j' t1 t2,
        arrives_in arr_seq j ->
        arrives_in arr_seq j' ->
        job_interference job_arrival job_cost job_jitter sched j' j t1 t2 != 0 ->
        job_arrival j + job_deadline j <= job_arrival j' + job_deadline j'.
    Proof.
      rename H_scheduler_uses_EDF into PRIO.
      intros j j' t1 t2 ARR ARR' INTERF.
      unfold job_interference in INTERF.
      destruct ([exists t': 'I_t2,
                   [exists cpu: processor num_cpus,
                      (t' >= t1) &&
                      backlogged job_arrival job_cost job_jitter sched j' t' &&
                      scheduled_on sched j cpu t']]) eqn:EX.
      {
        move: EX => /existsP [t' /existsP [cpu /andP [/andP [LE BACK] SCHED]]].
        apply PRIO with (t := t'); try (by done).
        by apply/existsP; exists cpu.
      }
      {
        apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL.
        rewrite big_nat_cond (eq_bigr (fun x => 0)) in INTERF;
          first by rewrite -big_nat_cond big_const_nat iter_addn mul0n  addn0 eq_refl in INTERF.
        move => i /andP [/andP [GEi LTi] _].
        specialize (ALL (Ordinal LTi)).
        rewrite negb_exists in ALL.
        move: ALL => /forallP ALL.
        rewrite (eq_bigr (fun x => 0));
          first by rewrite big_const_ord iter_addn mul0n addn0.
        intros cpu _; specialize (ALL cpu); simpl in ALL.
        destruct (backlogged job_arrival job_cost job_jitter sched j' i); last by rewrite andFb.
        rewrite GEi 2!andTb in ALL; rewrite andTb.
        by apply negbTE in ALL; rewrite ALL.
      }
    Qed.

  End Lemmas.

End InterferenceEDF.