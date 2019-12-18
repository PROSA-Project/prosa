Require Import prosa.classic.util.all prosa.classic.util.find_seq
               Arith.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.schedule.uni.basic.platform_tdma
               prosa.classic.model.arrival.basic.task prosa.classic.model.policy_tdma.
Require Import prosa.classic.model.schedule.uni.schedule prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.priority
               prosa.classic.analysis.uni.basic.tdma_rta_theory
               prosa.classic.model.schedule.uni.transformation.construction.
Require Import prosa.classic.implementation.job prosa.classic.implementation.task
               prosa.classic.implementation.arrival_sequence
               prosa.classic.implementation.uni.basic.schedule.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Set Bullet Behavior "Strict Subproofs".
Module ConcreteSchedulerTDMA.

  Import Job ArrivalSequence UniprocessorSchedule SporadicTaskset Schedulability Priority
         ResponseTimeAnalysisTDMA PolicyTDMA ScheduleConstruction Platform_TDMA.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler BigOp.
 
  Section ImplementationTDMA.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    Variable arr_seq: arrival_sequence Job.

    Variable ts: {set Task}.

    Variable time_slot: TDMA_slot Task.

    Variable slot_order: TDMA_slot_order Task.

    Hypothesis H_arrival_times_are_consistent: 
        arrival_times_are_consistent job_arrival arr_seq.

    Section JobSchedule.

        Variable sched: schedule Job.
        Variable t:time.

        Let is_pending := pending job_arrival job_cost sched.

        Definition pending_jobs:=
             [seq j <- jobs_arrived_up_to arr_seq t | is_pending j t].


        Let job_in_time_slot:=
          fun job => Task_in_time_slot ts slot_order (job_task job) time_slot t.


        Definition job_to_schedule :=
          findP job_in_time_slot pending_jobs.

      Section Lemmas.

        Hypothesis arr_seq_is_a_set:
          arrival_sequence_is_a_set arr_seq.

        Lemma pending_jobs_uniq:
          uniq pending_jobs.
        Proof.
        apply filter_uniq
        , arrivals_uniq with (job_arrival0:=job_arrival);auto.
        Qed.


        Lemma respects_FIFO:
          forall j j', j \in pending_jobs -> j' \in pending_jobs ->
          find (fun job => job==j') pending_jobs
           < find (fun job => job==j) pending_jobs ->
          job_arrival j' <= job_arrival j.
        Proof.
        rewrite /job_to_schedule /pending_jobs /jobs_arrived_up_to
        /jobs_arrived_between. intros*.
        repeat rewrite mem_filter.
        move=> /andP [PENJ JIN] /andP [PENJ' J'IN] LEQ.
        apply mem_bigcat_nat_exists in JIN.
        apply mem_bigcat_nat_exists in J'IN.
        destruct JIN as [arrj [JIN _]].
        destruct J'IN as [arrj' [J'IN _]].
        have ARRJ: job_arrival j = arrj by eauto.
        have ARRJ': job_arrival j' = arrj' by eauto.
        have JLT: arrj' <= t by move:PENJ'=>/andP [HAD _]; eauto.
        destruct (leqP arrj' arrj) as [G|G]. eauto.
        apply mem_bigcat_nat with (m:=0) (n:=arrj.+1) in JIN;auto.
        apply mem_bigcat_nat with (m:=arrj.+1) (n:=t.+1) in J'IN;auto.
        have BIGJ: j \in [seq j <- \big[cat/[::]]_(0 <= i < arrj.+1)
                    jobs_arriving_at arr_seq i | is_pending j t]
        by rewrite mem_filter;apply /andP.
        have BIGJ': j' \in [seq j <- \big[cat/[::]]_(arrj.+1 <= i < t.+1)
                    jobs_arriving_at arr_seq i | is_pending j t]
        by rewrite mem_filter;apply /andP.
        rewrite ->big_cat_nat with (n:=arrj.+1) in LEQ;try ssromega.
        rewrite filter_cat find_cat /=in LEQ.
        rewrite find_cat /= in LEQ.
        have F: (has (fun job : Job => job == j')
          [seq j <- \big[cat/[::]]_(0 <= i < arrj.+1)
                       jobs_arriving_at arr_seq i
             | is_pending j t]) = false .
        apply find_uniq with (l2:=
        [seq j <- \big[cat/[::]]_(arrj.+1 <= i < t.+1)
                       jobs_arriving_at arr_seq i
             | is_pending j t]);auto.
        rewrite -filter_cat -big_cat_nat;auto. apply pending_jobs_uniq.
        ssromega.
        have TT: (has (fun job : Job => job == j)
          [seq j <- \big[cat/[::]]_(0 <= i < arrj.+1)
                       jobs_arriving_at arr_seq i
             | is_pending j t]) = true. apply /hasP. by exists j.
        have FI: find (fun job : Job => job == j)
          [seq j <- \big[cat/[::]]_(0 <= t < arrj.+1)
                       jobs_arriving_at arr_seq t
             | is_pending j t] < size (
          [seq j <- \big[cat/[::]]_(0 <= t < arrj.+1)
                       jobs_arriving_at arr_seq t
             | is_pending j t]). by rewrite -has_find.
       rewrite F TT in LEQ. ssromega.
        Qed.
      
        Lemma pending_job_in_penging_list:
          forall j, arrives_in arr_seq j ->
          pending job_arrival job_cost sched j t ->
          j \in pending_jobs.
        Proof.
        intros* ARRJ PEN.
        rewrite mem_filter. apply /andP. split.
        apply PEN. rewrite /jobs_arrived_up_to.
        apply arrived_between_implies_in_arrivals with (job_arrival0:=job_arrival).
        apply H_arrival_times_are_consistent. auto.
        rewrite /arrived_between. simpl. 
        rewrite /pending in PEN. move:PEN=>/andP [ARRED _].
        rewrite /has_arrived in ARRED. auto.
        Qed.

        Lemma pendinglist_jobs_in_arr_seq:
          forall j, j \in pending_jobs ->
           arrives_in arr_seq j.
        Proof.
        intros* JIN.
        rewrite mem_filter in JIN. move /andP in JIN.
        destruct JIN as [PEN ARR]. rewrite /jobs_arrived_up_to in ARR.
        by apply in_arrivals_implies_arrived with (t1:= 0)(t2:= t.+1).
        Qed.
      End Lemmas.

    End JobSchedule.



    Section SchedulerTDMA.

        Let empty_schedule : schedule Job := fun t => None.
        Definition scheduler_tdma:=
           build_schedule_from_prefixes job_to_schedule empty_schedule.

        Lemma scheduler_depends_only_on_prefix:
          forall sched1 sched2 t,
          (forall t0, t0 < t -> sched1 t0 = sched2 t0) ->
          job_to_schedule sched1 t = job_to_schedule sched2 t.
        Proof.
        intros * ALL.
        rewrite /job_to_schedule. f_equal.
        apply eq_in_filter.
        intros j ARR.
        apply in_arrivals_implies_arrived_before 
        with (job_arrival0 := job_arrival) in ARR.
        rewrite /arrived_before ltnS in ARR.
        rewrite /pending /has_arrived ARR. repeat rewrite andTb; f_equal.
        rewrite /completed_by; f_equal.
        apply eq_big_nat. intros.
        by rewrite /service_at /scheduled_at ALL.
        assumption.
      Qed.

      Lemma scheduler_uses_construction_function:
      forall t, scheduler_tdma t = job_to_schedule scheduler_tdma t.
      Proof.
      intro t. apply prefix_dependent_schedule_construction.
      apply scheduler_depends_only_on_prefix.
      Qed.

    End SchedulerTDMA.

    
    Let sched:=
      scheduler_tdma.


    Theorem scheduler_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Proof.
      move => j t /eqP SCHED.
      rewrite /sched scheduler_uses_construction_function /job_to_schedule in SCHED.
      apply findP_in_seq in SCHED. move:SCHED => [IN PEN].
      rewrite mem_filter in PEN.
      by move: PEN => /andP [/andP [ARR _] _].
    Qed.

    Theorem scheduler_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.
    Proof.
      intros j t.
      induction t;
        first by rewrite /service /service_during big_geq //.
      rewrite /service /service_during big_nat_recr //=.
      rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LT]; last first.
      {
        apply: leq_trans LT; rewrite -addn1.
          by apply leq_add; last by apply leq_b1.
      }
      rewrite -[job_cost _]addn0; apply leq_add; first by rewrite -EQ.
      rewrite leqn0 eqb0 /scheduled_at.
      rewrite /sched scheduler_uses_construction_function //.
      rewrite /job_to_schedule.
      apply/eqP; intro FIND.
      apply findP_in_seq in FIND. move:FIND => [IN PEN].
      by rewrite mem_filter /pending /completed_by -EQ leqnn andbF andFb in PEN.
    Qed.

  End ImplementationTDMA.

End ConcreteSchedulerTDMA.