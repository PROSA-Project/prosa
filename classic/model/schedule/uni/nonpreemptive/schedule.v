Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.schedule.uni.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module NonpreemptiveSchedule.

  Export UniprocessorSchedule.

  Section Definitions.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    
    (* Consider any uniprocessor schedule. *)
    Variable sched: schedule Job.

    (* For simplicity, let's define some local names. *)
    Let job_completed_by := completed_by job_cost sched.
    Let job_remaining_cost j t := remaining_cost job_cost sched j t.
    
    (* We define schedule to be nonpreemptive iff every job remains scheduled until completion. *)
    Definition is_nonpreemptive_schedule := 
      forall j t t',
        t <= t' -> 
        scheduled_at sched j t ->
        ~~ job_completed_by j t' -> 
        scheduled_at sched j t'. 

    (* In this section, we prove some basic lemmas about nonpreemptive schedules. *)
    Section Lemmas.

      (* Assume that we have a nonpreemptive schedule. *)
      Hypothesis H_nonpreemptive: is_nonpreemptive_schedule.

      Section BasicLemmas.

        (* Consider any job j. *)
        Variable j: Job.
        
        (* Assume that completed jobs do not execute. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
        
        (* First, we show that if j is scheduled at any two time instants, 
           then it is also scheduled at any time between them. *)
        Lemma continuity_of_nonpreemptive_scheduling:
          forall t t1 t2,
            t1 <= t <= t2 ->
            scheduled_at sched j t1 ->
            scheduled_at sched j t2 ->
            scheduled_at sched j t.
        Proof.
          move => t t1 t2 /andP [GT LE] SCHEDt1 SCHEDt2.          
          unfold is_nonpreemptive_schedule, job_completed_by in *.
          apply H_nonpreemptive with (t := t1); [by done| by done| ].
          apply /negP; intros COMP.
          apply (scheduled_implies_not_completed job_cost) in SCHEDt2; last by done.
          apply completion_monotonic with (t' := t2) in COMP; last by done.
            by move: SCHEDt2 => /negP SCHEDt2; apply: SCHEDt2.
        Qed.

        (* Next, we show that in any nonpreemptive schedule, once a job is scheduled, 
           it cannot be preempted until completion. *)
        Lemma in_nonpreemption_schedule_preemption_implies_completeness:
          forall t t' ,
            t <= t' ->
            scheduled_at sched j t ->
            ~~ scheduled_at sched j t' ->
            job_completed_by j t'.
        Proof.
          intros t t' LE SCHED; apply contraNT.
            by apply H_nonpreemptive with (t := t). 
        Qed.
         
      End BasicLemmas.
      
      (* In this section, we prove properties related to job completion. *)
      Section CompletionUnderNonpreemptive.
        
        (* Assume that completed jobs do not execute. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.

        (* If job j is scheduled at time t, then it must complete by (t + remaining_cost j t). *)
        Lemma job_completes_after_remaining_cost:
          forall j t,
            scheduled_at sched j t ->
            job_completed_by j (t + job_remaining_cost j t).
        Proof.
          intros j t SCHED.
          rewrite /job_completed_by /completed_by.
          rewrite /service /service_during.
          rewrite (@big_cat_nat _ _ _ t) //= ?leq_addr //.
          apply leq_trans with (n := service sched j t + job_remaining_cost j t);
            first by rewrite /remaining_cost subnKC //.
          rewrite leq_add2l.
          set t2 := t + _.
          apply leq_trans with (n := \sum_(t <= i < t2) 1);
            first by simpl_sum_const; rewrite /t2 addKn.
          apply leq_sum_nat. 
          move => i /andP [GE LT _].
          rewrite lt0n eqb0 negbK.
          apply (H_nonpreemptive j t i); try (by done).
          unfold t2 in *; clear t2.
          have NOTCOMP: ~~ job_completed_by j t.
          {
            apply contraT. rewrite negbK. intros COMP.
            apply completed_implies_not_scheduled in COMP; last by done.
              by rewrite SCHED in COMP.
          }
          apply job_doesnt_complete_before_remaining_cost in NOTCOMP; last by done.
          apply contraT; rewrite negbK; intros COMP.
          exfalso; move: NOTCOMP => /negP NOTCOMP; apply: NOTCOMP.
          apply completion_monotonic with (t0 := i); try ( by done).
            by apply subh3; first rewrite addn1.
        Qed.
        
      End CompletionUnderNonpreemptive.

      (* In this section, we determine bounds on the length of the execution interval. *)
      Section ExecutionInterval.
        
        (* Assume that jobs do not execute after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.

        (* Let j be any job scheduled at time t. *)
        Variable j: Job.
        Variable t: time.
        Hypothesis H_j_is_scheduled_at_t: scheduled_at sched j t.

        (* Is this section we show that there is a bound for how early job j can start. *)
        Section LeftBound.
          
          (* We prove that job j is scheduled at time (t - service sched j t)... *)
          Lemma  j_is_scheduled_at_t_minus_service:
            scheduled_at sched j (t - service sched j t).
          Proof.
            unfold is_nonpreemptive_schedule in *.
            apply contraT; intros CONTRA; exfalso.
            rename H_j_is_scheduled_at_t into SCHED.
            have COSTPOS: job_cost j > 0.
            { apply (scheduled_implies_not_completed job_cost) in SCHED; last by done.
              unfold job_completed_by, completed_by in SCHED.
              apply contraT; rewrite -eqn0Ngt.
              move => /eqP EQ0.
              rewrite EQ0 in SCHED.
                by rewrite -ltnNge ltn0 in SCHED.
            }

            have H: service sched j (t + job_remaining_cost j t) == job_cost j.
            { rewrite eqn_leq; apply/andP; split; eauto 2.
                by apply job_completes_after_remaining_cost.
            }              
            unfold job_completed_by, completed_by in H.
            move: H => /eqP H.
            unfold service, service_during in H.
            rewrite (@big_cat_nat _ _ _ (t - service sched j t)) //= in H;
              last by rewrite leq_subLR addnC -addnA leq_addr.
            have R: forall a b c, a + b = c -> b < c -> a > 0.
            {  by intros a b c EQ LT; induction a;
                first by rewrite add0n in EQ; subst b;
                rewrite ltnn in LT.        
            }
            apply R in H; last first.
            {
              have CUMLED := cumulative_service_le_delta sched j 0 t.
              have CUMLEJC := cumulative_service_le_job_cost _ _ j H_completed_jobs_dont_execute 0 t.
              rewrite (@big_cat_nat _ _ _ ((t - service sched j t).+1)) //=.
              {
                rewrite big_nat_recl; last by done.
                rewrite big_geq; last by done.
                rewrite -eqb0 in CONTRA; move: CONTRA => /eqP CONTRA.
                rewrite /service_at CONTRA add0n add0n.
                apply leq_ltn_trans with
                    (t + job_remaining_cost j t - ((t - service sched j t).+1)).
                 set (t - service sched j t).+1 as T.
                 apply leq_trans with (\sum_(T <= i < t + job_remaining_cost j t) 1).
                 rewrite leq_sum //; intros; by destruct (scheduled_at sched j i).
                 simpl_sum_const. by done.
                 unfold job_remaining_cost, remaining_cost.
                 rewrite -addn1 -addn1  subh1; first by
                     by rewrite leq_subLR addnBA;
                 first by  rewrite -addnA [1+job_cost j]addnC addnA -subh1.
                 { 
                  rewrite subh1; last by done.
                  rewrite leq_subLR addnA.
                  rewrite addnBA; last by done.
                  rewrite [_+t]addnC [_+job_cost j]addnC addnA.
                  rewrite -addnBA; last by done.
                    by rewrite subnn addn0 addnC leq_add2r.
                }
              }
              {
                unfold remaining_cost.
                rewrite addnBA; last by done.
                rewrite -addn1 subh1; last by done.
                rewrite leq_subLR -addnBA; last by done.
                rewrite addnA [_+t]addnC -addnA leq_add2l addnBA; last by done.
                  by rewrite addnC -addnBA; first by rewrite subnn addn0.
              }
            }
            {
              rewrite lt0n in H; move: H => /neqP H; apply: H.
              rewrite big_nat_cond big1 //; move => i /andP [/andP [_ LT] _].
              apply /eqP; rewrite eqb0; apply /negP; intros CONT.

              have Y := continuity_of_nonpreemptive_scheduling j _ (t - service sched j t) i t.
              feed_n 4 Y; try(done).
                by apply/andP; split; [rewrite ltnW | rewrite leq_subr].
                  by move: CONTRA => /negP CONTRA; apply CONTRA.
            }
          Qed. 
          
          (* ... and it is not scheduled at time (t - service sched j t - 1). *)
          Lemma j_is_not_scheduled_at_t_minus_service_minus_one:
            t - service sched j t > 0 ->
            ~~ scheduled_at sched j (t - service sched j t - 1).
          Proof.
            rename H_j_is_scheduled_at_t into SCHED.
            intros GT; apply/negP; intros CONTRA.
            have L1 := job_doesnt_complete_before_remaining_cost
                         job_cost sched j H_completed_jobs_dont_execute t.
            feed L1; first by rewrite scheduled_implies_not_completed.
            have L2 := job_completes_after_remaining_cost
                         H_completed_jobs_dont_execute
                         j (t-service sched j t - 1).
            feed L2; first by done. 
            have EQ:
              t + job_remaining_cost j t - 1 =
              t - service sched j t - 1 + job_remaining_cost j (t - service sched j t - 1).
            {
              have T1: service sched j (t - service sched j t - 1) = 0.
              {

                rewrite [service _ _ _]/service /service_during.
                rewrite big_nat_cond big1 //; move => t' /andP [/andP [_ LT] _]. 
                apply /eqP; rewrite eqb0; apply /negP; intros CONTR.

                have COMPL: completed_by job_cost sched j (t + job_remaining_cost j t - 1).
                {
                  apply completion_monotonic with (t0 := t' + job_remaining_cost j t');
                  [| by apply job_completes_after_remaining_cost].
                  unfold remaining_cost.
                  have LLF: t' < t - service sched j t.
                  {
                      by apply ltn_trans with (t - service sched j t - 1);
                    last by rewrite -addn1 subh1 // -addnBA // subnn addn0.
                  } clear LT.
                  rewrite !addnBA;
                    try(rewrite H_completed_jobs_dont_execute //).
                  rewrite [t' + _]addnC [t + _]addnC.
                  rewrite -addnBA; last by rewrite cumulative_service_le_delta.
                  rewrite -addnBA; last by rewrite cumulative_service_le_delta.
                  rewrite -addnBA ?leq_add2l; last by done.
                  by apply leq_trans with (t' + 1 - 1);
                    rewrite addn1 subn1 -pred_Sn;
                  [rewrite leq_subr | rewrite subh3 // addn1].
                }
                have L3 := job_doesnt_complete_before_remaining_cost job_cost sched
                             j H_completed_jobs_dont_execute t;
                    feed L3; first by rewrite scheduled_implies_not_completed.
                unfold job_completed_by in *.
                  by move: L3 => /negP L3; apply L3.
              }
              rewrite /job_remaining_cost /remaining_cost T1 subn0 addnBA; last by done.
              rewrite -subh1.
                by rewrite -[(t-service sched j t) + _ - _]subh1.
                  by rewrite cumulative_service_le_delta.
            }
            move: L1 => /neqP L1; apply: L1.
            rewrite -EQ in L2.
              by unfold job_completed_by, completed_by in L2; move: L2 => /eqP L2.
          Qed.

          (* Using the previous lemma, we show that job j cannot be scheduled 
             before (t - service sched j t). *)
          Lemma j_is_not_scheduled_earlier_t_minus_service:
            forall t',
              t' < t - service sched j t ->
              ~~ scheduled_at sched j t'.
          Proof.
            intros t' GT.
            have NOTSCHED := j_is_not_scheduled_at_t_minus_service_minus_one;
                feed NOTSCHED; first by apply leq_ltn_trans with t'.
            apply/negP;  intros CONTRA.
            move: NOTSCHED => /negP NOTSCHED; apply: NOTSCHED.
            apply continuity_of_nonpreemptive_scheduling with (t1 := t') (t2 := t);
              [ by done | | by done | by done ].
            apply/andP; split; last by apply leq_trans with (t - service sched j t); rewrite leq_subr.
            rewrite [t']pred_Sn -subn1 leq_sub2r //.
          Qed.
          
        End LeftBound.

        (* Is this section we prove that job j cannot be scheduled after (t + remaining_cost j t - 1). *)
        Section RightBound.

          (* We show that if job j is scheduled at time t, 
             then it is also scheduled at time (t + remaining_cost j t - 1)... *)
          Lemma j_is_scheduled_at_t_plus_remaining_cost_minus_one:
            scheduled_at sched j (t + job_remaining_cost j t - 1).
          Proof.
            move: (H_j_is_scheduled_at_t) => COMP.
            apply (scheduled_implies_not_completed job_cost) in COMP; last by done.
            apply  job_doesnt_complete_before_remaining_cost in COMP; last by done.
            move: COMP; apply contraR; intros CONTR.
            apply in_nonpreemption_schedule_preemption_implies_completeness
            with (t:=t); [|by done| by done].
            rewrite subh3 // ?leq_add2l.
              by rewrite scheduled_implies_positive_remaining_cost //.
          Qed.

          (* ... and it is not scheduled after (t + remaining cost j t - 1). *)       
          Lemma j_is_not_scheduled_after_t_plus_remaining_cost_minus_one:
            forall t',
              t + job_remaining_cost j t <= t' ->
              ~~ scheduled_at sched j t'.
          Proof.
            intros t' GE.
            unfold job_completed_by in *.
            rename H_j_is_scheduled_at_t into SCHED.
            apply job_completes_after_remaining_cost in SCHED; last by done.
            by apply (completion_monotonic job_cost) with (t' := t') in SCHED; first
              by apply (completed_implies_not_scheduled job_cost).
          Qed.
          
        End RightBound.
        
        (* To conclude, we identify the interval where job j is scheduled. *) 
        Lemma nonpreemptive_executing_interval:
          forall t',
            t - service sched j t <= t' < t + job_remaining_cost j t ->
            scheduled_at sched j t'.
        Proof.
          move => t' /andP [GE LE].
          move: (H_j_is_scheduled_at_t) => SCHED1; move: (H_j_is_scheduled_at_t) => SCHED2.
          rewrite -addn1 in LE; apply subh3 with (m := t') (p := 1) in LE;
            apply continuity_of_nonpreemptive_scheduling with
                (t1 := t - service sched j t)
                (t2 := t + job_remaining_cost j t - 1); first by done.
          - by apply/andP;split.
          - by apply j_is_scheduled_at_t_minus_service.
          - by apply j_is_scheduled_at_t_plus_remaining_cost_minus_one.
        Qed.
        
      End ExecutionInterval.
      
    End Lemmas.

  End Definitions.

End NonpreemptiveSchedule.