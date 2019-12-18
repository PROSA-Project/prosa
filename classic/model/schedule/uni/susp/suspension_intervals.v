Require Import prosa.classic.util.all.

Require Import prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.susp.last_execution.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module SuspensionIntervals.

  Export Job UniprocessorSchedule Suspension LastExecution.

  (* In this section we define job suspension intervals in a schedule. *)
  Section DefiningSuspensionIntervals.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Consider any job suspension times... *)
    Variable next_suspension: job_suspension Job.

    (* ...and any uniprocessor schedule. *)
    (*Context {arr_seq: arrival_sequence Job}.*)
    Variable sched: schedule Job.

    (* For simplicity, let's define some local names. *)
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.

    (* Based on the time after the last execution of a job, we define next
       whether a job is suspended. *)
    Section JobSuspension.
      
      (* Let j be any job. *)
      Variable j: Job.

      Section DefiningSuspension.
        
        (* We are going to define whether job j is suspended at time t. *)
        Variable t: time.

        (* First, we define the beginning of the latest self suspension as the
           time following the last execution of job j in the interval [0, t).
           (Note that suspension_start can return time t itself.) *)
        Let suspension_start := time_after_last_execution job_arrival sched j t.

        (* Next, using the service received by j in the interval [0, suspension_start),...*)
        Let current_service := service sched j suspension_start.

        (* ... we recall the duration of the suspension expected for job j after having
           received that amount of service. *)
        Definition suspension_duration := next_suspension j current_service.

        (* Then, we say that job j is suspended at time t iff j has not completed
           by time t and t lies in the latest suspension interval.
           (Also note that the suspension interval can have duration 0, in which
            case suspended_at will be trivially false.)                         *)
        Definition suspended_at :=
          ~~ completed_by job_cost sched j t &&
          (suspension_start <= t < suspension_start + suspension_duration).

      End DefiningSuspension.

      (* Based on the notion of suspension, we also define the cumulative
         suspension time of job j in any interval [t1, t2)... *)
      Definition cumulative_suspension_during (t1 t2: time) :=
        \sum_(t1 <= t < t2) (suspended_at t).

      (* ...and the cumulative suspension time in any interval [0, t). *)
      Definition cumulative_suspension (t: time) := cumulative_suspension_during 0 t.

    End JobSuspension.

    (* Next, we define whether the schedule respects self-suspensions. *)
    Section SuspensionAwareSchedule.

      (* We say that the schedule respects self-suspensions iff suspended
         jobs are never scheduled. *)
      Definition respects_self_suspensions :=
        forall j t,
          job_scheduled_at j t -> ~ suspended_at j t.

    End SuspensionAwareSchedule.
    
    (* In this section, we prove several results related to job suspensions. *)
    Section Lemmas.

      (* First, we prove that at any time within any suspension interval, 
         a job is always suspended. *)
      Section InsideSuspensionInterval.

        (* Assume that jobs do not execute before they arrive... *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute job_arrival sched.

        (* ...and nor after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
      
        (* Assume that the schedule respects self-suspensions. *)
        Hypothesis H_respects_self_suspensions: respects_self_suspensions.
      
        (* Let j be any job. *)
        Variable j: Job.

        (* Consider any time t after the arrival of j... *)
        Variable t: time.
        Hypothesis H_has_arrived: has_arrived job_arrival j t.

        (* ...and recall the latest suspension interval of job j relative to time t. *)
        Let suspension_start := time_after_last_execution job_arrival sched j t.
        Let duration := suspension_duration j t.

        (* First, we analyze the service received during a suspension interval. *)
        Section SameService.
          
          (* Let t_in be any time in the suspension interval relative to time t. *)
          Variable t_in: time.
          Hypothesis H_within_suspension_interval:
            suspension_start <= t_in <= suspension_start + duration.

          (* Then, we show that the service received before time t_in
             equals the service received before the beginning of the
             latest suspension interval (if exists). *)
          Lemma same_service_in_suspension_interval:
            service sched j t_in = service sched j suspension_start.
          Proof.
            rename H_within_suspension_interval into BETWEEN,
                   H_respects_self_suspensions into SUSP, t_in into i.
            generalize dependent i.
            suff SAME:
              forall delta,
                delta <= duration ->
                service sched j (suspension_start + delta) =
                service sched j suspension_start.
            {
              move => i /andP [GE LT].
              feed (SAME (i-suspension_start)); first by rewrite leq_subLR.
              by rewrite addnBA // addKn in SAME.
            }
            induction delta; first by rewrite addn0.
            intros LT.
            feed IHdelta; first by apply ltnW.
            rewrite addnS -[service _ _ suspension_start]addn0.
            rewrite /service /service_during big_nat_recr //=.
            f_equal; first by done.
            apply/eqP; rewrite eqb0; apply/negP; intro SCHED.
            move: (SCHED) => SCHED'.
            apply SUSP in SCHED; apply SCHED; clear SCHED.
            rewrite /suspended_at /suspension_duration.
            case: (boolP (completed_by _ _ _ _)) => [COMP | NOTCOMP];
              first by apply completed_implies_not_scheduled in COMP;
                first by rewrite SCHED' in COMP.
            rewrite andTb (same_service_implies_same_last_execution _ _ _ _
                                                                    suspension_start) //.
            rewrite /suspension_start last_execution_idempotent //.
            apply/andP; split; first by apply leq_addr.
            by rewrite ltn_add2l.
          Qed.

        End SameService.

        (* Next, we infer that the job is suspended at all times during
           the suspension interval. *)
        Section JobSuspendedAtAllTimes.

          (* Let t_in be any time before the completion of job j. *)
          Variable t_in: time.
          Hypothesis H_not_completed: ~~ job_completed_by j t_in.

          (* If t_in lies in the suspension interval relative to time t, ...*)
          Hypothesis H_within_suspension_interval:
            suspension_start <= t_in < suspension_start + duration.

          (* ...then job j is suspended at time t_in. More precisely, the suspension
             interval relative to time t_in is included in the suspension interval
             relative to time t. *)
          Lemma suspended_in_suspension_interval:
            suspended_at j t_in.
          Proof.
            rename H_within_suspension_interval into BETWEEN.
            move: BETWEEN => /andP [GE LT].
            have ARR: has_arrived job_arrival j t_in.
            {
              apply leq_trans with (n := suspension_start); last by done.
              rewrite -/(has_arrived job_arrival j suspension_start).
              by apply last_execution_after_arrival.
            }
            apply/andP; split; first by done.
            apply/andP; split;
              first by apply last_execution_bounded_by_identity.
            apply (leq_trans LT).
            have SAME: time_after_last_execution job_arrival sched j t =
                       time_after_last_execution job_arrival sched j t_in.
            {
              set b := _ _ t.
              rewrite [_ _ t_in](same_service_implies_same_last_execution _ _ _ _ b);
                first by rewrite last_execution_idempotent.
              apply same_service_in_suspension_interval.
              by apply/andP; split; last by apply ltnW.
            }
            rewrite /suspension_start SAME leq_add2l.
            by rewrite /duration /suspension_duration SAME.
          Qed.
 
        End JobSuspendedAtAllTimes.
        
      End InsideSuspensionInterval.
      
      (* Next, we prove lemmas about the state of a suspended job. *)
      Section StateOfSuspendedJob.

        (* Assume that jobs do not execute before they arrived. *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute job_arrival sched.
        
        (* Let j be any job. *)
        Variable j: Job.

        (* Assume that j is suspended at time t. *)
        Variable t: time.
        Hypothesis H_j_is_suspended: suspended_at j t.

        (* First, we show that j must have arrived by time t. *)
        Lemma suspended_implies_arrived: has_arrived job_arrival j t. 
        Proof.
          rename H_j_is_suspended into SUSP.
          move: SUSP => /andP [_ SUSP].
          rewrite -[_ && _]negbK in SUSP; move: SUSP => /negP SUSP.
          rewrite /has_arrived leqNgt; apply/negP; intro LT.
          apply SUSP; clear SUSP.
          rewrite negb_and; apply/orP; left.
          rewrite -ltnNge.
          apply: (leq_trans LT); clear LT.
          rewrite /time_after_last_execution.
          case EX: [exists _, _]; last by apply leqnn.
          set t' := \max_(_ < _ | _)_.
          move: EX => /existsP [t0 EX].
          apply bigmax_pred in EX; rewrite -/t' /job_scheduled_at in EX.
          apply leq_trans with (n := t'); last by apply leq_addr.
          rewrite leqNgt; apply/negP; intro LT.
          have NOTSCHED: ~~ scheduled_at sched j t'.
          {
            rewrite -eqb0; apply/eqP.
            by eapply service_before_job_arrival_zero; first by eauto.
          }
          by rewrite EX in NOTSCHED.
        Qed.

        (* By the definition of suspension, it also follows that j cannot
           have completed by time t. *)
        Corollary suspended_implies_not_completed:
          ~~ completed_by job_cost sched j t.
        Proof.
          by move: H_j_is_suspended => /andP [NOTCOMP _].
        Qed.

      End StateOfSuspendedJob.

      (* Next, we establish a bound on the cumulative suspension time of any job. *)
      Section BoundOnCumulativeSuspension.

        (* Assume that jobs do not execute before they arrive... *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute job_arrival sched.

        (* ...and nor after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
      
        (* Assume that the schedule respects self-suspensions. *)
        Hypothesis H_respects_self_suspensions: respects_self_suspensions.

        (* Let j be any job. *)
        Variable j: Job.

        (* Recall the total suspension of job j as given by the dynamic suspension model. *)
        Let cumulative_suspension_of_j :=
          cumulative_suspension_during j.
        Let total_suspension_of_j :=
          total_suspension job_cost next_suspension j.

        (* We prove that the cumulative suspension time of job j in any
           interval is upper-bounded by the total suspension time. *)
        Lemma cumulative_suspension_le_total_suspension:
          forall t1 t2,
            cumulative_suspension_of_j t1 t2 <= total_suspension_of_j.
        Proof.
          unfold cumulative_suspension_of_j, cumulative_suspension_during,
                 total_suspension_of_j, total_suspension.
          intros t1 t2.
          apply leq_trans with (n := \sum_(0 <= s < job_cost j)
                            \sum_(t1 <= t < t2 | service sched j t == s) suspended_at j t).
          { rewrite (exchange_big_dep_nat (fun x => true)) //=.
            apply leq_sum; intros s _.
            destruct (boolP (suspended_at j s)) as [SUSP | NOTSUSP]; last by done.
            rewrite (big_rem (service sched j s)); first by rewrite eq_refl.
            rewrite mem_index_iota; apply/andP; split; first by done.
            rewrite ltn_neqAle; apply/andP; split;
              last by apply cumulative_service_le_job_cost.
            apply suspended_implies_not_completed in SUSP.
            rewrite neq_ltn; apply/orP; left.
              by rewrite ltnNge.
          }
          { apply leq_sum_nat; move => s /andP [_ LT] _.
            destruct (boolP [exists t:'I_t2, (t>=t1)&& (service sched j t==s)]) as [EX|ALL];
              last first.
            {
              rewrite negb_exists in ALL; move: ALL => /forallP ALL.
              rewrite big_nat_cond big1 //.
              move => i /andP [/andP [GEi LTi] SERV].
              by specialize (ALL (Ordinal LTi)); rewrite /= SERV GEi andbT in ALL.
            }
            move: EX => /existsP [t' /andP [GE' /eqP SERV]].
            unfold suspended_at, suspension_duration.
            set b := time_after_last_execution job_arrival sched j.
            set n := next_suspension j s.
            apply leq_trans with (n := \sum_(t1 <= t < t2 | b t' <= t < b t' + n) 1).
            {
              rewrite big_mkcond [\sum_(_ <= _ < _ | b t' <= _ < _) _]big_mkcond /=.
              apply leq_sum_nat; intros t LEt _.
              case: (boolP (completed_by _ _ _ _)) => [COMP | NOTCOMP];
                [by case (_ == _) | simpl].
              case EQ: (service _ _ _ == _); last by done.
              move: EQ => /eqP EQ. rewrite /n -EQ.
              case INT: (_ <= _ < _); last by done.
              apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
              move: INT => /andP [GEt LTt].
              rewrite (same_service_in_suspension_interval _ _ _ _ t') //.
              {
                rewrite -/b [b t'](same_service_implies_same_last_execution _ _ _ _ t);
                  last by rewrite SERV EQ.
                by apply/andP; split.
              }
              {
                rewrite /suspension_duration -/b.
                rewrite [b t'](same_service_implies_same_last_execution _ _ _ _ t);
                  last by rewrite SERV EQ.
                by apply/andP; split; last by apply ltnW.
              }
            }
            apply leq_trans with (n := \sum_(b t' <= t < b t' + n) 1);
              last by simpl_sum_const; rewrite addKn.
            by apply leq_sum1_smaller_range; move => i [LE LE']; split.
          }
        Qed.

      End BoundOnCumulativeSuspension.
      
      (* Next, we show that when a job completes, it must have suspended
         as long as the total suspension time. *)
      Section SuspendsForTotalSuspension.

        (* Assume that jobs do not execute before they arrive... *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute job_arrival sched.

        (* ...and nor after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
      
        (* Assume that the schedule respects self-suspensions. *)
        Hypothesis H_respects_self_suspensions: respects_self_suspensions.

        (* Let j be any job. *)
        Variable j: Job.

        (* Assume that j has completed by time t. *)
        Variable t: time.
        Hypothesis H_j_has_completed: completed_by job_cost sched j t.

        (* Then, we prove that the cumulative suspension time must be
           exactly equal to the total suspension time of the job. *)
        Lemma cumulative_suspension_eq_total_suspension:
          cumulative_suspension j t = total_suspension job_cost next_suspension j.
        Proof.
          rename H_j_has_completed into COMP, H_jobs_must_arrive_to_execute into ARR.
          have EARLIER := exists_last_execution_with_smaller_service job_arrival
                                                           job_cost sched ARR j t COMP.
          apply/eqP; rewrite eqn_leq; apply/andP; split;
            first by apply cumulative_suspension_le_total_suspension.
          rewrite /total_suspension /cumulative_suspension /cumulative_suspension_during.
          move: COMP => /eqP COMP.
          apply leq_trans with (n := \sum_(0 <= s < job_cost j)
                           \sum_(0 <= t0 < t | service sched j t0 == s) suspended_at j t0);
            last first.
          {
            rewrite (exchange_big_dep_nat (fun x => true)) //=.
            apply leq_sum_nat; move => t0 /andP [_ LT] _.
            case (boolP [exists s: 'I_(job_cost j), service sched j t0 == s]) => [EX | ALL].
            {
              move: EX => /existsP [s /eqP EQs].
              rewrite big_mkcond /=.
              rewrite (bigD1_seq (nat_of_ord s)); [simpl | | by apply iota_uniq];
                last by rewrite mem_index_iota; apply/andP;split; last by apply ltn_ord.
              rewrite EQs eq_refl big1; first by rewrite addn0.
              by move => i /negbTE NEQ; rewrite eq_sym NEQ.
            }
            {
              rewrite big_nat_cond big1; first by done.
              move => i /andP [/andP [_ LTi] /eqP SERV].
              rewrite negb_exists in ALL; move: ALL => /forallP ALL.
              by specialize (ALL (Ordinal LTi)); rewrite /= SERV eq_refl in ALL.
            }
          }
          {
            apply leq_sum_nat; move => s /andP [_ LTs] _.
            rewrite /suspended_at /suspension_duration.
            set b := time_after_last_execution job_arrival sched j.
            set n := next_suspension j.

            move: (EARLIER s LTs) => [t' EQ'].
            apply leq_trans with (n := \sum_(0 <= t0 < t | (service sched j t0 == s) &&
                          (b t' <= t0 < b t' + n (service sched j (b t')))) 1); last first.
            { rewrite big_mkcond [\sum_(_ <= _ < _ | _ == s)_]big_mkcond.
              apply leq_sum_nat; move => i /andP [_ LTi] _.
              case EQi: (service sched j i == s); [rewrite andTb | by rewrite andFb].
              case LE: (_ <= _ <= _); last by done.
              rewrite lt0n eqb0 negbK.
              apply suspended_in_suspension_interval with (t := t'); try (by done).
              rewrite -ltnNge.
                by apply: (leq_ltn_trans _ LTs); apply eq_leq; apply/eqP.
            }
            { apply leq_trans with (n := \sum_(b t'<= t0< b t'+ n (service sched j (b t')) |
                                            (0 <= t0 < t) && (service sched j t0 == s)) 1).
              {
                apply leq_trans with (n := \sum_(b t' <= t0 < b t'
                                                         + n (service sched j (b t'))) 1);
                  first by simpl_sum_const; rewrite addKn -EQ'.
                rewrite [in X in _ <= X]big_mkcond /=.
                apply leq_sum_nat; move => i /andP [LEi GTi] _.
                apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
                apply/andP; split.
                {
                  have SUSPi: suspended_at j i.
                  {
                    apply: (suspended_in_suspension_interval _ _ _ _ t');
                      try (by done); last by apply/andP; split.
                    rewrite -ltnNge.
                    rewrite (same_service_in_suspension_interval _ _ _ _ t') //;
                      first by rewrite EQ'.
                    by apply/andP; split; last by apply ltnW.
                  }
                  apply contraT; rewrite -leqNgt; intro LE.
                  apply suspended_implies_not_completed in SUSPi.
                  exfalso; move: SUSPi => /negP COMPi; apply COMPi.
                  apply completion_monotonic with (t0 := t); try (by done).
                  by apply/eqP.
                }
                {
                  rewrite -EQ'; apply/eqP.
                  apply same_service_in_suspension_interval; try (by done).
                  by apply/andP; split; last by apply ltnW.
                }
              }
              {
                apply leq_sum1_smaller_range.
                by move => i [LEb /andP [LE EQs]]; split;
                  last by apply/andP; split.
              }
            }
          }
        Qed.
        
      End SuspendsForTotalSuspension.

      (* In this section, we prove that a job executes just before it starts suspending.  *)
      Section ExecutionBeforeSuspension.

        (* Assume that jobs do not execute before they arrive... *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute job_arrival sched.

        (* ...and nor after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
      
        (* Assume that the schedule respects self-suspensions. *)
        Hypothesis H_respects_self_suspensions: respects_self_suspensions.

        (* Let j be any job... *)
        Variable j: Job.

        (* ...that has arrived by some time t. *)
        Variable t: time.
        Hypothesis H_arrived: has_arrived job_arrival j t.

        (* If job j is not suspended at time t, but starts to suspend at time t + 1, ... *)
        Hypothesis H_not_suspended_at_t: ~~ suspended_at j t.
        Hypothesis H_begins_suspension: suspended_at j t.+1.

        (* ...then j must be scheduled at time t. *)
        Lemma executes_before_suspension:
          scheduled_at sched j t.
        Proof.
          rename H_not_suspended_at_t into NOTSUSPs, H_begins_suspension into SUSPs'.
          move: SUSPs' => /andP [NOTCOMP' /andP [GE LT]].
          apply contraT; intro NOTSCHED.
          suff BUG: suspended_at j t by rewrite BUG in NOTSUSPs.
          apply suspended_in_suspension_interval with (t := t.+1); try done.
          {
            apply contraT; rewrite negbK; intro COMP.
            suff COMP': completed_by job_cost sched j t.+1 by rewrite COMP' in NOTCOMP'.
            by apply completion_monotonic with (t0 := t).
          }
          apply/andP; split; last by apply: (leq_ltn_trans _ LT).
          apply leq_trans with (n := time_after_last_execution job_arrival sched j t);
            last by apply last_execution_bounded_by_identity.
          apply eq_leq, same_service_implies_same_last_execution.
          rewrite /service /service_during big_nat_recr //= /service_at.
          by apply negbTE in NOTSCHED; rewrite NOTSCHED addn0.
        Qed.
        
      End ExecutionBeforeSuspension.
      
    End Lemmas.
      
  End DefiningSuspensionIntervals.

End SuspensionIntervals.
