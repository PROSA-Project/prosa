Require Import rt.util.all.
Require Import rt.model.arrival.basic.task
               rt.model.arrival.basic.job
               rt.model.arrival.basic.arrival_sequence
               rt.model.priority
               rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.uni.service
               rt.model.schedule.uni.workload
               rt.model.schedule.uni.schedule.
Require Import rt.model.schedule.uni.limited.platform.definitions.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(** * Busy Interval for JLFP-models *)
(** In this module we define the notion of busy intervals for uniprocessor for JLFP schedulers. *)
Module BusyIntervalJLFP.
      
  Import Job Priority UniprocessorSchedule LimitedPreemptionPlatform Service Workload TaskArrival.
  
  Section Definitions.
 
    Context {Task: eqType}.    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any arrival sequence with consistent arrival times... *)
    Variable arr_seq: arrival_sequence Job.  
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    
    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job. 
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    
    (* Assume a given JLFP policy. *)
    Variable higher_eq_priority: JLFP_policy Job.

    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_remaining_cost j t := remaining_cost job_cost sched j t.

    (* In this section, we define the notion of a busy interval. *)
    Section BusyInterval.
      
      (* Consider an arbitrary task tsk. *) 
      Variable tsk: Task.

      (* Consider any job j of tsk. *)
      Variable j: Job.
      Hypothesis H_from_arrival_sequence: arrives_in arr_seq j.
      Hypothesis H_job_task: job_task j = tsk.     

      (* We say that t is a quiet time for j iff every higher-priority job from
       the arrival sequence that arrived before t has completed by that time. *)
      Definition quiet_time (t: time) :=
        forall j_hp,
          arrives_in arr_seq j_hp ->
          higher_eq_priority j_hp j ->
          arrived_before job_arrival j_hp t ->
          job_completed_by j_hp t.
      
      (* Based on the definition of quiet time, we say that interval
         [t1, t_busy) is a (potentially unbounded) busy-interval prefix
         iff the interval starts with a quiet time where a higher or equal 
         priority job is released and remains non-quiet. We also require
         job j to be release in the interval. *)    
      Definition busy_interval_prefix (t1 t_busy: time) :=
        t1 < t_busy /\
        quiet_time t1 /\
        (forall t, t1 < t < t_busy -> ~ quiet_time t) /\
        t1 <= job_arrival j < t_busy.

      (* Next, we say that an interval [t1, t2) is a busy interval iff
         [t1, t2) is a busy-interval prefix and t2 is a quiet time. *)
      Definition busy_interval (t1 t2: time) :=
        busy_interval_prefix t1 t2 /\
        quiet_time t2.

    End BusyInterval.

    (* In this section, we define a notion of bounded priority inversion experienced by a job. *)
    Section JobPriorityInversionBound.

      (* Consider an arbitrary task tsk. *)
      Variable tsk: Task.

      (* Consider any job j of tsk. *)
      Variable j: Job.
      Hypothesis H_from_arrival_sequence: arrives_in arr_seq j.
      Hypothesis H_job_task: job_task j = tsk.

      (* We say that the job incurs priority inversion if it has higher priority than the scheduled
         job. Note that this definition implicitly assumes that the scheduler is work-conserving in 
         the sense of the definition given in rt.model.schedule.uni.basic.platform. Therefore, it 
         cannot be applied to models with jitter or self-suspensions. *)
      Definition is_priority_inversion t :=
        if sched t is Some jlp then
          ~~ higher_eq_priority jlp j
        else false.
      
      (* Then we compute the cumulative priority inversion incurred by
         a job within some time interval [t1, t2). *)
      Definition cumulative_priority_inversion t1 t2 :=
        \sum_(t1 <= t < t2) is_priority_inversion t.

      (* We say that priority inversion of job j is bounded by a constant B iff cumulative 
         priority inversion within any busy inverval prefix is bounded by B. *)
      Definition priority_inversion_of_job_is_bounded_by (B: time) :=
        forall (t1 t2: time),
          busy_interval_prefix j t1 t2 ->
          cumulative_priority_inversion t1 t2 <= B.

    End JobPriorityInversionBound.

    (* In this section, we define a notion of the bounded priority inversion for task. *)
    Section TaskPriorityInversionBound.

      (* Consider an arbitrary task tsk. *)
      Variable tsk: Task.

      (* We say that task tsk has bounded priority inversion if all 
       its jobs have bounded cumulative priority inversion. *)
      Definition priority_inversion_is_bounded_by (B: time) :=
        forall (j: Job),
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_cost j > 0 -> 
          priority_inversion_of_job_is_bounded_by j B.

    End TaskPriorityInversionBound.
  
    (* Now we prove some lemmas about busy intervals. *)
    Section Lemmas.
      
      (* Consider an arbitrary task tsk. *)
      Variable tsk: Task.

      (* Consider an arbitrary job j. *)
      Variable j: Job.
      Hypothesis H_from_arrival_sequence: arrives_in arr_seq j.
      Hypothesis H_job_task: job_task j = tsk.
      Hypothesis H_job_cost_positive: job_cost_positive job_cost j.

      (* Recall the list of jobs that arrive in any interval. *)
      Let arrivals_between := jobs_arrived_between arr_seq.
      Let quiet_time t1 := quiet_time j t1.
      Let busy_interval_prefix t1 t2 := busy_interval_prefix j t1 t2.
      Let busy_interval t1 t2 := busy_interval j t1 t2.
      Let is_priority_inversion_bounded_by K := priority_inversion_of_job_is_bounded_by j K.
      
      (* We begin by proving a basic lemma about completion of the job within its busy interval. *)
      Section BasicLemma.

        (* Assume that the priority relation is reflexive. *)
        Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
        
        (* Consider any busy interval [t1, t2) of job j. *)
        Variable t1 t2: time.
        Hypothesis H_busy_interval: busy_interval t1 t2.
        
        (* We prove that job j completes by the end of the busy interval. *)
        Lemma job_completes_within_busy_interval: 
          job_completed_by j t2.
        Proof.
          rename H_priority_is_reflexive into REFL, H_busy_interval into BUSY.
          move: BUSY => [[_ [_ [_ /andP [_ ARR]]]] QUIET].
            by apply QUIET.
        Qed.

      End BasicLemma.
      
      (* In this section, we prove that during a busy interval there
         always exists a pending job. *)
      Section ExistsPendingJob.

        (* Assume that jobs do not execute after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.

        (* Let [t1, t2] be any interval where time t1 is quiet and time t2 is not quiet. *)
        Variable t1 t2: time.
        Hypothesis H_interval: t1 <= t2.
        Hypothesis H_quiet: quiet_time t1.
        Hypothesis H_not_quiet: ~ quiet_time t2.
        
      (* Then, we prove that there is a job pending at time t2
         that has higher or equal priority (with respect of tsk). *)
        Lemma not_quiet_implies_exists_pending_job:
          exists j_hp,
            arrives_in arr_seq j_hp /\
            arrived_between job_arrival j_hp t1 t2 /\
            higher_eq_priority j_hp j /\
            ~ job_completed_by j_hp t2. 
        Proof.
          rename H_quiet into QUIET, H_not_quiet into NOTQUIET.
          destruct (has (fun j_hp => (~~ job_completed_by j_hp t2) && higher_eq_priority j_hp j)
                        (arrivals_between t1 t2)) eqn:COMP.
          {
            move: COMP => /hasP [j_hp ARR /andP [NOTCOMP HP]].
            move: (ARR) => INarr.
            apply in_arrivals_implies_arrived_between with (job_arrival0 := job_arrival) in ARR;
              last by done.
            apply in_arrivals_implies_arrived in INarr.
            by exists j_hp; repeat split; last by apply/negP.
          }
          {
            apply negbT in COMP; rewrite -all_predC in COMP.
            move: COMP => /allP COMP.
            exfalso; apply NOTQUIET; intros j_hp IN HP ARR.
            destruct (ltnP (job_arrival j_hp) t1) as [BEFORE | AFTER];
              first by specialize (QUIET j_hp IN HP BEFORE); apply completion_monotonic with (t := t1).
            feed (COMP j_hp).
              by eapply arrived_between_implies_in_arrivals; eauto 1; apply/andP; split.
            by rewrite /= HP andbT negbK in COMP.
          }
        Qed.

      End ExistsPendingJob.
      
      (* In this section, we prove that during a busy interval the
         processor is never idle. *)
      Section ProcessorAlwaysBusy.

        (* Assume that the schedule is work-conserving and that jobs do
           not execute before their arrival nor after completion. *)
        Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
        Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
        Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.

        (* Next, we assume that the priority relation is reflexive and transitive. *)
        Hypothesis H_priority_is_reflexive: JLFP_is_reflexive higher_eq_priority.
        Hypothesis H_priority_is_transitive: JLFP_is_transitive higher_eq_priority.
      
        (* Consider any busy interval prefix [t1, t2). *)
        Variable t1 t2: time.
        Hypothesis H_busy_interval_prefix: busy_interval_prefix t1 t2.

        (* We prove that if the processot is idle at a time instant t, then 
           the next time instant [t+1] will be a quiet time. *)
        Lemma idle_time_implies_quiet_time_at_the_next_time_instant:
          forall t,
            is_idle sched t ->
            quiet_time t.+1.
        Proof.
          intros t IDLE jhp ARR HP AB.
          apply negbNE; apply/negP; intros NCOMP.
          rewrite /arrived_before ltnS in AB.
          move:(H_work_conserving _ t ARR) => WC.
          feed WC.
          { apply/andP; split; first (apply/andP; split).
            - by done.
            - apply/negP; intros COMP.
              move: NCOMP => /negP NCOMP; apply: NCOMP.
                by apply completion_monotonic with t.
            - move: IDLE => /eqP IDLE.
                by rewrite /scheduled_at IDLE.
          }
          move: IDLE WC => /eqP IDLE [jo /eqP SCHED].
            by rewrite IDLE in SCHED.
        Qed.

        (* Next, we prove that at any time instant t within the busy interval there exists a job 
           jhp such that (1) job jhp is pending at time t and (2) job jhp has higher-or-equal
           priority than task tsk. *)
         Lemma pending_hp_job_exists:
          forall t,
            t1 <= t < t2 ->
            exists jhp,
              arrives_in arr_seq jhp /\
              job_pending_at jhp t /\
              higher_eq_priority jhp j.
        Proof.
          move => t /andP [GE LT].
          move: (ltngtP t1.+1 t2) => [GT|CONTR|EQ].
          { move: (H_busy_interval_prefix) => [_ [QT [NQT _]]].
            have EX:
              exists (hps: seq Job),
                forall jhp,
                  jhp \in hps <-> arrives_in arr_seq jhp /\ job_pending_at jhp t
                                  /\ higher_eq_priority jhp j.
            { exists (filter
                        (fun jo => (job_pending_at jo t) && (higher_eq_priority jo j))
                        (jobs_arrived_between arr_seq 0 t.+1)).
              intros; split; intros.
              { move: H; rewrite mem_filter; move => /andP [/andP [PEN HP] IN].
                repeat split; try done.
                  by eapply in_arrivals_implies_arrived; eauto 2.
              }
              { move: H => [ARR [PEN HP]].
                rewrite mem_filter.
                apply/andP; split; first (apply/andP; split); try done.
                apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival); try done.
                apply/andP; split; first by done.
                rewrite ltnS.
                  by move: PEN => /andP [T _].
              }
            }
            move: EX => [hps SE].
            case FL: (hps) => [ | jhp jhps].
            { subst hps.
              exfalso.
              move: GE; rewrite leq_eqVlt; move => /orP [/eqP EQ| GE].
              { subst t.
                apply NQT with t1.+1; first by apply/andP; split.
                intros jhp ARR HP ARRB.
                apply negbNE; apply/negP; intros NCOMP.
                move: (SE jhp) => [_ SE2].
                feed SE2. repeat split; try done; first apply/andP; split; try done.
                apply/negP; intros COMLP.
                move: NCOMP => /negP NCOMP; apply: NCOMP.
                  by apply completion_monotonic with t1.
                    by done.
              }
              { apply NQT with t; first by apply/andP; split.
                intros jhp ARR HP ARRB.
                apply negbNE; apply/negP; intros NCOMP.
                move: (SE jhp) => [_ SE2].
                feed SE2. repeat split; try done.
                - by apply/andP; split; first apply ltnW.
                    by done.
              }
            } 
            { exists jhp.
              specialize (SE jhp).
              move: SE => [SE1 _].
              feed SE1; first by rewrite FL in_cons; apply/orP; left.
                by done.
            }
          }
          { exfalso.
            rewrite ltnS in CONTR.
            move: (leq_ltn_trans GE LT) => NEQ.
              by move: CONTR; rewrite leqNgt; move => /negP CONTR; apply: CONTR.
          } 
          { subst t2; rewrite ltnS in LT.
            have EQ: t1 = t; first by apply/eqP; rewrite eqn_leq; apply/andP; split.
            subst t1; clear GE LT.
            move: (H_busy_interval_prefix) => [_ [QTt [_ REL]]].
            exists j; repeat split.
            - by done. 
            - move: REL; rewrite ltnS -eqn_leq eq_sym; move => /eqP REL.
              rewrite -REL.
                by eapply UniprocessorSchedule.job_pending_at_arrival; eauto 2.
            - by apply H_priority_is_reflexive.
          }
        Qed.
        
        (* We prove that at any time instant t within [t1, t2) the processor is not idle. *)
        Lemma not_quiet_implies_not_idle:
          forall t,
            t1 <= t < t2 ->
            ~ is_idle sched t.
        Proof.
          intros t NEQ IDLE.
          move: (pending_hp_job_exists _ NEQ) => [jhp [ARR [PEND HP]]].
          unfold work_conserving, platform.Platform.work_conserving in *.
          feed (H_work_conserving _ t ARR).
          apply/andP; split; first by done.
          move: IDLE => /eqP IDLE. unfold scheduled_at. rewrite IDLE. by done.
          move: (H_work_conserving) => [jo SCHED].
          move: IDLE SCHED => /eqP IDLE /eqP SCHED.
            by rewrite SCHED in IDLE.
        Qed.
        
      End ProcessorAlwaysBusy.

      (* In this section, we show that the length of any busy interval
         is bounded, as long as there is enough supply to accomodate
         the workload of tasks with higher or equal priority. *)
      Section BoundingBusyInterval.

        (* Assume that there are no duplicate job arrivals... *)
        Hypothesis H_arrival_sequence_is_a_set:
          arrival_sequence_is_a_set arr_seq.
        
        (* ...and that jobs do not execute before their arrival nor after completion. *)
        Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
        Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

        (* Also assume a work-conserving JLFP schedule, ... *)
        Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

        (* ...in which the priority relation is reflexive and transitive. *)
        Hypothesis H_priority_is_reflexive: JLFP_is_reflexive higher_eq_priority.
        Hypothesis H_priority_is_transitive: JLFP_is_transitive higher_eq_priority.


        (* Next, we recall the notion of workload of all jobs released in a given interval
           [t1, t2) that have higher-or-equal priority w.r.t the job j being analyzed. *)
        Let hp_workload t1 t2 :=
          workload_of_higher_or_equal_priority_jobs
            job_cost (arrivals_between t1 t2) higher_eq_priority j.
          
        (* With regard to the jobs with higher-or-equal priority that are released
           in a given interval [t1, t2), we also recall the service received by these
           jobs in the same interval [t1, t2). *)
        Let hp_service t1 t2 :=
          service_of_higher_or_equal_priority_jobs
            sched (arrivals_between t1 t2) higher_eq_priority j t1 t2.

        (* Now we begin the proof. First, we show that the busy interval is bounded. *)
        Section BoundingBusyInterval.

          (* Suppose that job j is pending at time t_busy. *)
          Variable t_busy: time.
          Hypothesis H_j_is_pending: job_pending_at j t_busy.
          
          (* First, we show that there must exist a busy interval prefix. *)
          Section LowerBound.

            (* Since job j is pending, there is a (potentially unbounded)
               busy interval that starts no later than with the arrival of j. *)
            Lemma exists_busy_interval_prefix:
              exists t1,
                busy_interval_prefix t1 t_busy.+1 /\
                t1 <= job_arrival j <= t_busy.
            Proof. 
              move: (H_from_arrival_sequence) => FROM.
              rename H_j_is_pending into PEND,
              H_work_conserving into WORK, H_priority_is_reflexive into REFL.
              unfold busy_interval_prefix.
              set dec_quiet :=
                fun t => all (fun j_hp =>
                                higher_eq_priority j_hp j ==> (completed_by job_cost sched j_hp t))
                           (jobs_arrived_before arr_seq t). 
              destruct ([exists t:'I_t_busy.+1, dec_quiet t]) eqn:EX.
              {  
                set last := \max_(t < t_busy.+1 | dec_quiet t) t.
                move: EX => /existsP [t EX].
                have PRED: dec_quiet last by apply (bigmax_pred t_busy.+1 dec_quiet t).
                have QUIET: quiet_time last.
                {
                  move: PRED => /allP PRED.
                  intros j_hp IN HP ARR.
                  feed (PRED j_hp).
                    by apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival).
                      by rewrite HP implyTb in PRED.
                } 
                exists last.
                have JAIN: last <= job_arrival j <= t_busy.
                {
                  apply/andP; split; last by move: PEND => /andP [ARR _].
                  apply contraT; rewrite -ltnNge; intros BEFORE.
                  feed (QUIET j FROM); first by apply REFL.
                  specialize (QUIET BEFORE).
                  move: PEND => /andP [_ NOTCOMP].
                  apply completion_monotonic with (t' := t_busy) in QUIET;
                    [by rewrite QUIET in NOTCOMP | by done |].
                  by apply bigmax_ltn_ord with (i0 := t).
                }
                split; last by done.
                repeat split.
                - by apply bigmax_ltn_ord with (i0 := t).
                - by done.
                - 
                  move => t0 /andP [GTlast LTbusy] QUIET0.
                  have PRED0: dec_quiet t0.
                  {
                    apply/allP; intros j_hp ARR; apply/implyP; intros HP.
                    apply QUIET0.
                    - by eapply in_arrivals_implies_arrived; eauto.
                    - by done. 
                    - by eapply in_arrivals_implies_arrived_before; eauto.
                  } 
                  have BUG: t0 <= last.
                  {
                    have LE := @leq_bigmax_cond _ (fun (x: 'I_t_busy.+1) => dec_quiet x)
                                                (fun x => x) (Ordinal LTbusy) PRED0.
                    by apply LE.
                  }
                  apply leq_trans with (p := last) in GTlast; last by done.
                  by rewrite ltnn in GTlast.
                - by rewrite ltnS.
              }
              {
                apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL.
                exists 0; split;
                last by apply/andP; split; last by move: PEND => /andP [ARR _].
                split.  by done.
                split; first by intros j_hp _ _ ARR; rewrite /arrived_before ltn0 in ARR.
                split.
                move => t /andP [GE LT].
                specialize (ALL (Ordinal LT)); move: ALL => /negP ALL.
                intros QUIET; apply ALL; simpl.
                apply/allP; intros j_hp ARR; apply/implyP; intros HP.
                apply QUIET.
                - by eapply in_arrivals_implies_arrived; eauto.
                - by done. 
                - by eapply in_arrivals_implies_arrived_before; eauto.
                apply/andP; split; first by done.
                  by move: PEND => /andP [ARR _].
              }
            Qed.             

          End LowerBound.
           
          (* Next we prove that, if there is a point where the requested workload
             is upper-bounded by the supply, then the busy interval eventually ends. *)
          Section UpperBound.

            (* Consider any busy interval prefix of job j. *)
            Variable t1: time.
            Hypothesis H_is_busy_prefix: busy_interval_prefix t1 t_busy.+1.
            
            (* Let priority_inversion_bound be a constant which bounds
             length of a priority inversion. *)
            Variable priority_inversion_bound: time.
            Hypothesis H_priority_inversion_is_bounded:
              is_priority_inversion_bounded_by priority_inversion_bound.
            
            (* Next, assume that for some positive delta, the sum of requested workload
               at time [t1 + delta] and constant priority_inversion_bound is bounded by 
               delta (i.e., the supply). *)
            Variable delta: time.
            Hypothesis H_delta_positive: delta > 0.
            Hypothesis H_workload_is_bounded:
              priority_inversion_bound + hp_workload t1 (t1 + delta) <= delta.

            (* If there is a quiet time by time (t1 + delta), it trivially follows that
               the busy interval is bounded.
               Thus, let's consider first the harder case where there is no quiet time,
               which turns out to be impossible. *)
            Section CannotBeBusyForSoLong.
             
              (* Assume that there is no quiet time in the interval (t1, t1 + delta]. *)
              Hypothesis H_no_quiet_time:
                forall t, t1 < t <= t1 + delta -> ~ quiet_time t.

              (* Since the interval is always non-quiet, the processor is always busy
                 with tasks of higher-or-equal priority or some lower priority job which was scheduled,
                 i.e., the sum of service done by jobs with actual arrival time in [t1, t1 + delta) 
                 and priority inversion equals delta. *)
              Lemma busy_interval_has_uninterrupted_service: 
                delta <= priority_inversion_bound + hp_service t1 (t1 + delta).
              Proof.
                clear H_workload_is_bounded.
                move: H_is_busy_prefix => [H_strictly_larger [H_quiet [_ EXj]]].
                                destruct (delta <= priority_inversion_bound) eqn:KLEΔ.
                { by apply leq_trans with priority_inversion_bound; last rewrite leq_addr. }
                apply negbT in KLEΔ; rewrite -ltnNge in KLEΔ.
                have Lemma1:
                  forall t delta P,
                    \sum_(j <- arrivals_between t (t + delta) | P j)
                     service_during sched j t (t + delta) <= delta.
                { clear KLEΔ H_no_quiet_time H_delta_positive delta.
                  intros.
                  have EQ: \sum_(t <= x < t + delta) 1 = delta.
                  { by rewrite big_const_nat iter_addn mul1n addn0 -{2}[t]addn0 subnDl subn0. }
                  rewrite -{3}EQ; clear EQ.
                  rewrite exchange_big //=.
                  rewrite leq_sum //.
                  move => t' _.
                  case SCHED: (sched t') => [j1 | ]; simpl.
                  { case ARR: (j1 \in arrivals_between t (t + delta)).
                    { rewrite (big_rem j1) //=; simpl.
                      rewrite /service_at /scheduled_at SCHED; simpl.
                      rewrite -[1]addn0 leq_add //.
                      - case (P j1); last by done.
                          by case (Some j1 == Some j1).
                      - rewrite leqn0 big1_seq; first by done.
                        move => j2 /andP [_ ARRj2].
                        apply/eqP; rewrite eqb0.
                        apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                        inversion CONTR; subst j2; clear CONTR.
                        rewrite rem_filter in ARRj2; last first.
                        eapply arrivals_uniq; eauto 2.
                        move: ARRj2; rewrite mem_filter; move => /andP [/negP CONTR _].
                          by apply: CONTR. }
                    { apply leq_trans with 0; last by done.
                      rewrite leqn0 big1_seq; first by done.
                      move => j2 /andP [_ ARRj2].
                      apply/eqP; rewrite eqb0.
                      rewrite /scheduled_at SCHED.
                      apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                      inversion CONTR; clear CONTR.
                        by subst j2; rewrite ARR in ARRj2.
                    }
                  }                    
                  { apply leq_trans with 0; last by done.
                    rewrite leqn0 big1_seq; first by done.
                    move => j2 /andP [_ ARRj2].
                      by rewrite /service_at /scheduled_at SCHED.
                  }
                }
                have AbsLemma1:
                  forall P F rs,
                    \sum_(r <- rs | P r) F r =
                    \sum_(r <- rs) F r - \sum_(r <- rs | ~~ P r) F r.
                { clear.
                  intros.
                  induction rs; first by rewrite !big_nil subn0.
                  rewrite !big_cons !IHrs; clear IHrs.
                  case (P a); simpl; last by rewrite subnDl.
                  rewrite addnBA; first by done.
                  rewrite big_mkcond leq_sum //.
                  intros t _.
                    by case (P t).
                }
                apply leq_trans with (
                  cumulative_priority_inversion j t1 (t1 + delta) + hp_service t1 (t1 + delta)); last first.
                {
                  rewrite leq_add2r.
                  destruct (t1 + delta <= t_busy.+1) eqn:NEQ.
                  {
                    apply H_priority_inversion_is_bounded in H_is_busy_prefix.
                    apply leq_trans with (cumulative_priority_inversion j t1 t_busy.+1); last by done.
                    unfold cumulative_priority_inversion.
                    rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + delta)) //=.
                    rewrite leq_addr //.
                    by rewrite leq_addr.
                  }
                  {
                    apply H_priority_inversion_is_bounded.
                    apply negbT in NEQ. rewrite -ltnNge in NEQ.
                    repeat split; try done.
                    - by rewrite -addn1 leq_add2l.
                    - move => t' /andP [LT GT]; apply H_no_quiet_time.
                        by apply/andP; split; [ | rewrite ltnW ].
                    - move: EXj => /andP [T1 T2].
                      apply/andP; split; first by done.
                        by apply ltn_trans with (t_busy.+1).
                  }
                }
                unfold hp_service, service_of_higher_or_equal_priority_jobs, service_of_jobs.
                have EQ:
                    \sum_(j0 <- arrivals_between t1 (t1 + delta) | higher_eq_priority j0 j)
                     service_during sched j0 t1 (t1 + delta)  =
                    \sum_(j0 <- arrivals_between 0 (t1 + delta) | higher_eq_priority j0 j)
                     service_during sched j0 t1 (t1 + delta).
                {
                  rewrite /arrivals_between.
                  rewrite [in X in _ = X](job_arrived_between_cat _ _ t1); [ | | rewrite leq_addr]; try done.
                  rewrite big_cat //=.
                  rewrite -{1}[\sum_(j0 <- jobs_arrived_between _ _  (t1 + delta) | _)
                             service_during sched j0 t1 (t1 + delta)]add0n.
                  apply/eqP. rewrite eqn_add2r eq_sym exchange_big //=.
                  rewrite big1_seq //.
                  move => t /andP [_ NEQ]; rewrite mem_iota in NEQ.
                  rewrite big1_seq //.
                  move => jhp /andP [HP ARR].
                  apply/eqP; rewrite eqb0.
                  apply completed_implies_not_scheduled with job_cost; first by done.
                  apply completion_monotonic with t1; [ | move: NEQ => /andP [T1 _] | ]; try done.
                  apply H_quiet; try done.
                  - eapply in_arrivals_implies_arrived; eauto 2.
                  - eapply in_arrivals_implies_arrived_before; eauto 2.
                }
                rewrite EQ; clear EQ.
                rewrite AbsLemma1. 
                rewrite addnBA; last first.
                { rewrite big_mkcond //= leq_sum //.
                    by intros j' _; case (higher_eq_priority j' j). }
                rewrite addnC.
                rewrite -addnBA; last first.
                rewrite exchange_big //=.
                unfold cumulative_priority_inversion.
                unfold is_priority_inversion.
                apply leq_sum_seq.
                move => t II _.
                rewrite mem_index_iota in II; move: II => /andP [GEi LEt].
                rewrite big_mkcond //=. 
                case SCHED: (sched t) => [j1 | ]; simpl.
                { case PRIO1: (higher_eq_priority j1 j); simpl.
                  { rewrite leqn0 big1_seq; first by done.
                    move => j2 /andP [_ ARRj2].
                    case PRIO2: (higher_eq_priority j2 j); simpl; first by done.
                    rewrite /service_at /scheduled_at SCHED.
                    case EQ: (j1 == j2).
                    { move: EQ => /eqP EQ; subst j2.
                        by rewrite PRIO1 in PRIO2. }
                    { apply/eqP; rewrite eqb0.
                      apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                      inversion CONTR; clear CONTR.
                        by subst j2; rewrite PRIO1 in PRIO2. } }
                  { case ARR: (j1 \in arrivals_between 0 (t1 + delta)).
                    { rewrite (big_rem j1) //= PRIO1; simpl.
                      rewrite /service_at /scheduled_at SCHED; simpl.
                      rewrite -[1]addn0 leq_add //.
                      - by case (Some j1 == Some j1). 
                      - rewrite leqn0 big1_seq; first by done.
                        move => j2 /andP [_ ARRj2].
                        case (higher_eq_priority j2 j); simpl; first by done.
                        apply/eqP; rewrite eqb0.
                        apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                        inversion CONTR; subst j2; clear CONTR.
                        rewrite rem_filter in ARRj2; last first.
                        eapply arrivals_uniq; eauto 2.
                        move: ARRj2; rewrite mem_filter; move => /andP [/negP CONTR _].
                          by apply: CONTR. }
                    { apply leq_trans with 0; last by done.
                      rewrite leqn0 big1_seq; first by done.
                      move => j2 /andP [_ ARRj2].
                      case (higher_eq_priority j2 j); simpl; first by done.
                      apply/eqP; rewrite eqb0.
                      rewrite /scheduled_at SCHED.
                      apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                      inversion CONTR; clear CONTR.
                        by subst j2; rewrite ARR in ARRj2. } } } 
                { simpl.
                  rewrite leqn0 big1_seq; first by done.
                  move => j1 /andP [_ ARRj1].
                  rewrite /service_at /scheduled_at SCHED.
                    by case (higher_eq_priority j1 j). }
                have EQ:
                  \sum_(r <- arrivals_between 0 (t1 + delta))
                   service_during sched r t1 (t1 + delta) = delta.
                {
                  have EQ: \sum_(t1 <= x < t1 + delta) 1 = delta.
                  { by rewrite big_const_nat iter_addn mul1n addn0 -{2}[t1]addn0 subnDl subn0. }
                  rewrite -{3}EQ exchange_big //=. clear EQ.
                  apply/eqP; rewrite eqn_leq; apply/andP; split.
                  { rewrite leq_sum //.
                    move => t' _.
                    case SCHED: (sched t') => [j1 | ]; simpl.
                    { case ARR: (j1 \in arrivals_between 0 (t1 + delta)).
                      { rewrite (big_rem j1) //=; simpl.
                        rewrite /service_at /scheduled_at SCHED; simpl.
                        rewrite -[1]addn0 leq_add //.
                        - by case (Some j1 == Some j1).
                        - rewrite leqn0 big1_seq; first by done.
                          move => j2 /andP [_ ARRj2].
                          apply/eqP; rewrite eqb0.
                          apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                          inversion CONTR; subst j2; clear CONTR.
                          rewrite rem_filter in ARRj2; last first.
                          eapply arrivals_uniq; eauto 2.
                          move: ARRj2; rewrite mem_filter; move => /andP [/negP CONTR _].
                            by apply: CONTR. }
                      { apply leq_trans with 0; last by done.
                        rewrite leqn0 big1_seq; first by done.
                        move => j2 /andP [_ ARRj2].
                        apply/eqP; rewrite eqb0.
                        rewrite /scheduled_at SCHED.
                        apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                        inversion CONTR; clear CONTR.
                          by subst j2; rewrite ARR in ARRj2. } }                    
                    { apply leq_trans with 0; last by done.
                      rewrite leqn0 big1_seq; first by done.
                      move => j2 /andP [_ ARRj2].
                        by rewrite /service_at /scheduled_at SCHED. }
                  }                    
                  { rewrite [in X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond //=.
                    rewrite leq_sum //.
                    move => t' /andP [/andP [LT GT] _].
                    apply/sum_seq_gt0P.
                    case SCHED: (sched t') => [j1 | ]; last first.
                    { exfalso.
                      move: LT; rewrite leq_eqVlt; move => /orP [/eqP EQ|LT].
                      { subst t'.
                        feed (H_no_quiet_time t1.+1); first by apply/andP; split.
                        move: SCHED => /eqP SCHED.
                        apply: H_no_quiet_time.
                          by apply idle_time_implies_quiet_time_at_the_next_time_instant.
                      }
                      {
                        feed (H_no_quiet_time t') .  by apply/andP; split; last rewrite ltnW.
                        apply: H_no_quiet_time.
                        intros j_hp IN HP ARR.
                        apply contraT; intros NOTCOMP.
                        destruct (scheduled_at sched j_hp t') eqn:SCHEDhp;
                          first by move: SCHEDhp => /eqP SCHEDhp; rewrite SCHED in SCHEDhp.
                        apply negbT in SCHEDhp.
                        feed (H_work_conserving j_hp t' IN);
                          first by repeat (apply/andP; split); first by apply ltnW.
                        move: H_work_conserving => [j_other /eqP SCHEDother].
                          by rewrite SCHED in SCHEDother.
                      }              
                    }
                    { exists j1; split.
                      - unfold arrivals_between.
                        apply arrived_between_implies_in_arrivals with job_arrival; try done.
                        unfold jobs_come_from_arrival_sequence in *.
                        apply H_jobs_come_from_arrival_sequence with t'.
                        unfold scheduled_at . rewrite SCHED. by done.
                        unfold arrived_between; apply/andP; split; first by done.
                        unfold jobs_must_arrive_to_execute in *.
                        move: SCHED => /eqP SCHED.
                        apply H_jobs_must_arrive_to_execute in SCHED.
                        unfold has_arrived in SCHED.
                          by apply leq_ltn_trans with t'.
                      -
                          by rewrite /service_at /scheduled_at SCHED lt0b. }
                  } 
                } 
                rewrite EQ; clear EQ.
                  by rewrite leq_addr.
              Qed.

              (* Moreover, the fact that the interval is not quiet also implies
                 that there's more workload requested than service received. *)
              Lemma busy_interval_too_much_workload:
                hp_workload t1 (t1 + delta) > hp_service t1 (t1 + delta).
              Proof.
                have PEND := not_quiet_implies_exists_pending_job 
                               H_completed_jobs_dont_execute.
                rename H_no_quiet_time into NOTQUIET, 
                H_is_busy_prefix into PREFIX.
                set l := jobs_arrived_between arr_seq t1 (t1 + delta).
                set hep := higher_eq_priority.
                unfold hp_service, service_of_higher_or_equal_priority_jobs, service_of_jobs,
                hp_workload, workload_of_higher_or_equal_priority_jobs, workload_of_jobs.
                fold arrivals_between l hep.
                move: (PREFIX) => [_ [QUIET _]].
                move: (NOTQUIET) => NOTQUIET'.
                feed (NOTQUIET' (t1 + delta)).
                { by apply/andP; split; first
                    by rewrite -addn1 leq_add2l.
                }
                feed (PEND t1 (t1 + delta)); first by apply leq_addr.
                specialize (PEND QUIET NOTQUIET').
                move: PEND => [j0 [ARR0 [/andP [GE0 LT0] [HP0 NOTCOMP0]]]].
                have IN0: j0 \in l.
                { by eapply arrived_between_implies_in_arrivals; eauto 1; apply/andP; split. }
                have UNIQ: uniq l by eapply arrivals_uniq; eauto 1.
                rewrite big_mkcond [\sum_(_ <- _ | _ _ _)_]big_mkcond //=.
                rewrite (bigD1_seq j0); [simpl | by done | by done].
                rewrite (bigD1_seq j0); [simpl | by done | by done].
                rewrite /hep HP0.
                rewrite -add1n addnA [1 + _]addnC addn1.
                apply leq_add; last first.
                {
                  apply leq_sum; intros j1 NEQ.
                  destruct (higher_eq_priority j1 j); last by done.
                    by apply cumulative_service_le_job_cost. 
                }
                rewrite ltn_neqAle; apply/andP; split; last by apply cumulative_service_le_job_cost.
                unfold service_during.
                rewrite (ignore_service_before_arrival job_arrival); rewrite //; [| by apply ltnW].
                rewrite <- ignore_service_before_arrival with (t2:=0); rewrite //; [|by apply ltnW].
                  by apply/negP.
              Qed.               
              
              (* Using the two lemmas above, we infer that the workload is larger than the
                 interval length. However, this contradicts the assumption H_workload_is_bounded. *)
              Corollary busy_interval_workload_larger_than_interval:
                priority_inversion_bound + hp_workload t1 (t1 + delta)  > delta.
              Proof.
                apply leq_ltn_trans with (priority_inversion_bound + hp_service t1 (t1 + delta)).
                apply busy_interval_has_uninterrupted_service.
                rewrite ltn_add2l.
                apply busy_interval_too_much_workload.
              Qed.
              
            End CannotBeBusyForSoLong.  
            
            (* Since the interval cannot remain busy for so long, we prove that
               the busy interval finishes at some point t2 <= t1 + delta. *)
            Lemma busy_interval_is_bounded:
              exists t2,
                t2 <= t1 + delta /\
                busy_interval t1 t2.
            Proof. 
              have TOOMUCH := busy_interval_workload_larger_than_interval. 
              have BOUNDED := H_workload_is_bounded.
              rename H_is_busy_prefix into PREFIX.              
              set dec_quiet :=
                fun t =>
                  all (fun j_hp => higher_eq_priority j_hp j ==> (completed_by job_cost sched j_hp t))
                      (jobs_arrived_before arr_seq t).
              destruct ([exists t2:'I_(t1 + delta).+1, (t2 > t1) && dec_quiet t2]) eqn:EX.
              {
                have EX': exists (t2: nat), ((t1 < t2 <= t1 + delta) && dec_quiet t2).
                {
                  move: EX => /existsP [t2 /andP [LE QUIET]].
                  exists t2; apply/andP; split; last by done.
                    by apply/andP; split; last by rewrite -ltnS; apply ltn_ord.
                }
                have MIN := ex_minnP EX'.
                move: MIN => [t2 /andP [/andP [GT LE] QUIET] MIN]; clear EX EX'.
                exists t2; split; first by done.
                split; last first.
                { 
                  intros j_hp IN HP ARR.
                  move: QUIET => /allP QUIET.
                  feed (QUIET j_hp);
                    first by eapply arrived_between_implies_in_arrivals; last by apply ARR.
                    by move: QUIET => /implyP QUIET; apply QUIET.
                }
                split; first by done.
                split; first by move: PREFIX => [_ [QUIET1 _]].
                split.
                move => t /andP [GT1 LT2] BUG.
                feed (MIN t). 
                {
                  apply/andP; split;
                  first by apply/andP; split;
                  last by apply leq_trans with (n := t2); [by apply ltnW |].
                  apply/allP; intros j_hp ARR; apply/implyP; intro HP.
                  apply BUG. 
                  - by eapply in_arrivals_implies_arrived, ARR.
                  - by done. 
                  - by eapply in_arrivals_implies_arrived_before, ARR.
                }
                  by apply leq_ltn_trans with (p := t2) in MIN; first by rewrite ltnn in MIN.
                {
                  move: PREFIX => [LT [QT [NQ IN]]].
                  have NEQ: t_busy < t2.
                  {
                    rewrite ltnNge; apply/negP; intros CONTR.
                    feed (NQ t2); first by apply/andP; split; last rewrite ltnS.
                    apply NQ.
                    unfold dec_quiet in *.
                    intros jhp ARR HP AB. 
                    move: QUIET => /allP QUIET.
                    feed (QUIET jhp).
                    eapply arrived_between_implies_in_arrivals; eauto 2.
                      by move: QUIET => /implyP QUIET; apply QUIET.
                  }
                  move: IN => /andP [IN1 IN2].
                  apply/andP; split; first by done.
                  apply leq_ltn_trans with t_busy.
                  rewrite -ltnS; by done.
                  by done.                  
                }
              } 
              {                
                apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL'.
                have ALL: forall t, t1 < t <= t1 + delta -> ~ quiet_time t.
                {
                  move => t /andP [GTt LEt] QUIET.
                  rewrite -ltnS in LEt.
                  specialize (ALL' (Ordinal LEt)); rewrite negb_and /= GTt orFb in ALL'. 
                  move: ALL' => /negP ALL'; apply ALL'; clear ALL'.
                  apply/allP; intros j_hp ARR; apply/implyP; intro HP.
                  apply QUIET.
                  - by eapply in_arrivals_implies_arrived, ARR.
                  - by done. 
                  - by eapply in_arrivals_implies_arrived_before, ARR.
                } exfalso; clear ALL'.
                specialize (TOOMUCH ALL).
                  by have BUG := leq_trans TOOMUCH BOUNDED;
                      rewrite ltnn in BUG.
              }
            Qed.
            
          End UpperBound.

        End BoundingBusyInterval.

        
        (* In this section, we show that from a workload bound we can infer
           the existence of a busy interval. *)
        Section BusyIntervalFromWorkloadBound.

          (* Let priority_inversion_bound be a constant that bounds the length of a priority inversion. *)
          Variable priority_inversion_bound: time.
          Hypothesis H_priority_inversion_is_bounded:
            is_priority_inversion_bounded_by priority_inversion_bound.

          (* Assume that for some positive delta, the sum of requested workload at
             time (t1 + delta) and priority inversion is bounded by delta (i.e., the supply). *)
          Variable delta: time.
          Hypothesis H_delta_positive: delta > 0.
          Hypothesis H_workload_is_bounded:
            forall t, priority_inversion_bound + hp_workload t (t + delta) <= delta.

          (* Next, we assume that job j has positive cost, from which we can
             infer that there is a time in which j is pending. *)
          Hypothesis H_positive_cost: job_cost j > 0.

          (* Therefore there must exists a busy interval [t1, t2) that
             contains the arrival time of j. *)
          Corollary exists_busy_interval:
            exists t1 t2, 
              t1 <= job_arrival j < t2 /\
              t2 <= t1 + delta /\
              busy_interval t1 t2.
          Proof. 
            have PREFIX := exists_busy_interval_prefix.
            move: (H_workload_is_bounded) => WORK.
            feed (PREFIX (job_arrival j)).
            {
              apply/andP; split; first by apply leqnn.
              rewrite /completed_by /service /service_during.
              rewrite (ignore_service_before_arrival job_arrival) //.
              rewrite big_geq; last by apply leqnn.
              by rewrite eq_sym -lt0n H_positive_cost.
            }
            move: PREFIX => [t1 [PREFIX /andP [GE1 GEarr]]].
            have BOUNDED := busy_interval_is_bounded
                              (job_arrival j) t1 _ priority_inversion_bound _ delta .            
            feed_n 4 BOUNDED; try done. 
            move: BOUNDED => [t2 [GE2 BUSY]].
            exists t1, t2; split.
            {
              apply/andP; split; first by done.
              apply contraT; rewrite -leqNgt; intro BUG.
              move: BUSY PREFIX => [[LE12 _] QUIET] [_ [_ [NOTQUIET _]]].
              feed (NOTQUIET t2); first by apply/andP; split.
              by exfalso; apply NOTQUIET.
            }
              by split. 
          Qed.
          
        End BusyIntervalFromWorkloadBound.
       
      End BoundingBusyInterval.

    End Lemmas.
    
  End Definitions. 
    
End BusyIntervalJLFP.
     