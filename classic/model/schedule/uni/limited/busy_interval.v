Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task
               prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.priority
               prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.limited.platform.definitions.

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
    Let arrivals_between := jobs_arrived_between arr_seq.

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
         the sense of the definition given in prosa.classic.model.schedule.uni.basic.platform. Therefore, it 
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

    (* In this section we define the computational
       version of the notion of quiet time. *)
    Section DecidableQuietTime.

      (* We say that t is a quiet time for j iff every higher-priority job from
         the arrival sequence that arrived before t has completed by that time. *)
      Definition quiet_time_dec (j : Job) (t : time) :=
        all
          (fun j_hp => higher_eq_priority j_hp j ==> (completed_by job_cost sched j_hp t))
          (jobs_arrived_before arr_seq t).

      (* We also show that the computational and propositional definitions are equivalent. *)
      Lemma quiet_time_P :
        forall j t, reflect (quiet_time j t) (quiet_time_dec j t).
      Proof.
        intros; apply/introP.
        { intros QT s ARRs HPs BEFs.
          move: QT => /allP QT.
          specialize (QT s); feed QT.
          eapply arrived_between_implies_in_arrivals; eauto 2.
            by move: QT => /implyP Q; apply Q in HPs.
        }
        { move => /negP DEC; intros QT; apply: DEC.
          apply/allP; intros s ARRs.
          apply/implyP; intros HPs.
          apply QT; try done.
          - by apply in_arrivals_implies_arrived in ARRs.
          - eapply in_arrivals_implies_arrived_between in ARRs; eauto 2.
              by move: ARRs => /andP [_ HP]. 
        }
      Qed.

    End DecidableQuietTime.
  
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

      (* In section we prove a few auxiliary lemmas about quiet time and service.  *)
      Section QuietTimeAndServiceOfJobs.

        (* Assume that there are no duplicate job arrivals... *)
        Hypothesis H_arrival_sequence_is_a_set:
          arrival_sequence_is_a_set arr_seq.
        
        (* ...and that jobs do not execute before their arrival nor after completion. *)
        Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
        Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

        (* We also assume that the schedule is work-conserving. *)
        Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

        (* Let t1 be a quiet time. *)
        Variable t1: time.
        Hypothesis H_quiet_time: quiet_time t1.
                
        (* Assume that there is no quiet time in the interval (t1, t1 + Δ]. *)
        Variable Δ: time.
        Hypothesis H_no_quiet_time: forall t, t1 < t <= t1 + Δ -> ~ quiet_time t.

        (* For clarity, we introduce a notion of the total service of jobs released in 
           time interval [t_beg, t_end) during the time interval [t1, t1 + Δ). *)
        Let service_received_by_hep_jobs_released_during t_beg t_end :=
          service_of_higher_or_equal_priority_jobs
            sched (arrivals_between t_beg t_end) higher_eq_priority j t1 (t1 + Δ).

        (* We prove that jobs with higher-than-or-equal priority that
           released before time instant t1 receive no service after 
           time instant t1. *)
        Lemma hep_jobs_receive_no_service_before_quiet_time:
            service_received_by_hep_jobs_released_during t1 (t1 + Δ) =
            service_received_by_hep_jobs_released_during 0 (t1 + Δ).
        Proof.
          intros.
          rewrite /service_received_by_hep_jobs_released_during
                  /service_of_higher_or_equal_priority_jobs
                  /service_of_jobs /arrivals_between.
          rewrite [in X in _ = X](job_arrived_between_cat _ _ t1);
            [ | | rewrite leq_addr]; try done.
          rewrite big_cat //=.
          rewrite -{1}[\sum_(j <- jobs_arrived_between _ _  (t1 + Δ) | _)
                        service_during sched j t1 (t1 + Δ)]add0n.
          apply/eqP. rewrite eqn_add2r eq_sym exchange_big //=.
          rewrite big1_seq //.
          move => t' /andP [_ NEQ]; rewrite mem_iota in NEQ.
          rewrite big1_seq //.
          move => jhp /andP [HP ARR].
          apply/eqP; rewrite eqb0.
          eapply completed_implies_not_scheduled with job_cost; first by done.
          apply completion_monotonic with t1; [ move: NEQ => /andP [T1 _] | ]; try done.
          apply H_quiet_time; try done.
          - by eapply in_arrivals_implies_arrived; eauto 2.
          - by eapply in_arrivals_implies_arrived_before; eauto 2.
        Qed. 

        (* Next we prove that the total service within a "non-quiet" 
           time interval [t1, t1 + Δ) is exactly Δ. *)
        Lemma no_idle_time_within_non_quiet_time_interval:
          service_of_jobs sched (arrivals_between 0 (t1 + Δ)) predT t1 (t1 + Δ) = Δ.
        Proof.
          intros; unfold service_of_jobs, service_of_higher_or_equal_priority_jobs.
          rewrite -{3}[Δ](sum_of_ones t1) exchange_big //=.
          apply/eqP; rewrite eqn_leq; apply/andP; split.
          { rewrite leq_sum //; move => t' _; eapply service_of_jobs_le_1; eauto. } 
          { rewrite [in X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond //=; rewrite leq_sum //.
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
              { feed (H_no_quiet_time t'); first by apply/andP; split; last rewrite ltnW.
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
              - apply arrived_between_implies_in_arrivals with job_arrival; try done.
                apply H_jobs_come_from_arrival_sequence with t'.
                rewrite /scheduled_at SCHED; by done.
                apply/andP; split; first by done.
                move: SCHED => /eqP SCHED; apply H_jobs_must_arrive_to_execute in SCHED.
                  by apply leq_ltn_trans with t'.
              - by rewrite /service_at /scheduled_at SCHED lt0b. }
          } 
        Qed. 

      End QuietTimeAndServiceOfJobs.

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
              destruct ([exists t:'I_t_busy.+1, quiet_time_dec j t]) eqn:EX.
              { set last := \max_(t < t_busy.+1 | quiet_time_dec j t) t.
                move: EX => /existsP [t EX].
                have PRED: quiet_time_dec j last by apply (bigmax_pred t_busy.+1 (quiet_time_dec j) t).
                have QUIET: quiet_time last.
                { move: PRED => /allP PRED.
                  intros j_hp IN HP ARR.
                  feed (PRED j_hp).
                  { by eapply arrived_between_implies_in_arrivals; eauto. } 
                    by rewrite HP implyTb in PRED.
                } 
                exists last.
                have JAIN: last <= job_arrival j <= t_busy.
                { apply/andP; split; last by move: PEND => /andP [ARR _].
                  apply contraT; rewrite -ltnNge; intros BEFORE.
                  feed (QUIET j FROM); first by apply REFL.
                  specialize (QUIET BEFORE).
                  move: PEND => /andP [_ NOTCOMP].
                  apply completion_monotonic with (t' := t_busy) in QUIET;
                    [by rewrite QUIET in NOTCOMP |].
                  by apply bigmax_ltn_ord with (i0 := t).
                }
                repeat split; try done.
                - by apply bigmax_ltn_ord with (i0 := t).
                - move => t0 /andP [GTlast LTbusy] QUIET0.
                  have PRED0: quiet_time_dec j t0.
                  { apply/allP; intros j_hp ARR; apply/implyP; intros HP.
                    apply QUIET0.
                    - by eapply in_arrivals_implies_arrived; eauto.
                    - by done. 
                    - by eapply in_arrivals_implies_arrived_before; eauto.
                  } 
                  have BUG: t0 <= last.
                  { intros.
                    have LE := @leq_bigmax_cond _ (fun (x: 'I_t_busy.+1) => quiet_time_dec j x) (fun x => x) (Ordinal LTbusy) PRED0.
                      by apply LE.
                  }
                  apply leq_trans with (p := last) in GTlast; last by done.
                  by rewrite ltnn in GTlast.
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
                move: H_is_busy_prefix => [H_strictly_larger [H_quiet [_ EXj]]].
                destruct (delta <= priority_inversion_bound) eqn:KLEΔ.
                { by apply leq_trans with priority_inversion_bound; last rewrite leq_addr. }
                apply negbT in KLEΔ; rewrite -ltnNge in KLEΔ. 
                apply leq_trans with (cumulative_priority_inversion j t1 (t1 + delta) + hp_service t1 (t1 + delta)).
                { rewrite /hp_service hep_jobs_receive_no_service_before_quiet_time //.
                  rewrite /service_of_higher_or_equal_priority_jobs /service_of_jobs sum_pred_diff. 
                  rewrite addnBA; last first.
                  { by rewrite big_mkcond //= leq_sum //; intros j' _; case (higher_eq_priority j' j). } 
                  rewrite addnC -addnBA.
                  { intros. have H := no_idle_time_within_non_quiet_time_interval; unfold service_of_jobs in H.
                      by rewrite H // leq_addr.
                  } 
                  { rewrite /cumulative_priority_inversion /is_priority_inversion exchange_big //=.
                    apply leq_sum_seq; move => t II _.
                    rewrite mem_index_iota in II; move: II => /andP [GEi LEt].
                    case SCHED: (sched t) => [j1 | ]; simpl; first last.
                    { by rewrite leqn0 big1_seq; last (move => j1 _; rewrite /service_at /scheduled_at SCHED). } 
                    { case PRIO1: (higher_eq_priority j1 j); simpl; first last.
                      - by eapply service_of_jobs_le_1; eauto 2. 
                      - rewrite leqn0 big1_seq; first by done.
                        move => j2 /andP [PRIO2 ARRj2].
                        rewrite /service_at /scheduled_at SCHED.
                        case EQ: (j1 == j2).
                        + by move: EQ => /eqP EQ; subst j2; rewrite PRIO1 in PRIO2.
                        + apply/eqP; rewrite eqb0; apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
                            by inversion CONTR; clear CONTR; subst j2; rewrite PRIO1 in PRIO2. } } }
                { rewrite leq_add2r.
                  destruct (t1 + delta <= t_busy.+1) eqn:NEQ; [ | apply negbT in NEQ; rewrite -ltnNge in NEQ].
                  - apply leq_trans with (cumulative_priority_inversion j t1 t_busy.+1); last eauto 2.
                      by rewrite [X in _ <= X](@big_cat_nat _ _ _ (t1 + delta)) //=; rewrite leq_addr.
                  -  apply H_priority_inversion_is_bounded; repeat split; try done.
                     + by rewrite -addn1 leq_add2l.
                     + move => t' /andP [LT GT]; apply H_no_quiet_time.
                         by apply/andP; split; [ | rewrite ltnW ].
                     + move: EXj => /andP [T1 T2].
                         by apply/andP; split; [done | apply ltn_trans with (t_busy.+1)].
                }
              Qed.
              
              (* Moreover, the fact that the interval is not quiet also implies
                 that there's more workload requested than service received. *)
              Lemma busy_interval_too_much_workload:
                hp_workload t1 (t1 + delta) > hp_service t1 (t1 + delta).
              Proof.
                have PEND := not_quiet_implies_exists_pending_job.
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
                unfold service_during.
                rewrite (ignore_service_before_arrival job_arrival); rewrite //; [| by apply ltnW].
                rewrite <- ignore_service_before_arrival with (t2:=0); rewrite //; [|by apply ltnW].
                  by rewrite ltnNge; apply/negP.
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
              destruct ([exists t2:'I_(t1 + delta).+1, (t2 > t1) && quiet_time_dec j t2]) eqn:EX.
              { have EX': exists (t2: nat), ((t1 < t2 <= t1 + delta) && quiet_time_dec j t2).
                { move: EX => /existsP [t2 /andP [LE QUIET]].
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
                    unfold quiet_time_dec in *.
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
            { apply/andP; split; first by apply leqnn.
              rewrite /completed_by /service /service_during.
              rewrite (ignore_service_before_arrival job_arrival) //.
              rewrite big_geq; last by apply leqnn.
                by rewrite -ltnNge.
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

        (* If we know that the workload is bounded, we can also use the
           busy interval to infer a response-time bound. *)
        Section ResponseTimeBoundFromBusyInterval.

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

          (* Then, job j must complete by (job_arrival j + delta). *)
          Lemma busy_interval_bounds_response_time:
            job_completed_by j (job_arrival j + delta).
          Proof.
            have BUSY := exists_busy_interval priority_inversion_bound _ delta.
            move: (posnP (job_cost j)) => [ZERO|POS].
            { by rewrite /job_completed_by /completed_by ZERO. } 
            feed_n 4 BUSY; try by done.
            move: BUSY => [t1 [t2 [/andP [GE1 LT2] [GE2 BUSY]]]].
            apply completion_monotonic with (t := t2); try (by done);
              first by apply leq_trans with (n := t1 + delta); [| by rewrite leq_add2r].
            apply job_completes_within_busy_interval with (t1 := t1); try by done.
          Qed.

        End ResponseTimeBoundFromBusyInterval.
       
      End BoundingBusyInterval.

    End Lemmas.
    
    (* In this section, we derive an alternative condition for the existence of 
       a busy interval. The new condition requires the total workload (instead 
       of the high-priority workload) generated by the task set to be bounded. *)
    Section NonOverloadedProcessor.

      (* The processor has no carry-in at time t iff every job (regardless of priority) 
         from the arrival sequence released before t has completed by that time. *)
      Definition no_carry_in (t: time) :=
        forall j_o,
          arrives_in arr_seq j_o ->
          arrived_before job_arrival j_o t ->
          job_completed_by j_o t.

      (* The fact that there is no carry-in at time instant t
         trivially implies that t is a quiet time. *)
      Lemma no_carry_in_implies_quiet_time :
        forall j t,
          no_carry_in t ->
          quiet_time j t.
      Proof.
        by intros j t FQT j_hp ARR HP BEF; apply FQT.
      Qed.
      
      (* Assume that there are no duplicate job arrivals. *)
      Hypothesis H_arrival_sequence_is_a_set:
        arrival_sequence_is_a_set arr_seq.

      (* We also assume that the schedule is work-conserving and that jobs
         do not execute before their arrival nor after completion. *)
      Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
      Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
      Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
      
      (* Next we show that an idle time implies no carry in at this time instant. *)
      Lemma idle_instant_implies_no_carry_in_at_t :
        forall t,
          is_idle sched t ->
          no_carry_in t.
      Proof.
        intros ? IDLE j ARR HA.
        apply/negPn/negP; intros NCOMPL.
         move: IDLE => /eqP IDLE.
         move: (H_work_conserving j t ARR) => NIDLE. 
         feed NIDLE.
         { apply/andP; split; last first.
           { by rewrite /scheduled_at IDLE. }
           { by apply/andP; split; [apply ltnW | done]. }
         }
         move: NIDLE => [j' SCHED].
           by rewrite /scheduled_at IDLE in SCHED.
      Qed.
      
      (* Moreover, an idle time implies no carry in at the next time instant. *)
      Lemma idle_instant_implies_no_carry_in_at_t_pl_1 :
        forall t,
          is_idle sched t ->
          no_carry_in t.+1.
      Proof.
         intros ? IDLE j ARR HA.
         apply/negPn/negP; intros NCOMPL.
         move: IDLE => /eqP IDLE.
         move: (H_work_conserving j t ARR) => NIDLE. 
         feed NIDLE.
         { apply/andP; split; last first.
           { by rewrite /scheduled_at IDLE. }
           { apply/andP; split; first by done.
             move: NCOMPL => /negP NC1; apply/negP; intros NC2; apply: NC1.
               by apply completion_monotonic with t. 
           }  
         }
         move: NIDLE => [j' SCHED].
             by rewrite /scheduled_at IDLE in SCHED.
      Qed.
      
      (* Let the priority relation be reflexive. *)
      Hypothesis H_priority_is_reflexive: JLFP_is_reflexive higher_eq_priority.
      
      (* Next, we recall the notion of workload of all jobs released in a given interval [t1, t2)... *)
      Let total_workload t1 t2 :=
        workload_of_jobs job_cost (arrivals_between t1 t2) predT.

      (* ... and total service of jobs within some time interval [t1, t2). *)
      Let total_service t1 t2 :=
        service_of_jobs sched (arrivals_between 0 t2) predT t1 t2.
      
      (* Assume that for some positive Δ, the sum of requested workload 
         at time (t + Δ) is bounded by delta (i.e., the supply). 
         Note that this assumption bounds the total workload of
         jobs released in a time interval [t, t + Δ) regardless of 
         their priorities. *)
      Variable Δ: time.
      Hypothesis H_delta_positive: Δ > 0.
      Hypothesis H_workload_is_bounded: forall t, total_workload t (t + Δ) <= Δ.

      (* Next we prove that since for any time instant t there is a point where 
         the total workload is upper-bounded by the supply the processor encounters 
         no carry-in instants at least every Δ time units. *)
      Section ProcessorIsNotTooBusy.

        (* We start by proving that the processor has no carry-in at 
           the beginning (i.e., has no carry-in at time instant 0). *)
        Lemma no_carry_in_at_the_beginning :
          no_carry_in 0.
        Proof.
          intros s ARR AB; exfalso.
            by rewrite /arrived_before ltn0 in AB.
        Qed.

        (* In this section, we prove that for any time instant t there
           exists another time instant t' ∈ (t, t + Δ] such that the 
           processor has no carry-in at time t'. *)
        Section ProcessorIsNotTooBusyInduction. 

          (* Consider an arbitrary time instant t... *)
          Variable t: time.
          
          (* ...such that the processor has no carry-in at time t. *)
          Hypothesis H_no_carry_in: no_carry_in t.

          (* First, recall that the total service is bounded by the total workload. Therefore
             the total service of jobs in the interval [t, t + Δ) is bounded by Δ. *)
          Lemma total_service_is_bounded_by_Δ :
            total_service t (t + Δ) <= Δ.
          Proof.
            unfold total_service. 
            rewrite -{3}[Δ]addn0 -{2}(subnn t) addnBA // [in X in _ <= X]addnC.
            apply service_of_jobs_le_delta.
              by eapply arrivals_uniq; eauto 2.
          Qed.

          (* Next we consider two cases: 
             (1) The case when the total service is strictly less than Δ, 
             (2) And when the total service is equal to Δ. *)

          (* In the first case, we use the pigeonhole principle to conclude 
             that there is an idle time instant; which in turn implies existence
             of a time instant with no carry-in. *)
          Lemma low_total_service_implies_existence_of_time_with_no_carry_in :
            total_service t (t + Δ) < Δ ->
            exists δ, δ < Δ /\ no_carry_in (t.+1 + δ).
          Proof.
            unfold total_service; intros LT.
            rewrite -{3}[Δ]addn0 -{2}(subnn t) addnBA // [Δ + t]addnC in LT.
            eapply low_service_implies_existence_of_idle_time in LT; eauto; [ | by rewrite leq_addr].
            move: LT => [t_idle [/andP [LEt GTe] IDLE]].
            move: LEt; rewrite leq_eqVlt; move => /orP [/eqP EQ|LT].
            { exists 0; split; first done.
              rewrite addn0; subst t_idle.
              intros s ARR BEF.
              apply idle_instant_implies_no_carry_in_at_t_pl_1 in IDLE; try done.
                by apply IDLE.
            }
            have EX: exists γ, t_idle = t + γ.
            { by exists (t_idle - t); rewrite subnKC // ltnW. }
            move: EX => [γ EQ]; subst t_idle; rewrite ltn_add2l in GTe.
            rewrite -{1}[t]addn0 ltn_add2l in LT.
            exists (γ.-1); split. 
            - apply leq_trans with γ. by rewrite prednK. by rewrite ltnW.
            - rewrite -subn1 -addn1 -addnA subnKC //.
              intros s ARR BEF.
                by apply idle_instant_implies_no_carry_in_at_t.
          Qed.
          
          (* In the second case, the total service within the time interval [t, t + Δ) is equal to Δ. 
             On the other hand, we know that the total workload is lower-bounded by the total service
             and upper-bounded by Δ. Therefore, the total workload is equal to total service this
             implies completion of all jobs by time [t + Δ] and hence no carry-in at time [t + Δ]. *)
          Lemma completion_of_all_jobs_implies_no_carry_in :
            total_service t (t + Δ) = Δ ->
            no_carry_in (t + Δ).
          Proof.
            unfold total_service; intros EQserv.
            move: (H_workload_is_bounded t); move => WORK.
            have EQ: total_workload 0 (t + Δ) = service_of_jobs sched (arrivals_between 0 (t + Δ)) predT 0 (t + Δ).
            { intros.
              have COMPL := all_jobs_have_completed_impl_workload_eq_service
                              job_arrival job_cost arr_seq _ sched _ _ predT 0 t t.
              feed_n 4 COMPL; try done.
              { intros; apply H_no_carry_in.
                - eapply in_arrivals_implies_arrived; eauto 2.
                - eapply in_arrivals_implies_arrived_between in H; eauto 2.
                    by move: H => /andP [_ H].
              }
              apply/eqP; rewrite eqn_leq; apply/andP; split; last by apply service_of_jobs_le_workload.
              rewrite /total_workload (workload_of_jobs_cat job_cost arr_seq (t)); last first.
              apply/andP; split; [by done | by rewrite leq_addr].
              rewrite (service_of_jobs_cat_scheduling_interval job_arrival _ _ _ _ _ _ _ t); try done; first last.
              { by apply/andP; split; [by done | by rewrite leq_addr]. }
              rewrite COMPL -addnA leq_add2l. 
              rewrite -service_of_jobs_cat_arrival_interval; last first.
              apply/andP; split; [by done| by rewrite leq_addr].
              rewrite EQserv.
                by apply H_workload_is_bounded.
            }  
            intros s ARR BEF.
            eapply workload_eq_service_impl_all_jobs_have_completed; eauto 2; try done.
              by eapply arrived_between_implies_in_arrivals; eauto 2.
          Qed.

        End ProcessorIsNotTooBusyInduction.

        (* Finally, we show that any interval of length Δ contains a time instant with no carry-in. *)
        Lemma processor_is_not_too_busy :
          forall t, exists δ, δ < Δ /\ no_carry_in (t + δ).
        Proof.
          induction t.
          { by exists 0; split; [ | rewrite addn0; apply no_carry_in_at_the_beginning]. }
          { move: IHt => [δ [LE FQT]].
            move: (posnP δ) => [Z|POS]; last first.
            { exists (δ.-1); split.
              - by apply leq_trans with δ; [rewrite prednK | apply ltnW]. 
              - by rewrite -subn1 -addn1 -addnA subnKC //.
            } subst δ; rewrite addn0 in FQT; clear LE.
            move: (total_service_is_bounded_by_Δ t); rewrite leq_eqVlt; move => /orP [/eqP EQ | LT].
            - exists (Δ.-1); split.
              + by rewrite prednK. 
              + by rewrite addSn -subn1 -addn1 -addnA subnK; first apply completion_of_all_jobs_implies_no_carry_in.
            - by apply low_total_service_implies_existence_of_time_with_no_carry_in. 
          }
        Qed.
        
      End ProcessorIsNotTooBusy.
      
      (* Consider an arbitrary job j with positive cost. *)
      Variable j: Job.
      Hypothesis H_from_arrival_sequence: arrives_in arr_seq j.
      Hypothesis H_job_cost_positive: job_cost_positive job_cost j.    

      (* We show that there must exists a busy interval [t1, t2) that
         contains the arrival time of j. *)
      Corollary exists_busy_interval_from_total_workload_bound :
        exists t1 t2, 
          t1 <= job_arrival j < t2 /\
          t2 <= t1 + Δ /\
          busy_interval j t1 t2.
      Proof.
        have PREFIX := exists_busy_interval_prefix j _ _ (job_arrival j).
        feed_n 3 PREFIX; try done.
        { apply/andP; split; first by apply leqnn.
          rewrite /completed_by /service /service_during.
          rewrite (ignore_service_before_arrival job_arrival) //.
          rewrite big_geq; last by apply leqnn.
          move: H_job_cost_positive; rewrite /job_cost_positive; move => POS.
            by rewrite -ltnNge. 
        } move: PREFIX => [t1 [PREFIX /andP [GE1 _]]].
        exists t1; move: (processor_is_not_too_busy t1.+1) => [δ [LE QT]].
        apply no_carry_in_implies_quiet_time with (j := j) in QT.
        have EX: exists t2, ((t1 < t2 <= t1.+1 + δ) && quiet_time_dec j t2).
        { exists (t1.+1 + δ); apply/andP; split.
          - by apply/andP; split; first rewrite addSn ltnS leq_addr. 
          - by apply/quiet_time_P. }
        move: (ex_minnP EX) => [t2 /andP [/andP [GTt2 LEt2] QUIET] MIN]; clear EX.
        have NEQ: t1 <= job_arrival j < t2.
        { apply/andP; split; first by done. 
          rewrite ltnNge; apply/negP; intros CONTR.
          move: (PREFIX) => [_ [_ [NQT _]]].
          move: (NQT t2); clear NQT; move  => NQT.
          feed NQT; first by (apply/andP; split; [|rewrite ltnS]). 
            by apply: NQT; apply/quiet_time_P.
        }
        exists t2; split; last split; first by done. 
        { apply leq_trans with (t1.+1 + δ); [by done | by rewrite addSn ltn_add2l]. }
        { move: PREFIX => [_ [QTt1 [NQT _]]]; repeat split; try done.
          - move => t /andP [GEt LTt] QTt.
            feed (MIN t).
            { apply/andP; split.
              + by apply/andP; split; last (apply leq_trans with t2; [apply ltnW | ]).
              + by apply/quiet_time_P.
            }
              by move: LTt; rewrite ltnNge; move => /negP LTt; apply: LTt.
          - by apply/quiet_time_P. 
        }
      Qed.
     
    End NonOverloadedProcessor. 
    
  End Definitions. 
    
End BusyIntervalJLFP.
     