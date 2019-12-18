Require Import prosa.classic.util.all.
Require Import prosa.classic.model.time prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module UniprocessorSchedule.

  Import SporadicTaskset.
  Export Time ArrivalSequence.

  Section Schedule.
 
    (* We begin by defining a uniprocessor schedule. *)
    Section ScheduleDef.

      (* Consider any job type. *)
      Variable Job: eqType.

      (* We define a uniprocessor schedule by mapping each point in time to either
         Some job that is scheduled or None, if the processor is idle. *)
      Definition schedule := time -> option Job.

    End ScheduleDef.

    (* In this section, we define properties of a schedule. *)
    Section ScheduleProperties.

      Context {Job: eqType}.
      Variable job_arrival: Job -> time.
      Variable job_cost: Job -> time.

      (* Consider any uniprocessor schedule. *)
      Variable sched: schedule Job.

      (* Let's define properties of the jobs to be scheduled. *)
      Section JobProperties.
        
        (* Let j be any job. *)
        Variable j: Job.

        (* First, we define whether a job j is scheduled at time t, ... *)
        Definition scheduled_at (t: time) := sched t == Some j.

        (* ...which also yields the instantaneous service received by
           job j at time t (i.e., either 0 or 1). *)
        Definition service_at (t: time) : time := scheduled_at t.

        (* Based on the notion of instantaneous service, we define the
           cumulative service received by job j during any interval [t1, t2). *)
        Definition service_during (t1 t2: time) :=
          \sum_(t1 <= t < t2) service_at t.

        (* Using the previous definition, we define the cumulative service
           received by job j up to time t, i.e., during interval [0, t). *)
        Definition service (t: time) := service_during 0 t.

        (* Next, we say that job j has completed by time t if it received enough
           service in the interval [0, t). *)
        Definition completed_by (t: time) := job_cost j <= service t.

        (* Job j is pending at time t iff it has arrived but has not yet completed. *)
        Definition pending (t: time) := has_arrived job_arrival j t && ~~ completed_by t.

        (* Job j is pending earlier and at time t iff it has arrived before time t 
           and has not been completed yet. *)
        Definition pending_earlier_and_at (t: time) :=
          arrived_before job_arrival j t && ~~ completed_by t.

        (* Job j is backlogged at time t iff it is pending and not scheduled. *)
        Definition backlogged (t: time) := pending t && ~~ scheduled_at t.
        
      End JobProperties.

      (* In this section, we define some properties of the processor. *)
      Section ProcessorProperties.

        (* We say that the processor is idle at time t iff there is no job being scheduled. *)
        Definition is_idle (t: time) := sched t == None.

        (* In addition, we define the total service performed by the processor in any interval
           [t1, t2) as the cumulative time in which the processor is not idle. *)
        Definition total_service_during (t1 t2: time) :=
          \sum_(t1 <= t < t2) ~~ is_idle t.

        (* Using the previous definition, we also define the total service up to time t2.*)
        Definition total_service (t2: time) := total_service_during 0 t2.

      End ProcessorProperties.

      Section PropertyOfSequentiality.

        Context {Task: eqType}.    
        Variable job_task: Job -> Task.

        (* We say that two jobs j1 and j2 are from the same task, if job_task j1 is equal to job_task j2. *)
        Let same_task j1 j2 := job_task j1 == job_task j2.

        (* We say that the jobs are sequential if they are executed in the order they arrived. *) 
        Definition sequential_jobs :=
          forall j1 j2 t,
            same_task j1 j2 ->
            job_arrival j1 < job_arrival j2 ->
            scheduled_at j2 t ->
            completed_by j1 t.

        (* Assume the hypothesis about sequential jobs holds. *)
        Hypothesis H_sequential_jobs: sequential_jobs.
        
        (* A simple corollary of this hypothesis is that the scheduler 
           executes a job with the earliest arrival time. *)
        Corollary scheduler_executes_job_with_earliest_arrival:
          forall j1 j2 t,
            same_task j1 j2 -> 
            ~~ completed_by j2 t ->
            scheduled_at j1 t ->
            job_arrival j1 <= job_arrival j2.
        Proof.
          intros ? ? t TSK NCOMPL SCHED.
          rewrite /same_task eq_sym in TSK.
          have SEQ := H_sequential_jobs j2 j1 t TSK.
          rewrite leqNgt; apply/negP; intros ARR.
          move: NCOMPL => /negP NCOMPL; apply: NCOMPL.
            by apply SEQ.
        Qed.

      End PropertyOfSequentiality.
      
    End ScheduleProperties.

    (* In this section, we define properties of valid schedules. *)
    Section ValidSchedules.

      Context {Job: eqType}.
      Variable job_arrival: Job -> time.
      Variable job_cost: Job -> time.

      (* Consider any uniprocessor schedule. *)
      Variable sched: schedule Job.

      (* We define whether jobs come from some arrival sequence... *)
      Definition jobs_come_from_arrival_sequence (arr_seq: arrival_sequence Job) :=
        forall j t, scheduled_at sched j t -> arrives_in arr_seq j.
      
      (* ..., whether a job can only be scheduled if it has arrived ... *)
      Definition jobs_must_arrive_to_execute :=
        forall j t, scheduled_at sched j t -> has_arrived job_arrival j t.

      (* ... and whether a job cannot be scheduled after it completes. *)
      Definition completed_jobs_dont_execute :=
        forall j t, service sched j t <= job_cost j.

    End ValidSchedules.

    (* In this section, we prove some basic lemmas about schedules. *)   
    Section Lemmas.

      Context {Job: eqType}.
      Variable job_arrival: Job -> time.
      Variable job_cost: Job -> time.

      (* Consider any uniprocessor schedule. *)
      Variable sched: schedule Job.

      (* Let's define the remaining cost of job j as the amount of service 
         that has to be received for its completion. *)
      Definition remaining_cost j t :=
        job_cost j - service sched j t.      

      (* Let's begin with lemmas about service. *)
      Section Service.

        (* Let j be any job that is to be scheduled. *)
        Variable j: Job.
        
        (* First, we prove that the instantaneous service cannot be greater than 1, ... *)
        Lemma service_at_most_one:
          forall t, service_at sched j t <= 1.
        Proof.
          by intros t; apply leq_b1.
        Qed.

        (* ...which implies that the cumulative service received by job j in any
           interval of length delta is at most delta. *)
        Lemma cumulative_service_le_delta:
          forall t delta,
            service_during sched j t (t + delta) <= delta.
        Proof.
          unfold service_during; intros t delta.
          apply leq_trans with (n := \sum_(t <= t0 < t + delta) 1);
            last by simpl_sum_const; rewrite addKn leqnn.
          by apply leq_sum; intros t0 _; apply leq_b1.
        Qed.
            
        (* Assume that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.
        
        (* Note that if a job scheduled at some time t then remaining 
             cost at this point is positive *)
        Lemma scheduled_implies_positive_remaining_cost:
          forall t,
            scheduled_at sched j t ->
            remaining_cost j t > 0.
        Proof. 
          intros.
          rewrite subn_gt0 /service /service_during.
          apply leq_trans with (\sum_(0 <= t0 < t.+1) service_at sched j t0);
            last by rewrite H_completed_jobs.
          by rewrite big_nat_recr //= -addn1 leq_add2l lt0b.
        Qed.
          
      End Service.

      (* Next, we prove properties related to job completion. *)
      Section Completion.
              
        (* Let j be any job that is to be scheduled. *)
        Variable j: Job.
        
        (* We prove that after job j completes, it remains completed. *)
        Lemma completion_monotonic:
          forall t t',
            t <= t' ->
            completed_by job_cost sched j t ->
            completed_by job_cost sched j t'.
        Proof. 
          unfold completed_by; move => t t' LE COMPt.
          apply leq_trans with (service sched j t); first by done.
            by rewrite /service /service_during [in X in _ <= X](@big_cat_nat _ _ _ t) //= leq_addr.
        Qed.          

        (* Assume that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.
        
        (* We also prove that a completed job cannot be scheduled. *)
        Lemma completed_implies_not_scheduled :
          forall t,
            completed_by job_cost sched j t ->
            ~~ scheduled_at sched j t.
        Proof.
          rename H_completed_jobs into COMP.
          unfold completed_jobs_dont_execute in *.
          intros t COMPLETED.
          apply/negP; red; intro SCHED.
          have BUG := COMP j t.+1.
          rewrite leqNgt in BUG; move: BUG => /negP BUG; apply: BUG.
          unfold service, service_during; rewrite big_nat_recr // /= -addn1.
          apply leq_add; first by done. 
            by rewrite /service_at SCHED.
        Qed.

        (* ... and that a scheduled job cannot be completed. *)
        Lemma scheduled_implies_not_completed:
          forall t,
            scheduled_at sched j t ->
            ~~ completed_by job_cost sched j t.
        Proof.
          move => t SCHED.
          rewrite /completed_by; apply/negP; intros CONTR.
          apply completed_implies_not_scheduled in CONTR.
            by move: CONTR => /negP CONTR; apply: CONTR.
        Qed.
        
        (* Next, we show that the service received by job j in any interval
           is no larger than its cost. *)
        Lemma cumulative_service_le_job_cost :
          forall t t',
            service_during sched j t t' <= job_cost j.
        Proof.
          unfold service_during; rename H_completed_jobs into COMP; red in COMP; ins.
          destruct (t > t') eqn:GT.
            by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
            apply leq_trans with
                (n := \sum_(0 <= t0 < t') service_at sched j t0);
              last by apply COMP.
            rewrite -> big_cat_nat with (m := 0) (n := t);
              [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
        Qed.

        (* If a job isn't complete at time t, 
           it can't be completed at time (t + remaining_cost j t - 1). *)
        Lemma job_doesnt_complete_before_remaining_cost:
          forall t,
            ~~ completed_by job_cost sched j t -> 
            ~~ completed_by job_cost sched j (t + remaining_cost j t - 1).
        Proof.
          intros t GT0.
          unfold remaining_cost, completed_by in *.
          have COSTGT0: job_cost j > 0.
          { apply contraT; rewrite -eqn0Ngt.
            move => /eqP EQ0.
              by rewrite EQ0 -ltnNge ltn0 in GT0.
          }
          rewrite -ltnNge.
          rewrite /service /service_during.
          set delta := (X in (t + X - 1)).
          have NONZERO: delta > 0.
          { rewrite -ltnNge in GT0.
            by rewrite /delta subn_gt0. 
          }
          rewrite (@big_cat_nat _ _ _ t) //= ?leq_addr //;
            last by rewrite -addnBA; [rewrite leq_addr | done].
          apply leq_ltn_trans with (n := service sched j t + \sum_(t <= i < t + delta - 1) 1);
            first by rewrite leq_add2l; apply leq_sum; intros; apply leq_b1.
          simpl_sum_const.
          rewrite -addnBA // addKn.
          rewrite addnBA // /delta.
          rewrite subnKC; last by done.
          rewrite subn1 -(ltn_add2r 1) addn1. 
            by rewrite prednK // addn1 ltnSn.
        Qed.
        
        (* In this section, we prove that the job with a positive 
           cost must be scheduled to be completed. *)
        Section JobMustBeScheduled.
          
          (* We assume that job j has positive cost, from which we can
             infer that there always is a time in which j is pending. *)
          Hypothesis H_positive_cost: job_cost j > 0.

          (* Assume that jobs must arrive to execute. *)
          Hypothesis H_jobs_must_arrive:
            jobs_must_arrive_to_execute job_arrival sched.
        
          (* Then, we prove that the job with a positive cost 
             must be scheduled to be completed. *)
          Lemma completed_implies_scheduled_before:
            forall t,
              completed_by job_cost sched j t ->
              exists t',
                job_arrival j <= t' < t
                /\ scheduled_at sched j t'.
          Proof.
            intros t COMPL.
            induction t.
            { exfalso.
              unfold completed_by, service, service_during in COMPL.
              move: COMPL; rewrite big_geq //; move => /eqP H0.
                by destruct (job_cost j).
            }
            destruct (completed_by job_cost sched j t) eqn:COMPLatt.
            { feed IHt; first by done.
              move: IHt => [t' [JA SCHED]].
              exists t'. split; first apply/andP; first split.
              - by apply H_jobs_must_arrive in SCHED.
              - move: JA => /andP [_ LT]. by apply leq_trans with t.
              - by done.
            }
            { apply negbT in COMPLatt.
              unfold completed_by in *.
              rewrite -ltnNge in COMPLatt.
              unfold service, service_during in COMPL.
              rewrite big_nat_recr //= in COMPL.
              have SCHED: scheduled_at sched j t.
              { rewrite {2}/service_at in COMPL.
                destruct (scheduled_at sched j t); first by done.
                rewrite addn0 in COMPL.
                  by exfalso; move: COMPL; rewrite leqNgt; move => /negP C; apply: C.
              }
              exists t. split; first apply/andP; first split; try done.
                by apply H_jobs_must_arrive in SCHED.
            }
          Qed.

        End JobMustBeScheduled. 
        
      End Completion.

      (* In this section we prove properties related to job arrivals. *)
      Section Arrival.

        (* Assume that jobs must arrive to execute. *)
        Hypothesis H_jobs_must_arrive:
          jobs_must_arrive_to_execute job_arrival sched.

        (* Let j be any job that is to be scheduled. *)
        Variable j: Job.

        (* First, we show that job j does not receive service at any time t
           prior to its arrival. *)
        Lemma service_before_job_arrival_zero :
          forall t,
            t < job_arrival j ->
            service_at sched j t = 0.
        Proof.
          rename H_jobs_must_arrive into ARR; red in ARR; intros t LT.
          specialize (ARR j t).
          apply contra with (c := scheduled_at sched j t)
                              (b := has_arrived job_arrival j t) in ARR;
            last by rewrite -ltnNge.
          by apply/eqP; rewrite eqb0.
        Qed.

        (* Note that the same property applies to the cumulative service. *)
        Lemma cumulative_service_before_job_arrival_zero :
          forall t1 t2,
            t2 <= job_arrival j ->
            \sum_(t1 <= i < t2) service_at sched j i = 0.
        Proof.
          intros t1 t2 LE; apply/eqP; rewrite -leqn0.
          apply leq_trans with (n := \sum_(t1 <= i < t2) 0);
            last by rewrite big_const_nat iter_addn mul0n addn0.
          rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
          apply leq_sum; intro i; rewrite andbT; move => /andP LTi; des.
          rewrite service_before_job_arrival_zero; first by ins.
          by apply leq_trans with (n := t2); ins.
        Qed.

        (* Hence, one can ignore the service received by a job before its arrival time. *)
        Lemma ignore_service_before_arrival:
          forall t1 t2,
            t1 <= job_arrival j ->
            t2 >= job_arrival j ->
            \sum_(t1 <= t < t2) service_at sched j t =
              \sum_(job_arrival j <= t < t2) service_at sched j t.
        Proof.
          intros t1 t2 LE1 GE2.
          rewrite -> big_cat_nat with (n := job_arrival j);
            [| by done | by done].
          by rewrite /= cumulative_service_before_job_arrival_zero; [rewrite add0n | apply leqnn].
        Qed.

      End Arrival.

      (* In this section, we prove properties about pending jobs. *)
      Section Pending.

        (* Assume that jobs must arrive to execute... *)
        Hypothesis H_jobs_must_arrive:
          jobs_must_arrive_to_execute job_arrival sched.

       (* ...and that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.

        (* Let j be any job. *)
        Variable j: Job.

        (* We show that if job j is scheduled, then it must be pending. *)
        Lemma scheduled_implies_pending:
          forall t,
            scheduled_at sched j t ->
            pending job_arrival job_cost sched j t.
        Proof.
          rename H_jobs_must_arrive into ARRIVE,
                 H_completed_jobs into COMP.
          unfold jobs_must_arrive_to_execute, completed_jobs_dont_execute in *.
          intros t SCHED.
          unfold pending; apply/andP; split; first by apply ARRIVE.
          apply/negP; unfold not; intro COMPLETED.
          have BUG := COMP j t.+1.
          rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
          unfold service, service_during; rewrite -addn1 big_nat_recr // /=.
          apply leq_add; first by done.
            by rewrite /service_at SCHED.
        Qed.

        (* Consider any arrival sequence. *)
        Variable arr_seq: arrival_sequence Job.
    
        (* Then we prove that the job is pending at the moment of its arrival. *)
        Lemma job_pending_at_arrival:
            arrives_in arr_seq j ->
            job_cost j > 0 ->
            pending job_arrival job_cost sched j (job_arrival j).
        Proof.
          intros ARR POS.
          apply/andP; split; first by rewrite /has_arrived.
          rewrite -ltnNge. 
          rewrite /service /service_during (ignore_service_before_arrival); try done.
            by rewrite big_geq; eauto 2.
        Qed.

      End Pending.

      (* In this section we show that the schedule is unique at any point. *)
      Section OnlyOneJobScheduled.

        (* Let j1 and j2 be any jobs. *)
        Variable j1 j2: Job.

        (* At any time t, if both j1 and j2 are scheduled, then they must be the same job. *)
        Lemma only_one_job_scheduled:
          forall t,
            scheduled_at sched j1 t ->
            scheduled_at sched j2 t ->
            j1 = j2.
        Proof.
          move => t /eqP SCHED1 /eqP SCHED2.
          by rewrite SCHED1 in SCHED2; inversion SCHED2.
        Qed.
          
      End OnlyOneJobScheduled.

      Section ServiceIsAStepFunction.

        (* First, we show that the service received by any job j
           is a step function. *)
        Lemma service_is_a_step_function:
          forall j,
            is_step_function (service sched j).
        Proof.
          unfold is_step_function, service, service_during; intros j t.
          rewrite addn1 big_nat_recr //=.
          by apply leq_add; last by apply leq_b1.
        Qed.

        (* Next, consider any job j at any time t... *)
        Variable j: Job.
        Variable t: time.

        (* ...and let s0 be any value less than the service received
           by job j by time t. *)
        Variable s0: time.
        Hypothesis H_less_than_s: s0 < service sched j t.

        (* Then, we show that there exists an earlier time t0 where
           job j had s0 units of service. *)
        Corollary exists_intermediate_service:
          exists t0,
            t0 < t /\
            service sched j t0 = s0.
        Proof.
          feed (exists_intermediate_point (service sched j));
            [by apply service_is_a_step_function | intros EX].
          feed (EX 0 t); first by done.
          feed (EX s0);
            first by rewrite /service /service_during big_geq //. 
          by move: EX => /= [x_mid EX]; exists x_mid.
        Qed.

      End ServiceIsAStepFunction.

      Section ScheduledAtEarlierTime.

        (* Next, we show that if the service is positive,
           then the job is scheduled at some earlier time. *)
        Lemma scheduled_at_earlier_time:
          forall j t,
            service sched j t > 0 ->
            exists t0,
              t0 < t /\
              scheduled_at sched j t0.
        Proof.
          intros j t GT.
          case (boolP ([exists t0:'I_t, scheduled_at sched j t0])) => [EX | ALL];
            first by move: EX => /existsP [t0 SCHED]; exists t0; split. 
          rewrite negb_exists in ALL; move: ALL => /forallP ALL.
          rewrite /service /service_during big_nat_cond big1 in GT; first by rewrite ltnn in GT.
          move => i => /andP [/= LT _].
          by apply/eqP; rewrite eqb0; apply (ALL (Ordinal LT)).
        Qed.
        
      End ScheduledAtEarlierTime.

      Section ServiceNotZero.

        (* Let j be any job. *)
        Variable j: Job.

        (* Assume that the service received by j during [t1, t2) is not zero. *)
        Variable t1 t2: time.
        Hypothesis H_service_not_zero: service_during sched j t1 t2 > 0.
        
        (* Then, there must be a time t where job j is scheduled. *)
        Lemma cumulative_service_implies_scheduled :
          exists t,
            t1 <= t < t2 /\ 
            scheduled_at sched j t.
        Proof.
          rename H_service_not_zero into NONZERO.
          case (boolP([exists t: 'I_t2,
                 (t >= t1) && (service_at sched j t != 0)])) => [EX | ALL].
          {
            move: EX => /existsP [x /andP [GE SERV]].
            rewrite eqb0 negbK in SERV.
            exists x; split; last by done.
            by apply/andP; split; last by apply ltn_ord.
          }
          {
            rewrite negb_exists in ALL; move: ALL => /forallP ALL. 
            rewrite /service_during big_nat_cond in NONZERO.
            rewrite big1 ?ltn0 // in NONZERO.
            intros i; rewrite andbT; move => /andP [GT LT].
            specialize (ALL (Ordinal LT)); simpl in ALL.
            by rewrite GT andTb negbK in ALL; apply/eqP.
          }
        Qed.

      End ServiceNotZero.

      (* In this section, we prove some lemmas about time instants
         with same service. *)
      Section TimesWithSameService.

        (* Let j be any job. *)
        Variable j: Job.

        (* Consider any time instants t1 and t2... *)
        Variable t1 t2: time.

        (* ...where job j has received the same amount of service. *)
        Hypothesis H_same_service: service sched j t1 = service sched j t2.

        (* First, we show that job j is scheduled at some point t < t1 iff
           j is scheduled at some point t' < t2.  *)
        Lemma same_service_implies_scheduled_at_earlier_times:
          [exists t: 'I_t1, scheduled_at sched j t] =
            [exists t': 'I_t2, scheduled_at sched j t'].
        Proof.
          rename H_same_service into SERV.
          move: t1 t2 SERV; clear t1 t2; move => t t'.
          wlog: t t' / (t <= t') => [EX SAME | LE SERV].
            by case/orP: (leq_total t t'); ins; [|symmetry]; apply EX.
          apply/idP/idP; move => /existsP [t0 SCHED].
          {
            have LT0: t0 < t' by apply: (leq_trans _ LE).
            by apply/existsP; exists (Ordinal LT0). 
          }
          {
            destruct (ltnP t0 t) as [LT01 | LE10];
              first by apply/existsP; exists (Ordinal LT01).
            exfalso; move: SERV => /eqP SERV.
            rewrite -[_ == _]negbK in SERV.
            move: SERV => /negP BUG; apply BUG; clear BUG.
            rewrite neq_ltn; apply/orP; left.
            rewrite /service /service_during.
            rewrite -> big_cat_nat with (n := t0) (p := t');
              [simpl | by done | by apply ltnW].
            rewrite -addn1; apply leq_add; first by apply extend_sum.
            destruct t0 as [t0 LT]; simpl in *.
            destruct t'; first by rewrite ltn0 in LT.
            rewrite big_nat_recl; last by done.
            by rewrite /service_at SCHED.
          }
        Qed.
        
      End TimesWithSameService.

    End Lemmas.
  
  End Schedule.
 
End UniprocessorSchedule.