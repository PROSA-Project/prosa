Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.arrival_sequence
               prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.schedule.uni.schedule prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
Require Import prosa.classic.implementation.uni.basic.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

Module ReductionToBasicSchedule.

  Import Job SporadicTaskset Suspension Priority SuspensionIntervals
         Schedulability ScheduleConstruction.

  (* Recall the platform constraints for suspension-oblivious and suspension-aware schedules. *)
  Module susp := ScheduleWithSuspensions.
  Module susp_oblivious := Platform.
  Module susp_aware := PlatformWithSuspensions.
  
  (* In this section, we perform a reduction from a suspension-aware schedule
     to a suspension-oblivious schedule, in which jobs have inflated execution costs. *)
  Section Reduction.

    Context {Task: eqType}.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Let ts be any task set to be analyzed. *)
    Variable ts: seq Task.

    (* Next, consider any consistent job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.

    (* ...whose jobs come from task set ts. *)
    Hypothesis H_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Consider any JLDP policy that is reflexive, transitive and total, i.e., that
       indicates "higher or equal priority". *)
    Variable higher_eq_priority: JLDP_policy Job.
    Hypothesis H_priority_is_reflexive: JLDP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: JLDP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: JLDP_is_total arr_seq higher_eq_priority.

    (* Consider the original job and task costs. *)
    Variable original_job_cost: Job -> time.
    Variable original_task_cost: Task -> time.

    (* Assume that the maximum suspension time of any job is bounded according
       to the dynamic suspension model. *)
    Variable next_suspension: job_suspension Job.
    Variable task_suspension_bound: Task -> time.
    Hypothesis H_dynamic_suspensions:
      dynamic_suspension_model original_job_cost job_task next_suspension task_suspension_bound.
      
    (* Next, consider any suspension-aware schedule of this arrival sequence. *)
    Variable sched_susp: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched_susp arr_seq.

    (* Assume that jobs only execute after they arrive... *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched_susp.

    (* ...and no longer than their execution costs. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute original_job_cost sched_susp.

    (* Also assume that the schedule is work-conserving if there are non-suspended jobs, ... *)
    Hypothesis H_work_conserving:
      susp_aware.work_conserving job_arrival original_job_cost next_suspension arr_seq sched_susp.

    (* ...that the schedule respects job priority... *)
    Hypothesis H_respects_priority:
      susp_aware.respects_JLDP_policy job_arrival original_job_cost next_suspension
                                      arr_seq sched_susp higher_eq_priority.

    (* ...and that suspended jobs are not allowed to be scheduled. *)
    Hypothesis H_respects_self_suspensions:
      respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp.

    (* Now we proceed with the reduction. First, we formalize the inflation of job and task costs. *)
    Section CostInflation.

      (* Recall the total suspension time of a job in the original schedule. *)
      Let job_total_suspension :=
        total_suspension original_job_cost next_suspension.

      (* To inflate job costs, we just add the total suspension of the job. *)
      Definition inflated_job_cost (j: Job) :=
        original_job_cost j + job_total_suspension j.

      (* Similarly, to inflate task costs, we just add its suspension bound. *)
      Definition inflated_task_cost (tsk: Task) :=
        original_task_cost tsk + task_suspension_bound tsk.

      (* As shown next, this inflation produces job valid parameters. *)
      Section NewParametersAreValid.

        (* Recall the definition of valid sporadic jobs and tasks. *)
        Let jobs_are_valid job_cost task_cost :=
          forall j,
            arrives_in arr_seq j ->
            valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
        Let tasks_are_valid task_cost :=
          valid_sporadic_taskset task_cost task_period task_deadline ts.
        
        (* If the inflated task costs are no larger than the deadline nor period of each task, ... *)
        Hypothesis H_inflated_cost_le_deadline_and_period:
          forall tsk,
            tsk \in ts ->
            inflated_task_cost tsk <= task_deadline tsk /\
            inflated_task_cost tsk <= task_period tsk.
      
        (* ...then we can prove that job parameters remain valid after the inflation. *)
        Lemma suspension_oblivious_job_parameters_remain_valid:
          jobs_are_valid original_job_cost original_task_cost ->
          jobs_are_valid inflated_job_cost inflated_task_cost.
        Proof.
          rename H_inflated_cost_le_deadline_and_period into LEdl,
                 H_dynamic_suspensions into DYN, H_jobs_from_taskset into FROMTS.
          unfold jobs_are_valid, valid_sporadic_job, valid_realtime_job.
          intros VALIDjob j ARRj; specialize (VALIDjob j ARRj); des.
          split.
          {
            split;
              first by apply leq_trans with (n := original_job_cost j);
                last by apply leq_addr.
            split; last by done.
            rewrite /job_cost_le_deadline /inflated_job_cost.
            feed (LEdl (job_task j)); [by apply FROMTS | move: LEdl => [LEdl _]].
            apply leq_trans with (n := inflated_task_cost (job_task j));
              last by rewrite VALIDjob1 LEdl.
            by apply leq_add; last by apply DYN.
          }
          split; last by done.
          by apply leq_add; last by apply DYN.
        Qed.

        (* The same applies for task parameters. *)
        Lemma suspension_oblivious_task_parameters_remain_valid:
          tasks_are_valid original_task_cost -> tasks_are_valid inflated_task_cost.
        Proof.
          rename H_inflated_cost_le_deadline_and_period into LEdl.
          unfold tasks_are_valid, valid_sporadic_taskset, is_valid_sporadic_task.
          intros VALIDtask tsk IN; specialize (VALIDtask tsk IN); des.
          split;
            first by apply: (leq_trans VALIDtask); last by apply leq_addr.
          specialize (LEdl tsk IN); move: LEdl => [LEdl LEp].
          by repeat split.
        Qed.
        
      End NewParametersAreValid.
      
    End CostInflation.

    (* Now, we are going to generate a suspension-oblivious schedule with the inflated
       job costs. For that, we always try to copy the original schedule, as long as that
       doesn't break the priority enforcement in the generated schedule. *)

    Section ScheduleConstruction.

      (* In this section, we define the schedule construction function. *)
      Section ConstructionStep.
        
        (* For any time t, suppose that we have generated the schedule prefix in the
           interval [0, t). Then, we must define what should be scheduled at time t. *)
        Variable sched_prefix: schedule Job.
        Variable t: time.
        
        (* First, consider the list of pending jobs at time t in the generated schedule. *)
        Let job_is_pending := pending job_arrival inflated_job_cost sched_prefix.
        Definition pending_jobs :=
          [seq j <- jobs_arrived_up_to arr_seq t | job_is_pending j t].

        (* From the list of pending jobs, we take one of the (possibly many) highest-priority
           jobs, or None, in case there are no pending jobs. *)
        Definition highest_priority_job := seq_min (higher_eq_priority t) pending_jobs.

        (* Then, we construct the schedule at time t as follows.
           a) If there's a job scheduled in the original schedule at time t that is also a
              highest-priority pending job in the generated schedule, copy this job.
           b) Else, pick one of the highest priority pending jobs in the generated schedule. *)
        
        Definition build_schedule : option Job :=
          (* If there is a highest-priority job j_hp in the generated schedule, ...*)
          if highest_priority_job is Some j_hp then
            (* ...and there is some job scheduled in the original schedule... *)
            if (sched_susp t) is Some j_sched then
              (* ...that is a highest-priority pending job,...*)
              if job_is_pending j_sched t && higher_eq_priority t j_sched j_hp then 
                Some j_sched (* ...copy this scheduled job. *)
              else
                highest_priority_job     (* In the remaining cases, just pick the           *)
            else highest_priority_job    (* highest-priority job in the generated schedule. *)
          else highest_priority_job.

      End ConstructionStep.

      (* Next, starting from the empty schedule, ...*)
      Let empty_schedule : schedule Job := fun t => None.

      (* ...we use the recursive definition above to construct the suspension-oblivious schedule. *)
      Definition sched_new := build_schedule_from_prefixes build_schedule empty_schedule.

      (* Then, by showing that the construction function depends only on the previous service, ... *)
      Lemma sched_new_depends_only_on_service:
        forall sched1 sched2 t,
          (forall j, service sched1 j t = service sched2 j t) ->          
          build_schedule sched1 t = build_schedule sched2 t.
      Proof.
        intros sched1 sched2 t ALL.
        rewrite /build_schedule /highest_priority_job.
        have SAME: pending_jobs sched1 t = pending_jobs sched2 t.
        {
          apply eq_in_filter.
          intros j IN.
          eapply in_arrivals_implies_arrived_before in IN; last by eauto.
          rewrite /arrived_before ltnS in IN.
          rewrite /pending /has_arrived IN 2!andTb.
          by rewrite /completed_by ALL.
        }
        have SAME': forall j, pending job_arrival inflated_job_cost sched1 j t =
                              pending job_arrival inflated_job_cost sched2 j t.
        {
          intros j; rewrite /pending.
          case: (has_arrived _ j t); [rewrite 2!andTb | by done].
          by rewrite /completed_by ALL.
        }
        rewrite SAME.
        desf; try (by done).
        - by rewrite SAME' in Heq1.
        - by rewrite -SAME' in Heq2.
      Qed.

      (* ...we infer that the generated schedule is indeed based on the construction function. *)
      Corollary sched_new_uses_construction_function:
        forall t,
          sched_new t = build_schedule sched_new t.
      Proof.
        by ins; apply service_dependent_schedule_construction,
                      sched_new_depends_only_on_service.
      Qed.
            
    End ScheduleConstruction.    

    (* Next, we prove that the generated schedule is well-formed. *)
    Section GeneratedScheduleIsValid.

      (* First, we show that scheduled jobs come from the arrival sequence. *)
      Lemma sched_newjobs_come_from_arrival_sequence:
        jobs_come_from_arrival_sequence sched_new arr_seq.
      Proof.
        rename H_jobs_come_from_arrival_sequence into FROM.
        move => j t /eqP SCHED.
        rewrite sched_new_uses_construction_function in SCHED.
        rewrite /build_schedule in SCHED.
        destruct (highest_priority_job sched_new t) as [j_hp|] eqn:HP; last by done.
        have ARRhp: arrives_in arr_seq j_hp.
        {
          rewrite /highest_priority_job in HP.
          apply seq_min_in_seq in HP.
          rewrite mem_filter in HP; move: HP => /andP [_ ARR].
          by eapply in_arrivals_implies_arrived, ARR.
        }
        destruct (sched_susp t) eqn:SUSP; last by case: SCHED => SAME; subst.
        by move: SCHED; case PEND: (_ && _); case => EQ; subst;
          first by apply (FROM j t); apply/eqP.
      Qed.

      (* Next, we show that jobs do not execute before their arrival times... *)
      Lemma sched_new_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched_new.
      Proof.
        move => j t /eqP SCHED.
        rewrite sched_new_uses_construction_function in SCHED.
        rewrite /build_schedule in SCHED.
        destruct (highest_priority_job sched_new t) as [j_hp|] eqn:HP; last by done.
        have IN: has_arrived job_arrival j_hp t.
        {
          suff IN: j_hp \in pending_jobs sched_new t.
            by rewrite mem_filter in IN; move: IN => /andP [/andP [ARR _] _].
          by apply: (seq_min_in_seq (higher_eq_priority t)).
        }
        destruct (sched_susp t) eqn:SUSP; last by move: SCHED; case => EQ; subst.
        move: SCHED; case: ifP; last by move => _; case => SAME; subst.
        by move => /andP [/andP [ARR _] _]; case => SAME; subst.
      Qed.

      (* ...nor longer than their execution costs. *)
      Lemma sched_new_completed_jobs_dont_execute:
        completed_jobs_dont_execute inflated_job_cost sched_new.
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
        rewrite -[inflated_job_cost _]addn0; apply leq_add; first by rewrite -EQ.
        rewrite leqn0 eqb0 /scheduled_at.
        rewrite sched_new_uses_construction_function.
        rewrite /build_schedule.
        destruct (highest_priority_job sched_new t) as [j_hp|] eqn:HP; last by done.
        rewrite /highest_priority_job in HP.
        destruct (sched_susp t) eqn:SUSP.
        {
          case: ifP => [PEND | NOTPEND].
          {
            apply/eqP; case => SAME; subst.
            move: PEND => /andP [PEND _].
              by rewrite /pending /completed_by EQ leqnn andbF in PEND.
          }
          {
            apply/eqP; case => SAME; subst.
            suff IN: j \in pending_jobs sched_new t.
            {
              rewrite mem_filter in IN; move: IN => /andP [/andP [_ NOTCOMP] _].
              by rewrite /completed_by EQ leqnn in NOTCOMP.
            }
            by apply: (seq_min_in_seq (higher_eq_priority t)).
          }
        }
        {
          apply/eqP; case => SAME; subst.
          suff IN: j \in pending_jobs sched_new t.
          {
            rewrite mem_filter in IN; move: IN => /andP [/andP [_ NOTCOMP] _].
            by rewrite /completed_by EQ leqnn in NOTCOMP.
          }
          by apply: (seq_min_in_seq (higher_eq_priority t)).
        }
      Qed.

      (* In addition, we prove that the schedule is (suspension-oblivious) work-conserving... *)
      Lemma sched_new_work_conserving:
        susp_oblivious.work_conserving job_arrival inflated_job_cost arr_seq sched_new.
      Proof.
        intros j t ARRj BACK.
        move: BACK => /andP [/andP [ARR NOTCOMP] NOTSCHED].
        rewrite /scheduled_at sched_new_uses_construction_function /build_schedule in NOTSCHED.
        rewrite /scheduled_at sched_new_uses_construction_function /build_schedule.
        destruct (highest_priority_job sched_new t) as [j_hp|] eqn:HP.
        {
          destruct (sched_susp t) as [j0 |] eqn:SUSP; last by exists j_hp.
          by case: ifP => [_ | _]; [exists j0 | exists j_hp].
        }
        {
          rewrite /highest_priority_job in HP.
          have IN: j \in pending_jobs sched_new t.
          {
            rewrite mem_filter /pending ARR NOTCOMP 2!andTb.
            by eapply arrived_between_implies_in_arrivals, ARR.
          }
          by apply seq_min_exists with (rel := higher_eq_priority t) in IN; rewrite HP eq_refl in IN.
        }
      Qed.

      (* ...and respects job priorities. *)
      Lemma sched_new_respects_policy:
        susp_oblivious.respects_JLDP_policy job_arrival inflated_job_cost
                                            arr_seq sched_new higher_eq_priority.
      Proof.
        rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL,
               H_priority_is_reflexive into REFL.
        move => j1 j2 t ARRj1 BACK /eqP SCHED.
        move: BACK => /andP [/andP [ARR NOTCOMP] NOTSCHED].
        rewrite /scheduled_at sched_new_uses_construction_function /build_schedule in NOTSCHED.
        rewrite /scheduled_at sched_new_uses_construction_function /build_schedule in SCHED.
        destruct (highest_priority_job sched_new t) as [j_hp|] eqn:HP; last by done.
        rewrite /highest_priority_job in HP.
        have ALL: forall j, j \in pending_jobs sched_new t -> higher_eq_priority t j_hp j.
        {
          intros j IN; apply seq_min_computes_min with (y := j) in HP; try (by done).
          intros x y; rewrite 2!mem_filter; move => /andP [_ INx] /andP [_ INy].
          by apply TOTAL; eapply in_arrivals_implies_arrived; eauto 1.
        }
        have IN: j1 \in pending_jobs sched_new t.
        {
          rewrite mem_filter /pending ARR NOTCOMP 2!andTb.
          by eapply arrived_between_implies_in_arrivals, ARR.
        }
        destruct (sched_susp t) as [j0|] eqn:SUSP;
          last by case: SCHED => SAME; subst; apply ALL; last by done.
        destruct (pending job_arrival inflated_job_cost sched_new j0 t
                          && higher_eq_priority t j0 j_hp) eqn:PEND;
          last by case: SCHED => SAME; subst; apply ALL.
        move: PEND => /andP [PEND HPj]; case: SCHED => SAME; subst.
        by apply: (TRANS _ j_hp); last by apply ALL.
      Qed.

      (* In addition, due to the copy step in the schedule construction, we show that in case
         there are multiple highest-priority jobs, we pick the same job as in the original
         schedule. *)
      Lemma sched_new_breaks_ties:
        forall j1 j2 t,
          higher_eq_priority t j1 j2 ->
          higher_eq_priority t j2 j1 ->
          scheduled_at sched_susp j1 t ->
          pending job_arrival inflated_job_cost sched_new j1 t ->
          scheduled_at sched_new j2 t ->
          j1 = j2.
      Proof.
        move => j1 j2 t HP1 HP2 /eqP SCHEDs PEND /eqP SCHEDn.
        rewrite sched_new_uses_construction_function /build_schedule in SCHEDn.
        destruct (highest_priority_job sched_new t) as [j_hp|] eqn:HP; last by done.
        destruct (sched_susp t) eqn:SUSP; last by done.
        case: SCHEDs => SAME; subst.
        rewrite PEND andTb in SCHEDn.
        move: SCHEDn; case: ifP => HP'; case => SAME; subst; first by done.
        by rewrite HP1 in HP'.
      Qed.
      
      (* To reason about schedulability, we now prove that the generated schedule
         preserves the service received by each job. *)
      Section Service.

        (* Recall the definitions of suspended job, cumulative service and
         cumulative suspension time in the suspension-aware schedule. *)
        Let job_suspended_at (sched: schedule Job) :=
          suspended_at job_arrival original_job_cost next_suspension sched.
        Let job_cumulative_suspension :=
          cumulative_suspension job_arrival original_job_cost next_suspension sched_susp. 
        Let job_service_with_suspensions := service sched_susp.

        (* Also recall the definition of cumulative service in the generated schedule. *)
        Let job_service_without_suspensions := service sched_new.

        (* We are going to prove that for any job j, at any time t, the service received by j
           in the generated schedule (without suspensions) is no larger than the sum of the
           cumulative service plus suspension time in the original schedule (with suspensions).
           The proof follows by induction on time. Since the base case is trivial, we focus
           on the inductive step.  *)
        Section InductiveStep.

          (* Assume that the claim we want to prove holds for the interval [0, t). *)
          Variable t: time.
          Hypothesis H_induction_hypothesis:
            forall j,
              arrives_in arr_seq j ->
              job_service_without_suspensions j t <=
              job_service_with_suspensions j t + job_cumulative_suspension j t.

          (* Now, let j be any job in arrival sequence. We are going to prove that the claim
           continues to hold for job j in the interval [0, t + 1). *)
          Variable j: Job.
          Hypothesis H_comes_from_arrival_sequence: arrives_in arr_seq j.

          (* If j has not arrived by time t, then the proof is trivial, ... *)
          Lemma reduction_inductive_step_not_arrived:
            ~~ has_arrived job_arrival j t ->
            job_service_without_suspensions j t.+1 <=
            job_service_with_suspensions j t.+1 + job_cumulative_suspension j t.+1.
          Proof.
            rewrite -ltnNge; intro NOTARR.
            rewrite /job_service_without_suspensions /job_service_with_suspensions
                    /service /service_during.
            rewrite (cumulative_service_before_job_arrival_zero job_arrival) //.
            by apply sched_new_jobs_must_arrive_to_execute.
          Qed.

          (* ...so let's assume instead that j has arrived by time t. *)
          Hypothesis H_j_has_arrived: has_arrived job_arrival j t.

          (* We begin by performing a case analysis on whether j has completed in the
           suspension-aware schedule. *)
          Section CompletedInSuspensionAwareSchedule.

            (* Case 1) If j has completed by time t in the suspension-aware schedule, ... *)
            Hypothesis H_j_has_completed:
              completed_by original_job_cost sched_susp j t.

            (* ...then it follows from the induction hypothesis that the service
             received by j is preserved up in the interval [0, t + 1). *)
            Lemma reduction_inductive_step_case1_completed:
              job_service_without_suspensions j t.+1 <=
              job_service_with_suspensions j t.+1 + job_cumulative_suspension j t.+1.
            Proof.
              rename H_j_has_completed into COMP, H_induction_hypothesis into IH.
              apply leq_trans with (n := original_job_cost j +
                                         total_suspension original_job_cost next_suspension j).
              { by apply leq_trans with (n := inflated_job_cost j);
                  first apply cumulative_service_le_job_cost,
                  sched_new_completed_jobs_dont_execute.
              }
              rewrite leq_add //; first by apply completion_monotonic with (t0 := t).
              apply completion_monotonic with (t' := t.+1) in COMP; try done.
              rewrite /job_cumulative_suspension.
                by rewrite -> cumulative_suspension_eq_total_suspension with
                    (job_cost := original_job_cost).
            Qed.

          End CompletedInSuspensionAwareSchedule.

          (* Next, consider the complementary case. *)
          Section PendingInSuspensionAwareSchedule.

            (* Case 2) Since job j has arrived by time t, let's assume that j has not completed
               by time t in the suspension-aware schedule, i.e., j is still pending. *)
            Hypothesis H_j_is_pending:
              ~~ completed_by original_job_cost sched_susp j t.

            (* Since we know from the induction hypothesis that the service received by j is
               preserved in the interval [0, t), now we only have to consider the state of job j
               at time t in both schedules. That is, we need to prove the following property:



                scheduled_at sched_new j t <=
                    job_suspended_at sched_susp j t + scheduled_at sched_susp j t.               *)

            (* If j is not scheduled in the suspension-oblivious schedule, then the claim follows. *)
            Lemma reduction_inductive_step_not_scheduled_in_new:
              ~~ scheduled_at sched_new j t ->
              scheduled_at sched_new j t <=
              job_suspended_at sched_susp j t + scheduled_at sched_susp j t.
            Proof.
                by case: scheduled_at.
            Qed.

            (* Likewise, if j is scheduled in the suspension-aware schedule, then the claim is also
               trivial. *)
            Lemma reduction_inductive_step_scheduled_in_susp:
              scheduled_at sched_susp j t ->
              scheduled_at sched_new j t <=
              job_suspended_at sched_susp j t + scheduled_at sched_susp j t.
            Proof.
                by move ->; case: scheduled_at; [by apply leq_addl | by rewrite addn1].
            Qed.

            (* Having proved the simple cases, let's now move to the harder case. *)
            Section NotScheduledInSuspensionAware.
              
              (* Assume that j is scheduled in the suspension-oblivious schedule, but
                 not in the suspension-aware schedule. *)
              Hypothesis H_j_scheduled_in_new: scheduled_at sched_new j t.
              Hypothesis H_j_not_scheduled_in_susp: ~~ scheduled_at sched_susp j t.

              (* It remains to show that j is suspended at time t in the suspension-aware schedule.
                 We are going to prove that by contradiction. *)
              Section ProofByContradiction.

                (* Assume that j it not suspended at time t in the suspension-aware schedule, ... *)
                Hypothesis H_j_is_not_suspended: ~~ job_suspended_at sched_susp j t. 

                (* ...which implies that j is backlogged at time t in the suspension-aware schedule. *)
                Lemma reduction_inductive_step_j_is_backlogged:
                  susp.backlogged job_arrival original_job_cost next_suspension sched_susp j t.
                Proof.
                  by repeat (apply/andP; split).
                Qed.

                (* By work conservation, there must be a scheduled job with higher or equal
                   priority in the suspension-aware schedule. *)
                Lemma reduction_inductive_step_exists_hep_job:
                  exists j_hp, arrives_in arr_seq j_hp /\
                               scheduled_at sched_susp j_hp t /\
                               higher_eq_priority t j_hp j.
                Proof.
                  rename H_work_conserving into WORKs, H_respects_priority into PRIOs,
                         H_jobs_come_from_arrival_sequence into FROM.
                  have BACKs := reduction_inductive_step_j_is_backlogged.
                  move: (BACKs) => BACKs'; apply WORKs in BACKs; last by done.
                  move: BACKs => [j_hp SCHEDhp]; exists j_hp.
                  split; first by apply (FROM j_hp t).
                  by split; last by apply PRIOs.
                Qed.

                (* Let j_hp be this job with higher-or-equal priority. *)
                Variable j_hp: Job.
                Hypothesis H_j_hp_comes_from_sequence: arrives_in arr_seq j_hp.
                Hypothesis H_j_hp_is_scheduled: scheduled_at sched_susp j_hp t.
                Hypothesis H_higher_or_equal_priority: higher_eq_priority t j_hp j.

                (* First, note that j and j_hp cannot be the same job, since j is not scheduled
                   in the suspension-aware schedule at time t. Moreover, since the generated
                   schedule breaks ties when there are multiple highest-priority jobs (by copying
                   the original schedule), it follows that the higher-priority job j_hp must have
                   completed earlier in the suspension-oblivious schedule. *)
                Lemma reduction_inductive_step_j_hp_completed_in_new:
                  completed_by inflated_job_cost sched_new j_hp t.
                Proof.
                  rename H_j_not_scheduled_in_susp into NOTSCHEDs, H_j_scheduled_in_new into SCHEDn.
                  move: H_j_hp_is_scheduled (H_j_hp_is_scheduled) => SCHEDhp PENDhp.
                  apply scheduled_implies_pending with (job_arrival0 := job_arrival)
                                   (job_cost := original_job_cost) in PENDhp; try (by done).
                  move: PENDhp => /andP [ARRhp _].
                  apply contraT; intro NOTCOMPhp.
                  have PENDhp: pending job_arrival inflated_job_cost sched_new j_hp t
                    by apply/andP; split.
                  destruct (boolP (scheduled_at sched_new j_hp t)) as [SCHEDhp' | NOTSCHEDhp'].
                  {
                    have SAME: j = j_hp by apply only_one_job_scheduled with (j1 := j) in SCHEDhp'.
                    by subst; rewrite SCHEDhp in NOTSCHEDs.
                  }
                  have BACKhp: backlogged job_arrival inflated_job_cost sched_new j_hp t by apply/andP.
                  have HP': higher_eq_priority t j j_hp by apply sched_new_respects_policy.
                  apply sched_new_breaks_ties in HP'; try (by done).
                  by subst; rewrite SCHEDn in NOTSCHEDhp'.
                Qed.

                (* However, recall from the induction hypothesis how the service in the two schedules
                   are related. From that, we can conclude that j_hp must have completed in the
                   suspension-aware schedule as well, ... *)
                Lemma reduction_inductive_step_j_hp_completed_in_susp:
                  completed_by original_job_cost sched_susp j_hp t.
                Proof.
                  have COMPNEW := reduction_inductive_step_j_hp_completed_in_new.
                  rename H_induction_hypothesis into IHt.
                  rewrite /completed_by. 
                  rewrite -(leq_add2r (total_suspension original_job_cost next_suspension j_hp)).
                  rewrite -/(inflated_job_cost _).
                  apply leq_trans with (n := job_service_without_suspensions j_hp t).
                  apply COMPNEW.
                  feed (IHt j_hp); first by done.
                  apply: (leq_trans IHt).
                    by rewrite leq_add2l; apply cumulative_suspension_le_total_suspension.
                Qed.

                (* ...which of course is a contradiction, since we assumed that j_hp was scheduled
                   in the the suspension-aware schedule at time t. *)
                Lemma reduction_inductive_step_contradiction: False.
                Proof.
                  have COMPhp' := reduction_inductive_step_j_hp_completed_in_susp.
                  rename H_j_hp_is_scheduled into SCHEDhp.
                  apply completed_implies_not_scheduled in COMPhp'; try (by done).
                  by rewrite SCHEDhp in COMPhp'.
                Qed.

              End ProofByContradiction.

            End NotScheduledInSuspensionAware.
            
            (* From the lemmas above, we infer that the claim to be proven holds if job j
               is pending in the suspension-aware schedule. *)
            Lemma reduction_inductive_step_case2_pending:
              job_service_without_suspensions j t.+1 <=
              job_service_with_suspensions j t.+1 + job_cumulative_suspension j t.+1.
            Proof.
              have CONTRA := reduction_inductive_step_contradiction.
              have HP := reduction_inductive_step_exists_hep_job.
              rename H_induction_hypothesis into IHt.
              rewrite /job_service_without_suspensions /job_service_with_suspensions
                      /job_cumulative_suspension /cumulative_suspension
                      /cumulative_suspension_during /service /service_during /service_at.
              rewrite !big_nat_recr //=.
              rewrite -addnA [scheduled_at sched_susp _ _ + _]addnC !addnA -addnA.
              apply leq_add; first by apply IHt.
              destruct (boolP (scheduled_at sched_new j t)) as [SCHEDn |]; last by done.
              destruct (boolP (scheduled_at sched_susp j t)) as [SCHEDs | NOTSCHEDs];
                [by apply leq_addl | rewrite addn0].
              apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
              apply contraT; intro NOTSUSP.
              specialize (HP NOTSCHEDs NOTSUSP); specialize (CONTRA SCHEDn NOTSCHEDs NOTSUSP).
              move: HP => [j_hp [INhp [SCHEDhp HP]]].
              by exfalso; apply CONTRA with (j_hp := j_hp).
            Qed.
            
          End PendingInSuspensionAwareSchedule.
          
        End InductiveStep.

        (* Using the proof by induction, we show that the service received by any
           job j at any time t is preserved in the suspension-aware schedule. *)
        Theorem suspension_oblivious_preserves_service:
          forall j t,
            arrives_in arr_seq j ->
            job_service_without_suspensions j t <= job_service_with_suspensions j t
                                                   + job_cumulative_suspension j t.
        Proof.
          have CASE1 := reduction_inductive_step_case1_completed.
          have CASE2 := reduction_inductive_step_case2_pending.
          move => j t; move: t j.
          induction t;
            first by ins; rewrite /job_service_without_suspensions/service/service_during big_geq.
          intros j ARRj.
          destruct (boolP (has_arrived job_arrival j t)) as [ARR | NOTARR];
            last by apply reduction_inductive_step_not_arrived.
          destruct (boolP (completed_by original_job_cost sched_susp j t)) as [COMP | NOTCOMP];
            first by apply CASE1.
          by apply CASE2.
        Qed.

        (* As a corollary, we show that if a job has completed in the suspension-oblivious
           schedule, it must have completed in the suspension-aware schedule as well. *)
        Corollary suspension_oblivious_preserves_completion:
          forall j t,
            arrives_in arr_seq j ->
            completed_by inflated_job_cost sched_new j t ->
            completed_by original_job_cost sched_susp j t.
        Proof.
          have COMP := sched_new_completed_jobs_dont_execute.
          have SERV := suspension_oblivious_preserves_service.
          intros j t ARRj COMPLETED.
          unfold completed_by in *.
          rewrite -(leq_add2r (total_suspension original_job_cost next_suspension j)).
          rewrite -/(inflated_job_cost j).
          apply leq_trans with (service sched_new j t); first by done.
          apply: (leq_trans (SERV j t ARRj)); rewrite leq_add2l.
            by apply cumulative_suspension_le_total_suspension.
        Qed.

      End Service.

    End GeneratedScheduleIsValid.
    
    (* To conclude, based on the definition of schedulability, ...*)
    Let schedulable_without_suspensions :=
      job_misses_no_deadline job_arrival inflated_job_cost job_deadline sched_new.
    Let schedulable_with_suspensions :=
      job_misses_no_deadline job_arrival original_job_cost job_deadline sched_susp.

    (* ...we prove that if no job misses a deadline in the suspension-oblivious schedule, ... *)
    Hypothesis H_schedulable_without_suspensions:
      forall j,
        arrives_in arr_seq j ->
        schedulable_without_suspensions j.

    (* ...then no job misses a deadline in the suspension-aware schedule. *)
    Corollary suspension_oblivious_preserves_schedulability:
      forall j,
        arrives_in arr_seq j ->
        schedulable_with_suspensions j.
    Proof.
      rename H_schedulable_without_suspensions into SCHED.
      by intros j ARRj; apply suspension_oblivious_preserves_completion, SCHED.
    Qed.

  End Reduction.

End ReductionToBasicSchedule.