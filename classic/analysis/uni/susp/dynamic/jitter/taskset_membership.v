Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.platform
               prosa.classic.model.schedule.uni.susp.valid_schedule.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule
               prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_taskset_generation.
Require Import prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction
               prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file we prove that the jitter-aware schedule sched_jitter used in the
   reduction is an instance of the jitter-aware task set that we analyze. *)
Module TaskSetMembership.

  Import SporadicTaskset Suspension Priority ValidSuspensionAwareSchedule
         ScheduleWithSuspensions ResponseTime PlatformWithSuspensions.

  Module reduction := JitterScheduleConstruction.
  Module ts_gen := JitterTaskSetGeneration.
  Module sust := SustainabilitySingleCost.
  Module sust_prop := SustainabilitySingleCostProperties.
  Module valid_sched := ValidSuspensionAwareSchedule.
  Module job_susp := Job.
  Module job_jitter := JobWithJitter.
  
  Section ProvingMembership.

    Context {Task: eqType}.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (** Basic Setup & Setting*)
    
    (* Let ts be any suspension-aware task set. *)
    Variable ts: seq Task.

    (* Consider any job arrival sequence with consistent, duplicate-free arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* ...where jobs come from the task set. *)
    Hypothesis H_jobs_come_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* ...and the associated job and task costs. *)
    Variable job_cost: Job -> time.
    Variable task_cost: Task -> time.

    (* Assume that jobs and tasks have associated suspension times. *)
    Variable job_suspension_duration: job_suspension Job.
    Variable task_suspension_bound: Task -> time.

    (* Assume any FP policy that is reflexive, transitive and total... *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: FP_is_total_over_task_set higher_eq_priority ts.
    Let job_higher_eq_priority := FP_to_JLDP job_task higher_eq_priority.

    (* Recall the definition of a valid suspension-aware schedule. *)
    Let is_valid_suspension_aware_schedule :=
      valid_suspension_aware_schedule job_arrival arr_seq job_higher_eq_priority
                                      job_suspension_duration.
    
    (* Next, consider any valid suspension-aware schedule of this arrival sequence.
       (Note: see prosa.classic.model.schedule.uni.susp.valid_schedule.v for details) *)
    Variable sched_susp: schedule Job.
    Hypothesis H_valid_schedule:
      valid_suspension_aware_schedule job_arrival arr_seq job_higher_eq_priority
                                      job_suspension_duration job_cost sched_susp.
    
    (* Recall the definition of response-time bounds in sched_susp. *)
    Let task_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched_susp.
    Let job_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_job job_arrival job_cost sched_susp.

    (** Analysis Setup *)
    
    (* Let tsk_i be any task to be analyzed... *)
    Variable tsk_i: Task.
    Hypothesis H_tsk_in_ts: tsk_i \in ts.

    (* ...and let j be any job of this task. *)
    Variable j: Job.
    Hypothesis H_j_arrives: arrives_in arr_seq j.
    Hypothesis H_job_of_tsk_i: job_task j = tsk_i.

    (* Also recall the definition of task response-time bound with any job cost and schedule... *)
    Let is_task_response_time_bound_with job_cost sched :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    
    (* ...and the definition of higher-or-equal-priority tasks (other than tsk_i). *)
    Let other_hep_task tsk_other := higher_eq_priority tsk_other tsk_i && (tsk_other != tsk_i).

    (* Next, assume that for each of those higher-or-equal-priority tasks (other than tsk_i),
       we know a response-time bound R that is valid across all suspension-aware schedules of ts. *)
    Variable R: Task -> time.   
    Hypothesis H_valid_response_time_bound_of_hp_tasks_in_all_schedules:
      forall job_cost sched,
        is_valid_suspension_aware_schedule job_cost sched ->
        forall tsk_hp,
          tsk_hp \in ts ->
          other_hep_task tsk_hp ->
          is_task_response_time_bound_with job_cost sched tsk_hp (R tsk_hp).
    
    (* The existence of response-time bounds across all schedules implies that we can find
       actual response times of the higher-priority jobs in sched_susp... *)
    Definition actual_response_time (j_hp: Job) : time :=
      [pick-min r <= R (job_task j_hp) |
       job_response_time_in_sched_susp_bounded_by j_hp r].

    (* ...and show that they are valid... *)
    Corollary actual_response_time_is_valid:
      forall j_hp,
        arrives_in arr_seq j_hp ->
        other_hep_task (job_task j_hp) ->
        job_response_time_in_sched_susp_bounded_by j_hp (actual_response_time j_hp).
    Proof.
      rename H_valid_response_time_bound_of_hp_tasks_in_all_schedules into RESPhp,
             H_jobs_come_from_taskset into FROM.
      intros j_hp ARRhp HP.
      rewrite /actual_response_time.
      apply pick_min_holds; last by done.
      exists (R (job_task j_hp)); split; first by done.
      by apply RESPhp; try (by done); first by apply FROM.
    Qed.

    (* ...and tight. *)
    Corollary actual_response_time_is_minimum:
      forall j_hp r_hp,
        arrives_in arr_seq j_hp ->
        other_hep_task (job_task j_hp) ->
        job_response_time_in_sched_susp_bounded_by j_hp r_hp ->
        actual_response_time j_hp <= r_hp.
    Proof.
      rename H_valid_response_time_bound_of_hp_tasks_in_all_schedules into RESPhp,
             H_jobs_come_from_taskset into FROM.
      intros j_hp r_hp ARRhp HP RESP.
      case (leqP r_hp (R (job_task j_hp))) => [LT | GE].
      {
        rewrite /actual_response_time.
        apply pick_min_holds;
          last by intros x RESPx _ MINx; rewrite -ltnS in LT; apply (MINx (Ordinal LT)).
        exists (R (job_task j_hp)); split; first by done.
        by apply RESPhp; try (by done); first by apply FROM.
      }
      {
        apply leq_trans with (n := (R (job_task j_hp))); last by apply ltnW. 
        rewrite -ltnS /actual_response_time.
        apply pick_min_ltn.
        exists (R (job_task j_hp)); split; first by done.
        by apply RESPhp; try (by done); first by apply FROM.
      }
    Qed.
    
    (** Instantiation of the Reduction *)
    
    (* Using the actual response time of higher-priority jobs as a parameter, we construct
       the jitter-aware schedule from sched_susp. *)
    Let inflated_job_cost := reduction.inflated_job_cost job_cost job_suspension_duration j. 
    Let job_jitter := reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j
                                           actual_response_time.

    (* We also recall the parameters of the generated jitter-aware task set. *)
    Let inflated_task_cost := ts_gen.inflated_task_cost task_cost task_suspension_bound tsk_i.
    Let task_jitter := ts_gen.task_jitter task_cost higher_eq_priority tsk_i R.

    (** Proof of Task Set Membership *)
    
    (* Now we proceed with the main claim. We are going to show that the job parameters in the
       jitter-aware schedule sched_susp are an instance of the task set parameters. *)

    (* Assume that the original costs are positive... *)
    Hypothesis H_positive_costs:
      forall j, arrives_in arr_seq j -> job_cost j > 0.
    
    (* ...and no larger than the task costs. *)
    Hypothesis H_job_cost_le_task_cost:
      forall j,
        arrives_in arr_seq j ->
        job_cost j <= task_cost (job_task j).

    (* Also assume that job suspension times are bounded by the task suspension bounds. *)
    Hypothesis H_dynamic_suspensions:
      dynamic_suspension_model job_cost job_task job_suspension_duration task_suspension_bound.
  
    (* We begin by showing that the inflated job costs remain positive... *)
    Section JobCostPositive.

      Lemma ts_membership_inflated_job_cost_positive:
        forall j, arrives_in arr_seq j -> inflated_job_cost j > 0.
      Proof.
        intros j0 ARR0.
        apply leq_trans with (n := job_cost j0); first by apply H_positive_costs.
        rewrite /inflated_job_cost /reduction.inflated_job_cost.
        by case: ifP => _; first by apply leq_addr.
      Qed.
      
    End JobCostPositive.

    (* ...and no larger than the inflated task costs. *)
    Section JobCostBoundedByTaskCost.

      Lemma ts_membership_inflated_job_cost_le_inflated_task_cost:
        forall j,
          arrives_in arr_seq j ->
          inflated_job_cost j <= inflated_task_cost (job_task j).
      Proof.
        intros j' ARR'.
        rewrite /inflated_job_cost /inflated_task_cost /reduction.inflated_job_cost
                /ts_gen.inflated_task_cost.
        case: ifP => [/eqP SAME | NEQ]; subst.
        {
          rewrite eq_refl; apply leq_add; last by apply H_dynamic_suspensions.
          by apply H_job_cost_le_task_cost.
        }
        case: ifP => [SAMEtsk | DIFFtsk]; last by apply H_job_cost_le_task_cost.
        apply leq_trans with (n := task_cost (job_task j')); last by apply leq_addr.
        by apply H_job_cost_le_task_cost.
      Qed.

    End JobCostBoundedByTaskCost.

    (* Finally, we show that the job jitter in sched_susp is upper-bounded by the task jitter.
       This only concerns higher-priority jobs, which are assigned non-zero jitter to
       compensate suspension times. *)
    Section JobJitterBoundedByTaskJitter.

      (* Let any_j be any job from the arrival sequence. *)
      Variable any_j: Job.
      Hypothesis H_any_j_arrives: arrives_in arr_seq any_j.

      (* Since most parts of the proof are trivial, we focus on the more complicated case
         of higher-priority jobs. *)
      Section JitterOfHigherPriorityJobs.

        (* Suppose that any_j is a higher-or-equal-priority job from some task other than tsk_i. *)
        Hypothesis H_higher_priority: higher_eq_priority (job_task any_j) tsk_i.
        Hypothesis H_different_task: job_task any_j != tsk_i.

        (* Recall that we want to prove that job_jitter any_j <= task_jitter (job_task any_j).
           By definition, this amounts to showing that:
                actual_response_time any_j - job_cost any_j <=
                    R (job_task any_j) - task_cost (job_task any_j). *)

        (* The proof follows by a sustainability argument based on the following reduction. *)
        
        (* By inflating the cost of any_j to its worst-case execution time...*)
        Let higher_cost_wcet j' :=
          if j' == any_j then task_cost (job_task any_j) else job_cost j'.

        (* ...we construct a new suspension-aware schedule sched_susp_highercost where the response
           time of any_j is as large as in the original schedule sched_susp.
           (For more details, see analysis/uni/susp/sustainability/cost. ) *)
        Let sched_susp_highercost :=
          sust.sched_susp_highercost job_arrival arr_seq job_higher_eq_priority
                                     sched_susp job_suspension_duration higher_cost_wcet.

        (* Next, recall the definition of task response-time bounds in sched_susp_highercost. *)
        Let task_response_time_in_sched_susp_highercost_bounded_by :=
          is_response_time_bound_of_task job_arrival higher_cost_wcet job_task arr_seq
                                         sched_susp_highercost.

        (* Since the response-time bounds R are valid across all suspension-aware schedules
           of task set ts, they are also valid in sched_susp_higher_cost. *)
        Remark response_time_bound_in_sched_susp_highercost:
          forall tsk_hp,
            tsk_hp \in ts ->
            other_hep_task tsk_hp ->
            task_response_time_in_sched_susp_highercost_bounded_by tsk_hp (R tsk_hp).
        Proof.
          rename H_valid_response_time_bound_of_hp_tasks_in_all_schedules into RESPhp,
                 H_jobs_come_from_taskset into FROM, H_valid_schedule into VALID.
          split_conj VALID.
          feed (RESPhp higher_cost_wcet sched_susp_highercost).
          {
            repeat split.
            - by apply sust_prop.sched_susp_highercost_jobs_come_from_arrival_sequence.
            - by apply sust_prop.sched_susp_highercost_jobs_must_arrive_to_execute.
            - by apply sust_prop.sched_susp_highercost_completed_jobs_dont_execute.
            - by apply sust_prop.sched_susp_highercost_work_conserving.
            - apply sust_prop.sched_susp_highercost_respects_policy; try (by done).
              -- by intros t j1 j2 j3; apply H_priority_is_transitive. 
              -- by intros j1 j2 t ARR1 ARR2; apply/orP; apply H_priority_is_total; apply FROM.
            - by apply sust_prop.sched_susp_highercost_respects_self_suspensions.
          }
          by intros tsk_hp IN Ohp; by apply RESPhp.
        Qed.
        
        (* Finally, by comparing the two schedules, we prove that the difference between the
           actual response time and job cost is bounded by the difference between the
           response-time bound and the task cost. *)
        Lemma ts_membership_difference_in_response_times:
          actual_response_time any_j - job_cost any_j <=
            R (job_task any_j) - task_cost (job_task any_j).
        Proof.
          have VALIDr := actual_response_time_is_valid.
          have MINr := actual_response_time_is_minimum.
          have RESPhp := response_time_bound_in_sched_susp_highercost.
          rename H_jobs_come_from_taskset into FROM, H_valid_schedule into VALIDSCHED.
          split_conj VALIDSCHED.
          apply leq_trans with (n := R (job_task any_j) - higher_cost_wcet any_j);
            last by apply leq_sub2l; rewrite /higher_cost_wcet eq_refl.
          apply sust_prop.sched_susp_highercost_incurs_more_interference with
            (job_arrival0 := job_arrival) (arr_seq0 := arr_seq) (sched_susp0 := sched_susp)
            (higher_eq_priority0:=job_higher_eq_priority)
            (job_suspension_duration0 := job_suspension_duration); try (by done).
          - by intros t j1; apply H_priority_is_reflexive.
          - by rewrite /higher_cost_wcet eq_refl; apply H_job_cost_le_task_cost.
          - by move => j' NEQ; apply negbTE in NEQ; rewrite /higher_cost_wcet NEQ.
          - by apply H_positive_costs.
          - by apply VALIDr; try (by done); apply/andP; split.
          - by intros r' RESP; apply MINr; try (by done); first by apply/andP; split.
          - by apply RESPhp; try (by done); [apply FROM | apply/andP; split].
        Qed.
        
      End JitterOfHigherPriorityJobs.

      (* Using the lemmas above, we conclude that the job jitter parameter is
         upper-bounded by the task jitter for any job in the arrival sequence. *)
      Lemma ts_membership_job_jitter_le_task_jitter:
        job_jitter any_j <= task_jitter (job_task any_j).
      Proof.
        have DIFF := ts_membership_difference_in_response_times.
        rewrite /job_jitter /task_jitter /reduction.job_jitter /ts_gen.task_jitter H_job_of_tsk_i.
        case: ifP => // /andP [HP' NEQ].
        rewrite /minn; case: ifP => [LTdist | GEdist]; last by apply DIFF.
        case (leqP (job_arrival j) (job_arrival any_j)) => [AFTER | BEFORE];
          first by apply leq_trans with (n := 0); first rewrite leqn0 subn_eq0.
        apply leq_trans with (n := actual_response_time any_j - job_cost any_j); first by apply ltnW.
        by apply DIFF.
      Qed.

    End JobJitterBoundedByTaskJitter.

  End ProvingMembership.

End TaskSetMembership.