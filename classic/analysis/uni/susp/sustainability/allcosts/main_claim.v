Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.schedule.uni.response_time
               prosa.classic.model.schedule.uni.sustainability.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.valid_schedule
               prosa.classic.model.schedule.uni.susp.build_suspension_table
               prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.analysis.uni.susp.sustainability.allcosts.reduction
               prosa.classic.analysis.uni.susp.sustainability.allcosts.reduction_properties.
Require Import prosa.classic.model.schedule.uni.transformation.construction.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we use the reduction we derived to show the weak sustainability with
   job costs and varying suspension times in the dynamic suspension model. *)
Module SustainabilityAllCostsProperty.
  
  Import ScheduleWithSuspensions Suspension Priority SuspensionIntervals
         PlatformWithSuspensions ResponseTime Sustainability
         ValidSuspensionAwareSchedule.

  Module reduction := SustainabilityAllCosts.
  Module reduction_prop := SustainabilityAllCostsProperties.
  
  Section SustainabilityProperty.
    
    Context {Task: eqType}.
    Context {Job: eqType}.
    
    (** Defining the task model *)

    Variable higher_eq_priority: JLDP_policy Job.
    Hypothesis H_priority_reflexive: JLDP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_transitive: JLDP_is_transitive higher_eq_priority.

    Variable job_task: Job -> Task.
    Variable task_suspension_bound: Task -> duration.

    (* First, we state all properties about suspension, ... *)
    Let satisfies_suspension_properties (params: seq (job_parameter Job)) :=
      dynamic_suspension_model (return_param JOB_COST params) job_task
                               (return_param JOB_SUSPENSION params) task_suspension_bound.

    (* ...all properties of the schedule, ... *)
    Let satisfies_schedule_properties (params: seq (job_parameter Job)) (arr_seq: arrival_sequence Job)
                                      (sched: schedule Job) :=
      let job_arrival := return_param JOB_ARRIVAL params in
      let job_cost := return_param JOB_COST params in
      let job_suspension_duration := return_param JOB_SUSPENSION params in
        jobs_come_from_arrival_sequence sched arr_seq /\
        jobs_must_arrive_to_execute job_arrival sched /\
        completed_jobs_dont_execute job_cost sched /\
        work_conserving job_arrival job_cost job_suspension_duration arr_seq sched /\
        respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq
                             sched higher_eq_priority /\
        respects_self_suspensions job_arrival job_cost job_suspension_duration sched.

    (* ...and all properties of the arrival sequence. *)
    Let satisfies_arrival_sequence_properties (params: seq (job_parameter Job))
                                              (arr_seq: arrival_sequence Job) :=
      arrival_times_are_consistent (return_param JOB_ARRIVAL params) arr_seq /\
      JLDP_is_total arr_seq higher_eq_priority.

    (* Then, we define the task model as the combination of such properties. *)
    Let belongs_to_task_model (params: seq (job_parameter Job))
                              (arr_seq: arrival_sequence Job) (sched: schedule Job) :=
      satisfies_arrival_sequence_properties params arr_seq /\
      satisfies_schedule_properties params arr_seq sched /\
      satisfies_suspension_properties params.
    
    (** Sustainability Claim *)

    (* We use as schedulability property the notion of response-time bound, i.e., we are
       going to show that improving job parameters leads to "no worse response times". *)
    Variable R: time.
    Let response_time_bounded_by_R (params: seq (job_parameter Job)) (sched: schedule Job) (j: Job) :=
      is_response_time_bound_of_job (return_param JOB_ARRIVAL params)
                                    (return_param JOB_COST params) sched j R.

    (* Next, we recall the definition of weakly-sustainable policy with job costs
       and varying suspension times... *)
    Let all_params := [:: JOB_ARRIVAL; JOB_COST; JOB_SUSPENSION].
    Let sustainable_param := JOB_COST.
    Let variable_params := [:: JOB_SUSPENSION].
    Let has_better_sustainable_param (cost cost': Job -> time) := forall j, cost j >= cost' j.
    
    Let weakly_sustainable_with_job_costs_and_variable_suspension_times :=
      weakly_sustainable all_params response_time_bounded_by_R belongs_to_task_model
                         sustainable_param has_better_sustainable_param variable_params.

    (* ...and prove that it holds for this scheduling policy and task model. *)
    Theorem policy_is_weakly_sustainable:
      weakly_sustainable_with_job_costs_and_variable_suspension_times.
    Proof.
      intros params good_params CONS CONS' ONLY BETTER VSCHED good_arr_seq good_sched good_j BELONGS.
      split_conj BELONGS; split_conj BELONGS; split_conj BELONGS0; split_conj BELONGS1.
      set job_arrival := return_param JOB_ARRIVAL good_params.
      unfold differ_only_by in *.
      have EQarr: job_arrival = return_param JOB_ARRIVAL params.
      {
        move: CONS CONS' => [UNIQ [IFF _]] [UNIQ' [IFF' _]].
        have ARR: JOB_ARRIVAL \in labels_of params by apply IFF.
        have ARR': JOB_ARRIVAL \in labels_of good_params by apply IFF'.
        move: ARR ARR' => /mapP2 [p IN EQ] => /mapP2 [p' IN' EQ'].
        symmetry in EQ; symmetry in EQ'.
        have EQp := found_param_label params p JOB_ARRIVAL UNIQ IN EQ.
        have EQp' := found_param_label good_params p' JOB_ARRIVAL UNIQ' IN' EQ'.
        specialize (ONLY p p' IN IN').
        feed_n 2 ONLY; [by rewrite EQ | by rewrite EQ |].
        rewrite ONLY EQp' in EQp.
        by inversion EQp.
      }
      set good_cost := return_param JOB_COST good_params.
      set bad_cost := return_param JOB_COST params.
      set good_suspension := return_param JOB_SUSPENSION good_params.
      set bad_sched := reduction.sched_new job_arrival good_cost good_arr_seq higher_eq_priority
                                           good_sched bad_cost good_j R.
      set reduced_suspension_duration := reduction.reduced_suspension_duration job_arrival good_cost
        good_arr_seq higher_eq_priority good_sched good_suspension bad_cost good_j R.
      set bad_params := [:: param JOB_ARRIVAL job_arrival; param JOB_COST bad_cost;
                            param JOB_SUSPENSION reduced_suspension_duration].  
      apply reduction_prop.sched_new_response_time_of_job_j with (arr_seq := good_arr_seq)
        (higher_eq_priority0 := higher_eq_priority) (inflated_job_cost := bad_cost);
        try done.
      feed (VSCHED bad_params).
      {
        split; first by done.
        split; first by intros l; split;
          move => IN; rewrite /= 2!in_cons mem_seq1 in IN;
          move: IN => /orP [/eqP EQ | /orP [/eqP EQ | /eqP EQ]]; rewrite EQ.
        intros l IN; move: CONS => [_ [IFF CONS]].
        specialize (CONS l IN); apply IFF in CONS.
        rewrite 2!in_cons mem_seq1 in CONS.
        by move: CONS => /orP [/eqP EQ | /orP [/eqP EQ | /eqP EQ]]; rewrite EQ.
      }
      rewrite -/bad_sched.
      apply VSCHED with (arr_seq := good_arr_seq).
      {
        intros P1 P2 IN1 IN2 EQ NOTIN; simpl in IN2.
        move: CONS CONS' => [UNIQ _] [UNIQ' [IN' _]].
        move: IN2 => [EQ2a | [EQ2c | [EQ2s | BUG]]]; try done; first last.
        - by rewrite EQ -EQ2s in NOTIN.
        - by rewrite -EQ2c; apply found_param_label; rewrite // EQ -EQ2c.
        - by rewrite -EQ2a EQarr; apply found_param_label; rewrite // EQ -EQ2a. 
      }
      {
        repeat split; try (by done).
        - by apply reduction_prop.sched_new_jobs_come_from_arrival_sequence.
        - by apply reduction_prop.sched_new_jobs_must_arrive_to_execute.
        - by apply reduction_prop.sched_new_completed_jobs_dont_execute.
        - by apply reduction_prop.sched_new_work_conserving.
        - by apply reduction_prop.sched_new_respects_policy.
        - by apply reduction_prop.sched_new_respects_self_suspensions.
        intros j0. 
        apply leq_trans with (n := total_suspension good_cost good_suspension j0); last by done.
        by apply reduction_prop.sched_new_has_shorter_total_suspension.
      }
    Qed.

    End SustainabilityProperty.
  
End SustainabilityAllCostsProperty.