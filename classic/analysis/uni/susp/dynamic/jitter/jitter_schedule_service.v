Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority prosa.classic.model.suspension.
Require Import prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.schedule.uni.schedulability prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.jitter.schedule
               prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals
               prosa.classic.model.schedule.uni.susp.schedule
               prosa.classic.model.schedule.uni.susp.platform
               prosa.classic.model.schedule.uni.susp.valid_schedule.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule
               prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(* In this file, we compare the service received by the analyzed job j after
   reducing the suspension-aware schedule to a jitter-aware schedule. *)
Module JitterScheduleService.

  Import Job SporadicTaskset Suspension Priority SuspensionIntervals Workload Service
         UniprocessorScheduleWithJitter Schedulability ResponseTime TaskArrival
         ScheduleConstruction ValidSuspensionAwareSchedule.

  Module basic := schedule.UniprocessorSchedule.
  Module susp := ScheduleWithSuspensions.
  Module jitter_aware := Platform.
  Module susp_aware := PlatformWithSuspensions.
  Module job_jitter := JobWithJitter.
  Module reduction := JitterScheduleConstruction.
  Module reduction_prop := JitterScheduleProperties.

  (* We begin by providing the initial setup and definitions in Sections 1 to 5.
     The main results are proven later in Sections 6-(A) to 6-(C). *)
  Section ProvingScheduleProperties.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (** 1) Basic Setup & Setting *)
    
    (* Let ts be any task set. *)
    Variable ts: seq Task.

    (* Next, consider any consistent, duplicate-free job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* ...where all jobs come from task set ts. *)
    Hypothesis H_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Since we consider real-time tasks, assume that job deadlines are equal to task deadlines. *)
    Hypothesis H_job_deadlines_equal_task_deadlines:
      forall j, arrives_in arr_seq j -> job_deadline j = task_deadline (job_task j).

    (* Also assume that tasks have constrained deadlines and that jobs arrive sporadically.
       (Note: this is required to bound the interference of previous jobs of the analyzed task.) *)
    Hypothesis H_constrained_deadlines:
      constrained_deadline_model task_period task_deadline ts.
    Hypothesis H_sporadic_arrivals:
      sporadic_task_model task_period job_arrival job_task arr_seq.
    
    (* Consider any FP policy that is reflexive, transitive and total. *)
    Variable higher_eq_priority: FP_policy Task.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    Hypothesis H_priority_is_total: FP_is_total_over_task_set higher_eq_priority ts.
    Let job_higher_eq_priority := FP_to_JLDP job_task higher_eq_priority.
    
    (* Assume that jobs have associated suspension times. *)
    Variable job_suspension_duration: job_suspension Job.

    (* Next, consider any valid suspension-aware schedule of this arrival sequence.
       (Note: see definition in prosa.classic.model.schedule.uni.susp.valid_schedule.v) *)
    Variable sched_susp: schedule Job.
    Hypothesis H_valid_schedule:
      valid_suspension_aware_schedule job_arrival arr_seq job_higher_eq_priority
                                      job_suspension_duration job_cost sched_susp.
    
    (* Finally, recall the notion of job response-time bound and deadline miss in sched_susp. *)
    Let job_response_time_in_sched_susp_bounded_by :=
      is_response_time_bound_of_job job_arrival job_cost sched_susp.
    Let job_misses_no_deadline_in_sched_susp :=
      job_misses_no_deadline job_arrival job_cost job_deadline sched_susp.
    
    (** 2) Analysis Setup *)
    
    (* Recall that we are going to analyze the response time of some job after
       applying the reduction to the jitter-aware schedule as defined in
       prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule. *)
       
    (* Let j be the job to be analyzed. *)
    Variable j: Job.
    Hypothesis H_from_arrival_sequence: arrives_in arr_seq j.
    Let arr_j := job_arrival j.
    
    (* Let R_j be any value that we want to prove to be a response-time bound for job j in sched_susp.
       Note that in the context of this proof, R_j also delimits the length of the schedules
       that we are going to analyze, i.e., we only care about the interval [0, arr_j + R_j). *)
    Variable R_j: time.
    
    (* Next, recall the definition of higher-or-equal-priority tasks (other than j's task). *)
    Let other_hep_task tsk_other :=
      higher_eq_priority tsk_other (job_task j) && (tsk_other != job_task j).

    (* Assume that each job of a higher-or-equal-priority task (other than j's task) is
       associated a response-time bound R_hp.
       (Note: this follows from analyzing the higher-priority tasks in a previous step.) *)
    Variable R_hp: Job -> time.
    Hypothesis H_bounded_response_time_of_hp_jobs:
      forall j_hp,
        arrives_in arr_seq j_hp ->
        other_hep_task (job_task j_hp) ->
        job_response_time_in_sched_susp_bounded_by j_hp (R_hp j_hp).

    (* Also assume that all the previous jobs of same task as j do not miss any
       deadlines in sched_susp.
       (Note: this is an induction hypothesis that is easily obtained when analyzing the
        sequence of jobs of the same task.) *)
    Hypothesis H_no_deadline_misses_for_previous_jobs:
      forall j0,
        arrives_in arr_seq j0 ->
        job_arrival j0 < job_arrival j ->
        job_task j0 = job_task j ->
        job_misses_no_deadline_in_sched_susp j0.
    
    (** 3) Instantiation of the Reduction *)

    (* Having stated all the properties of the suspension-aware schedule, now we recall
       the construction of the jitter-aware schedule and the corresponding job parameters. *)
    Let sched_jitter := reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority
                                               job_cost job_suspension_duration j R_hp.
    Let inflated_job_cost := reduction.inflated_job_cost job_cost job_suspension_duration j.
    Let job_jitter := reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp.

    (* By the end of this file, we are going to show that if job j completes by time (arr_j + R_j)
       in sched_jitter, then it also completes by time (arr_j + R_j) in sched_susp.
       The argument is based on the fact that the service of higher-or-equal-priority jobs is moved
       from the interval [0, arr_j) to the interval [arr_j, arr_j + R_j), when we introduce jitter.
       
       The proofs are structured in the three final sections. In Section 6-A, we prove that
       sched_jitter provides provides less service for higher-or-equal-priority jobs during [0, arr_j).
       In Section B, we prove that sched_jitter provides more service for higher-or-equal-priority
       jobs during [arr_j, arr_j + R). In Section 6-C, we conclude with the main theorem that compares
       the response time of job j in both schedules. *)

    (** 4) Setup for Next Sections *)

    (* For simplicity, let's define some local names... *)
    Let actual_job_arrival := actual_arrival job_arrival job_jitter.
    Let job_arrived_before := arrived_before job_arrival.
    Let job_has_arrived := has_arrived job_arrival.
    Let job_has_actually_arrived := jitter_has_passed job_arrival job_jitter.
    Let job_completed_in_sched_jitter := completed_by inflated_job_cost sched_jitter.
       
    (* ...and also recall definitions related to the suspension-aware schedule. *)
    Let job_suspended_at :=
      suspended_at job_arrival job_cost job_suspension_duration sched_susp.
    Let job_cumulative_suspension :=
      cumulative_suspension_during job_arrival job_cost job_suspension_duration sched_susp.
    Let job_completed_in_sched_susp := completed_by job_cost sched_susp.
    Let backlogged_in_sched_susp := susp.backlogged job_arrival job_cost
                                                    job_suspension_duration sched_susp.

    (* Since we'll have to reason about sets of arriving jobs with and without jitter,
       let's use simpler names for those as well. *)
    Let arrivals := jobs_arrived_between arr_seq.
    Let actual_arrivals := actual_arrivals_between job_arrival job_jitter arr_seq.

    (* Because we are dealing with a bounded scheduling window, we also identify all
       job arrivals (with and without jitter) in the interval [0, arr_j + R_j). *)
    Let arrivals_before_end_of_interval := arrivals 0 (arr_j + R_j).
    Let actual_arrivals_before_end_of_interval := actual_arrivals 0 (arr_j + R_j).

    (* Next, by checking jobs priorities, ... *)
    Let other_higher_eq_priority_job j_hp :=
      higher_eq_priority (job_task j_hp) (job_task j) && (j_hp != j).
      
    (* ...we identify the workload of higher-or-equal-priority jobs (other than j)
       that arrive in any interval [t1, t2), in the original schedule,... *)
    Definition workload_of_other_hep_jobs_in_sched_susp t1 t2 :=
      workload_of_jobs job_cost (arrivals t1 t2) other_higher_eq_priority_job.

    (* ... and also the workload of higher-or-equal priority jobs (other than j)
       with actual arrival time in the interval [t1, t2), in the jitter-aware schedule. *)
    Definition workload_of_other_hep_jobs_in_sched_jitter t1 t2 :=
      workload_of_jobs inflated_job_cost (actual_arrivals t1 t2) other_higher_eq_priority_job.     

    (* Next, we recall the cumulative service of all higher-or-equal-priority
       jobs (other than j) that arrived in the interval [0, arr_j + R_j),
       received in a given interval [t1, t2) in the original schedule. *)
    Definition service_of_other_hep_jobs_in_sched_susp t1 t2 :=
      service_of_jobs sched_susp arrivals_before_end_of_interval other_higher_eq_priority_job t1 t2.
      
    (* Similarly, we recall the cumulative service of all higher-or-equal-priority
       jobs (other than j) with actual arrival time in the interval [0, arr_j + R_j),
       received in a given interval [t1, t2) in the jitter-aware schedule. *)
    Definition service_of_other_hep_jobs_in_sched_jitter t1 t2 :=
      service_of_jobs sched_jitter actual_arrivals_before_end_of_interval
                      other_higher_eq_priority_job t1 t2.

    (** 5) Auxiliary Lemmas *)

    (* Before moving to the main results, let's prove some auxiliary lemmas about service/workload. *)
    Section AuxiliaryLemmas.
      
      (* First, we prove that if all higher-or-equal-priority jobs have completed by
         some time t in the jitter-aware schedule, then the service received
         by those jobs up to time t amounts to the requested workload. *)
      Section ServiceEqualsWorkload.

        (* Let t be any time no later than (arr_j + R_j)... *)
        Variable t: time.
        Hypothesis H_before_end_of_interval: t <= arr_j + R_j.

        (* ...in which all higher-or-equal-priority jobs (other than j) have completed. *)
        Hypothesis H_workload_has_finished:
          forall j_hp,
            arrives_in arr_seq j_hp ->
            actual_arrival_before job_arrival job_jitter j_hp t -> 
            other_higher_eq_priority_job j_hp ->
            job_completed_in_sched_jitter j_hp t.

        (* Then, the service received by all those jobs in the interval [0, t) amounts to
           the workload requested by them in the interval [0, t). *)
        Lemma jitter_reduction_service_equals_workload_in_jitter:
          service_of_other_hep_jobs_in_sched_jitter 0 t >=
          workload_of_other_hep_jobs_in_sched_jitter 0 t.
        Proof.
          rename H_workload_has_finished into WORK.
          rewrite /workload_of_other_hep_jobs_in_sched_jitter
                  /workload_of_jobs /service_of_other_hep_jobs_in_sched_jitter
                  /actual_arrivals_before_end_of_interval /actual_arrivals_before.
          set act := actual_arrivals.
          set t1 := arr_j; set t2 := arr_j + R_j.
          set hep := other_higher_eq_priority_job.
          set Sj := service_during sched_jitter.
          apply leq_trans with (n := \sum_(j0 <- act 0 t | hep j0) Sj j0 0 t); last first.
          {
            rewrite big_mkcond [X in _ <= X]big_mkcond.
            apply leq_sum_sub_uniq; first by apply actual_arrivals_uniq.
            intros j0 IN0.
            by apply actual_arrivals_between_sub with (t3 := 0) (t4 := t).
          }
          apply leq_sum_seq; rewrite /act /actual_arrivals; intros j0 IN0 HP0.
          apply WORK; try done.
          - by apply in_actual_arrivals_between_implies_arrived in IN0.
          - by apply in_actual_arrivals_implies_arrived_before in IN0.
        Qed.

      End ServiceEqualsWorkload.

      (* Next, we prove a lemma showing that service in the suspension-aware schedule
         is bounded by the workload. *)
      Section ServiceBoundedByWorkload.

        (* Consider any time t <= arr_j + R_j. *)
        Variable t: time.
        Hypothesis H_before_end_of_interval: t <= arr_j + R_j.

        (* Then, the service of all jobs with higher-or-equal-priority that arrive in
           the interval [0, arr_j + R_j), received in the interval [0, t), is no
           larger than the workload of all jobs with higher-or-equal-priority that
           are released in the interval [0, t), in the suspension-aware schedule. *)
        Lemma jitter_reduction_service_in_sched_susp_le_workload:
          service_of_other_hep_jobs_in_sched_susp 0 t <=
          workload_of_other_hep_jobs_in_sched_susp 0 t.
        Proof.
          move: (H_valid_schedule) => [FROMarr [MUSTARRs [COMPs _]]].
          rename H_before_end_of_interval into LTt.
          rewrite /workload_of_other_hep_jobs_in_sched_susp /workload_of_jobs
                  /service_of_other_hep_jobs_in_sched_susp /service_of_jobs
                  /arrivals_before_end_of_interval /jobs_arrived_before.
          set all := arrivals.
          set t1 := arr_j; set t2 := arr_j + R_j.
          set hep := other_higher_eq_priority_job.
          set Ss := service_during sched_susp.
          apply leq_trans with (n := \sum_(j0 <- all 0 t | hep j0) Ss j0 0 t);
            last by apply leq_sum; intros j0 _; apply cumulative_service_le_job_cost.
          rewrite exchange_big [X in _ <= X]exchange_big /=.
          apply leq_sum_nat; move => t' /= LT' _.
          apply leq_trans with (n := \sum_(j0 <- all 0 t2 | hep j0 &&
                                                   (scheduled_at sched_susp j0 t')) 1).
          {
            rewrite big_mkcond [X in _ <= X]big_mkcond.
            rewrite /service_at; apply leq_sum; intros j0 _.
            by case: hep; case SCHED': scheduled_at.
          }
          apply leq_trans with (n := \sum_(j0 <- all 0 t | hep j0 &&
                                      (scheduled_at sched_susp j0 t')) 1); last first.
          {
            rewrite big_mkcond [X in _ <= X]big_mkcond.
            rewrite /service_at; apply leq_sum; intros j0 _.
            by case: hep; case SCHED': scheduled_at.
          }
          rewrite -big_filter -[X in _ <= X]big_filter.
          apply leq_sum_sub_uniq; first by rewrite filter_uniq //; eapply arrivals_uniq; eauto 1.
          intros j0; rewrite 2!mem_filter; move => /andP [/andP [HP0 SCHED0] IN0].
          rewrite HP0 SCHED0 /=.
          have ARRin0: arrives_in arr_seq j0 by apply FROMarr in SCHED0.
          have ARR0: job_arrival j0 <= t' by apply MUSTARRs.
          apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival);
            try (by done).
          by apply: (leq_ltn_trans _ LT').
        Qed.

      End ServiceBoundedByWorkload.

    End AuxiliaryLemmas.
    
    (** ** 6-(A) Less High-Priority Service Before the Arrival of Job j in sched_jitter  *)

    (* In this section we prove that before the arrival of job j, the cumulative service
       received by other higher-or-equal-priority is no larger in the jitter-aware schedule
       than in the suspension-aware schedule. *)
    Section LessServiceBeforeArrival.

      (* In fact, we can prove that the service is not larger for each higher-or-equal-priority
         job in isolation. *)
      Section LessServiceForEachJob.

          (* Let j_hp be any higher-or-equal-priority job (different from j). *)
          Variable j_hp: Job.
          Hypothesis H_arrives: arrives_in arr_seq j_hp.
          Hypothesis H_higher_or_equal_priority: other_higher_eq_priority_job j_hp.

          (* For simplicity, let's define some local names. *)
          Let arr_hp := job_arrival j_hp.
          Let cost_hp := job_cost j_hp.
          Let Rhp := R_hp j_hp.

          (* Using a series of case analyses, we are going to prove that
               service sched_jitter j_hp t <= service sched_susp j_hp t. *)
          Section Case1.

            (* Case 1. Assume that j_hp is a job from the same task as j. *)
            Hypothesis H_same_task: job_task j_hp = job_task j.

            (* Due to constrained deadlines, we can infer that previous jobs of the same task
               complete in sched_susp before j arrives. Because these jobs do not have inflated
               costs, they cannot receive more service in sched_jitter before the arrival of j. *)
            Lemma jitter_reduction_less_job_service_before_interval_case1:
              service sched_jitter j_hp arr_j <= service sched_susp j_hp arr_j.
            Proof.
              move: (H_valid_schedule) => [_ [MUSTARRs [COMPs _]]].
              rename H_no_deadline_misses_for_previous_jobs into NOMISS,
                     H_constrained_deadlines into DL, H_jobs_from_taskset into FROM,
                     H_sporadic_arrivals into SPO.
              move: H_higher_or_equal_priority => /andP [HP NEQ].
              case (ltnP arr_hp arr_j) => [BEFORE | AFTER]; last first.
              {
                rewrite /service /service_during.
                rewrite (cumulative_service_before_jitter_is_zero job_arrival job_jitter) //;
                  first by eapply reduction_prop.sched_jitter_jobs_execute_after_jitter; eauto 1.
                move: H_same_task => /eqP SAMEtsk; apply negbF in SAMEtsk.
                by rewrite /actual_arrival /job_jitter /reduction.job_jitter HP SAMEtsk /= addn0.
              }
              apply leq_trans with (n := inflated_job_cost j_hp).
              {
                apply cumulative_service_le_job_cost.
                by apply reduction_prop.sched_jitter_completed_jobs_dont_execute.
              }
              rewrite /inflated_job_cost /reduction.inflated_job_cost.
              apply negbTE in NEQ; rewrite NEQ.
              apply completion_monotonic with (t := arr_hp + job_deadline j_hp); last by apply NOMISS. 
              rewrite H_job_deadlines_equal_task_deadlines //.
              apply leq_trans with (n := arr_hp + task_period (job_task j_hp));
                first by rewrite leq_add2l DL // FROM.
              apply SPO; try (by done); last by apply ltnW.
              by intros SAME; subst; rewrite eq_refl in NEQ.
            Qed.
            
          End Case1.

          Section Case2.
 
            (* Case 2. Assume that j_hp is a job from another task,... *)
            Hypothesis H_different_task: job_task j_hp != job_task j.

            (* ...that is released (with jitter) no earlier than the arrival of j. *)
            Hypothesis H_released_no_earlier: arr_j <= actual_job_arrival j_hp.

            (* Since j_hp cannot execute in sched_jitter, the claim trivially holds. *)
            Lemma jitter_reduction_less_job_service_before_interval_case2:
              service sched_jitter j_hp arr_j <= service sched_susp j_hp arr_j.
            Proof.
              rename H_different_task into DIFFtask.
              move: H_higher_or_equal_priority => /andP [HP NEQ].
              rewrite /service /service_during.
              by rewrite (cumulative_service_before_jitter_is_zero job_arrival job_jitter) //;
              first by eapply reduction_prop.sched_jitter_jobs_execute_after_jitter; eauto 1.
            Qed.
            
          End Case2.

          Section Case3.
            
            (* Case 3. Assume that j_hp is a job from another task,... *)
            Hypothesis H_different_task: job_task j_hp != job_task j.

            (* ...and that (arr_j - arr_hp < arr_j - cost_hp). *)
            Hypothesis H_distance_is_smaller:
              arr_j - arr_hp < Rhp - cost_hp.

            (* By definition, the jitter of j_hp is set so that it arrives after j.
               Since j_hp cannot execute in sched_jitter, the claim follows trivially. *)
            Lemma jitter_reduction_less_job_service_before_interval_case3:
              service sched_jitter j_hp arr_j <= service sched_susp j_hp arr_j.
            Proof.
              rename H_higher_or_equal_priority into HEP, H_distance_is_smaller into MIN.
              move: (HEP) => /andP [HP NEQ].
              rewrite /service /service_during.
              rewrite (cumulative_service_before_jitter_is_zero job_arrival job_jitter) //;
                first by eapply reduction_prop.sched_jitter_jobs_execute_after_jitter; eauto 1.
              rewrite /actual_arrival /job_jitter /reduction.job_jitter HP H_different_task /=.
              rewrite /minn MIN.
              case (leqP (job_arrival j) (job_arrival j_hp)) => [AFTER | BEFORE];
                first by apply: (leq_trans AFTER); apply leq_addr.
              by rewrite subnKC; last by apply ltnW.
            Qed.

          End Case3.
          
          Section Case4.

            (* Case 4. Assume that j_hp is a job from another task... *)
            Hypothesis H_different_task: job_task j_hp != job_task j.
           
            (* ...and that j_hp completes in sched_susp before j arrives. *)
            Hypothesis H_completes_before_j_arrives: arr_hp + Rhp <= arr_j.

            (* Since j_hp completes early in sched_susp and receives maximum service, it cannot
               receive more service in sched_jitter before j arrives, thus the claim holds. *)
            Lemma jitter_reduction_less_job_service_before_interval_case4:
              service sched_jitter j_hp arr_j <= service sched_susp j_hp arr_j.
            Proof.
              rename H_higher_or_equal_priority into HEP,
                     H_bounded_response_time_of_hp_jobs into RESPhp.
              move: (HEP) => /andP [HP NEQ].                
              apply leq_trans with (n := service sched_susp j_hp (arr_hp + Rhp));
                last by apply extend_sum.
              apply leq_trans with (n := cost_hp);
                last by apply RESPhp; last by apply/andP; split.
              apply leq_trans with (n := inflated_job_cost j_hp);
                last by rewrite /inflated_job_cost /reduction.inflated_job_cost -[_==_]negbK NEQ.
              apply cumulative_service_le_job_cost.
              by apply reduction_prop.sched_jitter_completed_jobs_dont_execute.          
            Qed.

          End Case4.

          Section Case5.

            (* Case 5. Assume that j_hp is a job from another task,... *)
            Hypothesis H_different_task: job_task j_hp != job_task j.

            (* ...that is released (with jitter) before the arrival of j. *)
            Hypothesis H_released_before: actual_job_arrival j_hp < arr_j.

            (* Also assume that (arr_j < arr_hp + Rhp) and (Rhp - costhp <= arr_j - arr_hp). *)
            Hypothesis H_j_hp_completes_after_j_arrives: arr_j < arr_hp + Rhp.
            Hypothesis H_distance_is_not_smaller: Rhp - cost_hp <= arr_j - arr_hp.

            (* Note that in this case the jitter of job j_hp is set to (Rhp - cost_hp). *)
            Remark jitter_reduction_jitter_equals_R_minus_cost:
              job_jitter j_hp = Rhp - cost_hp.
            Proof.
              rename H_higher_or_equal_priority into HEP, H_different_task into DIFFtask.
              move: (HEP) => /andP [HP NEQ].
              rewrite /job_jitter /reduction.job_jitter HP DIFFtask /= /minn.
              by rewrite ltnNge H_distance_is_not_smaller /=.
            Qed.

            (* Since j_hp is released late in sched_jitter with "slack" (Rhp - cost_hp), even
               if it executes at full speed, it cannot beat sched_susp in terms of service.
               Therefore, the claim also holds. *)
            Lemma jitter_reduction_less_job_service_before_interval_case5:
              service sched_jitter j_hp arr_j <= service sched_susp j_hp arr_j.
            Proof.
              move: (H_valid_schedule) => [_ [MUSTARRs [COMPs _]]].
              have JITdef := jitter_reduction_jitter_equals_R_minus_cost.
              rename H_higher_or_equal_priority into HEP,
                     H_bounded_response_time_of_hp_jobs into RESPhp.
              move: (HEP) => /andP [HP NEQ].
              set arr_hp' := actual_job_arrival j_hp.
              set cost_hp' := inflated_job_cost j_hp.
              have JIT: job_jitter j_hp = Rhp - cost_hp by apply JITdef.
              apply leq_trans with (n := cost_hp - (arr_hp + Rhp - arr_j)); last first.
              {
                rewrite /cost_hp leq_subLR.
                apply leq_trans with (n := service sched_susp j_hp (arr_hp + Rhp));
                  first by apply RESPhp; last by apply/andP; split.
                rewrite /service /service_during.
                apply leq_trans with (n := \sum_(arr_j <= t' < arr_hp+Rhp)
                                            1 + service sched_susp j_hp arr_j);
                  last by apply leq_add; first by simpl_sum_const.
                rewrite -> big_cat_nat with (n := arr_j); [simpl | by done | by apply ltnW]. 
                by rewrite addnC; apply leq_add; first by apply leq_sum; intros t0 _; apply leq_b1.
              }
              {
                have AFTERj := reduction_prop.sched_jitter_jobs_execute_after_jitter job_arrival
                               job_task arr_seq higher_eq_priority job_cost job_suspension_duration.
                rewrite /service /service_during.
                rewrite (ignore_service_before_jitter job_arrival job_jitter) //;
                  [| by eapply AFTERj; eauto 1 | by apply ltnW].
                apply leq_trans with (n := \sum_(arr_hp' <= t0 < arr_j) 1);
                  first by apply leq_sum; intros t0 _; apply leq_b1.
                simpl_sum_const; rewrite /arr_hp' /actual_job_arrival /actual_arrival JIT.
                have LEcost: cost_hp <= Rhp.
                {
                  apply leq_trans with (n := service sched_susp j_hp (arr_hp + Rhp));
                    first by apply RESPhp; last by apply/andP;split.
                 apply leq_trans with (n := \sum_(arr_hp <= t' < arr_hp + Rhp) 1);
                  last by simpl_sum_const; rewrite addKn.
                  rewrite /service /service_during.
                  rewrite (ignore_service_before_arrival job_arrival) //; last by apply leq_addr.
                  by apply leq_sum; intros t0 _; apply leq_b1.
                }
                rewrite addnBA; last by done.
                rewrite subnBA; last by apply: (leq_trans LEcost); apply leq_addl.
                rewrite subnBA; last by apply ltnW.
                by apply leq_sub2r; rewrite addnC.
              }
            Qed.
            
          End Case5.

          (** **** Main Claim of Section (A) *)
      
          (* Using the case analysis above, we conclude that before the arrival of job j,
             any higher-or-equal-priority job receives no more service in the jitter-aware
             schedule than in the suspension-aware schedule. *)
          Lemma jitter_reduction_less_job_service_before_interval:
            service sched_jitter j_hp arr_j <= service sched_susp j_hp arr_j.
          Proof.
            have CASE1 := jitter_reduction_less_job_service_before_interval_case1.
            have CASE2 := jitter_reduction_less_job_service_before_interval_case2.
            have CASE3 := jitter_reduction_less_job_service_before_interval_case3.
            have CASE4 := jitter_reduction_less_job_service_before_interval_case4.
            have CASE5 := jitter_reduction_less_job_service_before_interval_case5.
            have AFTERj := reduction_prop.sched_jitter_jobs_execute_after_jitter job_arrival job_task
                     arr_seq higher_eq_priority job_cost job_suspension_duration j _ R_hp.
            feed AFTERj; try (by done).
            case (boolP (job_task j_hp == job_task j)) => [/eqP SAME | DIFFtsk]; first by apply CASE1. 
            case (leqP arr_j (actual_job_arrival j_hp)) => [LEarr | GTarr]; first by apply CASE2.
            case (ltnP (arr_j - arr_hp) (Rhp - cost_hp)) => [LTdiff | GEdiff]; first by apply CASE3.
            case (leqP (arr_hp + Rhp) arr_j) => [LEarrj | GTarrj]; first by apply CASE4.
            by apply CASE5.
          Qed.

      End LessServiceForEachJob.

      (* Since the result about service applies to each individual job, we can prove that
         it also holds for the cumulative service of all higher-or-equal-priority jobs. *)
      Corollary jitter_reduction_less_service_before_the_interval:
        service_of_other_hep_jobs_in_sched_jitter 0 arr_j <=
        service_of_other_hep_jobs_in_sched_susp 0 arr_j.
      Proof.
        rewrite /service_of_other_hep_jobs_in_sched_jitter
                /service_of_other_hep_jobs_in_sched_susp
                /actual_arrivals_before_end_of_interval /arrivals_before_end_of_interval
                /actual_arrivals_before /jobs_arrived_before.
        set hep := other_higher_eq_priority_job.
        set Ss := service_during sched_susp.
        set t2 := arr_j + R_j.
        apply leq_trans with (n := \sum_(j_hp <- actual_arrivals 0 t2 | hep j_hp) Ss j_hp 0 arr_j).
        {
          apply leq_sum_seq; rewrite /actual_arrivals; intros j0 IN0 HEP0.
          apply jitter_reduction_less_job_service_before_interval; try (by done).
          by apply in_actual_arrivals_between_implies_arrived in IN0.
        }
        {
          rewrite big_mkcond [X in _ <= X]big_mkcond /actual_arrivals /=.
          apply leq_sum_sub_uniq; first by apply actual_arrivals_uniq.
          by intros j0; rewrite !mem_filter /=; move => /andP [_ IN0].
        }
      Qed.
      
    End LessServiceBeforeArrival.

    (** ** 6-(B) More High-Priority Service After the Arrival of Job j in sched_jitter  *)

    (* So far, we have shown that the higher-or-equal-priority jobs receives less service
       in the jitter-aware schedule during [0, arr_j). Recall that our final goal is to show
       that all this service is actually moved into the interval [arr_j, arr_j + R_j) and
       converted into interference for the job j being analyzed.
       In this section, we reason about what happens to high-priority jobs after job j arrives. *)
    Section MoreServiceAfterArrival.

      (* First, we show that the workload is conserved at every point in the interval
         [arr_j, arr_j + R_j). *)
      Section Conservation.

        (* Consider any time t >= arr_j (no earlier than the arrival of j). *)
        Variable t: time.
        Hypothesis H_no_earlier_than_j: t >= arr_j.

        (* Then, we prove that every job that arrives up to time t is also released
           in the jitter-aware schedule up to time t. *)
        Lemma jitter_reduction_actual_arrival_before_end_of_interval:
          forall j_hp,
            other_higher_eq_priority_job j_hp ->
            job_arrival j_hp <= t ->
            actual_job_arrival j_hp <= t.
        Proof.
          move => j_hp /andP [HP NEQ] ARRhp.
          set arr_hp := job_arrival j_hp.
          set cost_hp := job_cost j_hp.
          rewrite /actual_job_arrival /actual_arrival /job_jitter /reduction.job_jitter HP /=.
          case: ifP => [NEQtsk | /eqP SAMEtsk]; last by rewrite addn0. 
          case (ltnP (arr_j - arr_hp) (R_hp j_hp - cost_hp)) => [MINl | MINr].
          {
            rewrite /minn MINl.
            case (leqP arr_hp arr_j) => [BEFORE | AFTER]; first by rewrite subnKC //.
            by apply leq_trans with (n := arr_hp + (arr_hp - arr_hp));
              [by rewrite leq_add2l leq_sub2r // ltnW | by rewrite subnn addn0].
          }
          {
            rewrite /minn ltnNge MINr /=.
            apply leq_trans with (n := arr_hp + (arr_j - arr_hp)); first by rewrite leq_add2l.
            case (leqP arr_hp arr_j) => [BEFORE | AFTER]; first by rewrite subnKC //.
            by apply leq_trans with (n := arr_hp + (arr_hp - arr_hp));
              [by rewrite leq_add2l leq_sub2r // ltnW | by rewrite subnn addn0].
          }
        Qed.

        (* This implies that the workload is conserved up to time t (inclusive). That is,
           in the jitter-aware schedule, there's always as much (high-priority) work to be
           executed as in the original schedule. *)
        Lemma jitter_reduction_workload_conservation_inside_interval:
            workload_of_other_hep_jobs_in_sched_susp 0 t.+1 <=
            workload_of_other_hep_jobs_in_sched_jitter 0 t.+1. 
        Proof.
          rewrite /workload_of_other_hep_jobs_in_sched_susp
                  /workload_of_other_hep_jobs_in_sched_jitter /workload_of_jobs.
          set all := arrivals; set act := actual_arrivals.
          set hep := other_higher_eq_priority_job.
          apply leq_trans with (n := \sum_(j0 <- all 0 t.+1 | hep j0) inflated_job_cost j0).
          {
            apply leq_sum_seq; rewrite /all /arrivals; move => j0 IN0 /andP [_ NEQ].
            by apply negbTE in NEQ; rewrite /inflated_job_cost /reduction.inflated_job_cost NEQ //.
          }
          apply leq_trans with (n := \sum_(j0 <- all 0 t.+1 | hep j0 &&
                (actual_job_arrival j0 < t.+1)) inflated_job_cost j0); last first.
          {
            rewrite -big_filter -[X in _ <= X]big_filter.
            apply leq_sum_sub_uniq;
              first by rewrite filter_uniq //; eapply arrivals_uniq; eauto 1.
            intros j0; rewrite !mem_filter /=.
            by move => /andP [/andP [HP LT] IN]; rewrite HP LT IN.
          }
          rewrite big_mkcond [X in _ <= X]big_mkcond /=.
          apply leq_sum_seq; intros j0 IN0 _.
          case HP: hep; simpl; last by done.
          case: (leqP _ _); last by done.
          intros BUG; exfalso; rewrite leqNgt in BUG; move: BUG => /negP BUG; apply: BUG.
          apply jitter_reduction_actual_arrival_before_end_of_interval; try (by done).
          by eapply in_arrivals_implies_arrived_before in IN0; eauto 1.
        Qed.

      End Conservation.

      (* Since the higher-or-equal-priority jobs receive no more service in the jitter-aware
         schedule during [0, arr_j), and because the workload is conserved, we prove next
         that those jobs receive no less service in the jitter-aware schedule in the interval
         [arr_j, arr_j + R_j).  *)
      Section MoreServiceInsideTheInterval.

        (* The claim we need to show is presented next. The proof follows by induction on
           the interval length d:
             forall d,
               d <= R_j ->
               service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + d) <= 
               service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + d).    *)           

        (* Since the base case of the induction is trivial, we focus on the inductive step. *)
        Section InductiveStep.

          (* By strong induction, assume that for a given interval length d < R_j, ... *)
          Variable d: time.
          Hypothesis H_d_lt_R: d < R_j.

          (* ...the higher-or-equal-priority jobs (other than j) received as much service in
             the jitter-aware schedule during [arr_j, arr_j + d) as in the suspension-aware
             schedule. *)
          Hypothesis H_induction_hypothesis:
            service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + d) <=
            service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + d).

          (* Now we must prove that the claim continues to hold for interval [arr_j, arr_j + d + 1):

              service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + d + 1) <=
              service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + d + 1). *)

          (* The proof begins with a case analysis on whether there are pending
             higher-or-equal-priority jobs at time (arr_j + d) in the jitter-aware schedule. *)
          Section NoPendingJobs.

            (* Case 1. Assume that all higher-or-equal-priority jobs (other than j) whose jitter
                       has passed by time (arr_j + d) are already complete at time (arr_j + d)
                       in the jitter-aware schedule. *)
            Hypothesis H_all_jobs_completed_in_sched_jitter:
              forall j_hp,
                arrives_in arr_seq j_hp ->
                other_higher_eq_priority_job j_hp ->
                job_has_actually_arrived j_hp (arr_j + d) ->
                job_completed_in_sched_jitter j_hp (arr_j + d). 

            (* First, we show that the service received in the suspension-aware schedule
               during [arr_j, arr_j + d + 1) is bounded by the difference between the
               requested workload and the service received prior to the arrival of job j. *)
            Lemma jitter_reduction_convert_service_to_workload:
              service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + d + 1) <=
                workload_of_other_hep_jobs_in_sched_susp 0 (arr_j + d + 1)
                - service_of_other_hep_jobs_in_sched_susp 0 arr_j.
            Proof.
              have LEWORKs := jitter_reduction_service_in_sched_susp_le_workload.
              rewrite /service_of_other_hep_jobs_in_sched_jitter
                      /actual_arrivals_before_end_of_interval /actual_arrivals_before.
              rewrite /service_of_other_hep_jobs_in_sched_susp /service_of_jobs
                      /arrivals_before_end_of_interval /jobs_arrived_before.
              set all := arrivals; set act := actual_arrivals.
              set hep := other_higher_eq_priority_job.
              set Ss := service_during sched_susp.
              set Sj := service_during sched_jitter.
              set SCHs := scheduled_at sched_susp.
              set SCHj := scheduled_at sched_jitter.
              set SUSP := job_cumulative_suspension.
              set Wj := workload_of_other_hep_jobs_in_sched_jitter.
              set Ws := workload_of_other_hep_jobs_in_sched_susp.
              set t1 := arr_j.
              set t2 := arr_j + R_j.
              rewrite exchange_big [X in _ <= _ - X]exchange_big /= /service_at.
              rewrite -/SCHs -/SCHj addnS addn0.
              set TSs := fun a b => \sum_(a <= t0 < b)
                                           \sum_(j_hp <- all 0 t2 | hep j_hp) SCHs j_hp t0.
              set TSj := fun a b => \sum_(a <= t0 < b)
                                         \sum_(j_hp <- act 0 t2 | hep j_hp) SCHj j_hp t0.
              rewrite -/(TSs t1 (t1 + d).+1) -/(TSs 0 t1).
              rewrite subh3 //.
              rewrite addnC -big_cat_nat //=;
                last by apply leq_trans with (n := t1 + d); first by apply leq_addr.
              by rewrite exchange_big; apply LEWORKs; rewrite ltn_add2l.
            Qed.

            (* Because of workload conservation, we show that the workload in the suspension-aware
               schedule is bounded by the workload in the jitter-aware schedule. *)
            Lemma jitter_reduction_compare_workload:
                  workload_of_other_hep_jobs_in_sched_susp 0 (arr_j + d + 1)
                          - service_of_other_hep_jobs_in_sched_susp 0 arr_j
               <= workload_of_other_hep_jobs_in_sched_jitter 0 (arr_j + d + 1)
                          - service_of_other_hep_jobs_in_sched_susp 0 arr_j.
            Proof.
              have CONS := jitter_reduction_workload_conservation_inside_interval.
              rewrite /service_of_other_hep_jobs_in_sched_jitter
                      /actual_arrivals_before_end_of_interval /actual_arrivals_before.
              rewrite /service_of_other_hep_jobs_in_sched_susp /service_of_jobs
                      /arrivals_before_end_of_interval /jobs_arrived_before.
              set all := arrivals; set act := actual_arrivals.
              set hep := other_higher_eq_priority_job.
              set Ss := service_during sched_susp.
              set Sj := service_during sched_jitter.
              set SCHs := scheduled_at sched_susp.
              set SCHj := scheduled_at sched_jitter.
              set SUSP := job_cumulative_suspension.
              set Wj := workload_of_other_hep_jobs_in_sched_jitter.
              set Ws := workload_of_other_hep_jobs_in_sched_susp.
              set t1 := arr_j.
              set t2 := arr_j + R_j.
              rewrite exchange_big /= /service_at.
              rewrite -/SCHs -/SCHj addnS addn0.
              set TSs := fun a b => \sum_(a <= t0 < b)
                                           \sum_(j_hp <- all 0 t2 | hep j_hp) SCHs j_hp t0.
              set TSj := fun a b => \sum_(a <= t0 < b)
                                         \sum_(j_hp <- act 0 t2 | hep j_hp) SCHj j_hp t0.
              rewrite -/(TSs t1 (t1 + d).+1) -/(TSs 0 t1).
              apply leq_trans with (n := Ws 0 (t1 + d).+1 - TSs 0 t1); first by done.
              by rewrite leq_sub2r //; apply CONS, leq_addr.
            Qed.

            (* Since the higher-or-equal-priority jobs received less service in the
               jitter-aware schedule in the interval [0, arr_j), we can compare the
               service in the two schedules. *)
            Lemma jitter_reduction_compare_service:
                  workload_of_other_hep_jobs_in_sched_jitter 0 (arr_j + d + 1)
                          - service_of_other_hep_jobs_in_sched_susp 0 arr_j
               <= workload_of_other_hep_jobs_in_sched_jitter 0 (arr_j + d + 1)
                         - service_of_other_hep_jobs_in_sched_jitter 0 arr_j.
            Proof.
              have LEserv := jitter_reduction_less_service_before_the_interval.
              rewrite /service_of_other_hep_jobs_in_sched_jitter
                      /actual_arrivals_before_end_of_interval /actual_arrivals_before.
              rewrite /service_of_other_hep_jobs_in_sched_susp /service_of_jobs
                      /arrivals_before_end_of_interval /jobs_arrived_before.
              set all := arrivals; set act := actual_arrivals.
              set hep := other_higher_eq_priority_job.
              set Ss := service_during sched_susp.
              set Sj := service_during sched_jitter.
              set SCHs := scheduled_at sched_susp.
              set SCHj := scheduled_at sched_jitter.
              set SUSP := job_cumulative_suspension.
              set Wj := workload_of_other_hep_jobs_in_sched_jitter.
              set Ws := workload_of_other_hep_jobs_in_sched_susp.
              set t1 := arr_j.
              set t2 := arr_j + R_j.
              rewrite exchange_big [X in _ <= _ - X]exchange_big /= /service_at.
              rewrite -/SCHs -/SCHj addnS addn0.
              set TSs := fun a b => \sum_(a <= t0 < b)
                                           \sum_(j_hp <- all 0 t2 | hep j_hp) SCHs j_hp t0.
              set TSj := fun a b => \sum_(a <= t0 < b)
                                         \sum_(j_hp <- act 0 t2 | hep j_hp) SCHj j_hp t0.
              rewrite -/(TSs t1 (t1 + d).+1) -/(TSs 0 t1).
              rewrite leq_sub2l //.
              rewrite /TSj /TSs exchange_big [X in _ <= X]exchange_big /=.
              by apply LEserv.
            Qed.

            (* Having inferred that the difference between the workload and service is that
               large in the jitter-aware schedule, we can convert this difference back to
               service received in the interval [arr_j, arr_j + d + 1] in sched_jitter. *)
            Lemma jitter_reduction_convert_workload_to_service:
              workload_of_other_hep_jobs_in_sched_jitter 0 (arr_j + d + 1) -
                service_of_other_hep_jobs_in_sched_jitter 0 arr_j <=
              service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + d + 1).
            Proof.
              have EQWORKj := jitter_reduction_service_equals_workload_in_jitter.
              rename H_all_jobs_completed_in_sched_jitter into ALL.
              rewrite /service_of_other_hep_jobs_in_sched_jitter
                      /actual_arrivals_before_end_of_interval /actual_arrivals_before.
              rewrite /service_of_other_hep_jobs_in_sched_susp /service_of_jobs
                      /arrivals_before_end_of_interval /jobs_arrived_before.
              set all := arrivals; set act := actual_arrivals.
              set hep := other_higher_eq_priority_job.
              set Ss := service_during sched_susp.
              set Sj := service_during sched_jitter.
              set SCHs := scheduled_at sched_susp.
              set SCHj := scheduled_at sched_jitter.
              set SUSP := job_cumulative_suspension.
              set Wj := workload_of_other_hep_jobs_in_sched_jitter.
              set Ws := workload_of_other_hep_jobs_in_sched_susp.
              set t1 := arr_j.
              set t2 := arr_j + R_j.
              rewrite exchange_big [X in _ <= X]exchange_big /= /service_at.
              rewrite -/SCHs -/SCHj addnS addn0.
              set TSs := fun a b => \sum_(a <= t0 < b)
                                           \sum_(j_hp <- all 0 t2 | hep j_hp) SCHs j_hp t0.
              set TSj := fun a b => \sum_(a <= t0 < b)
                                         \sum_(j_hp <- act 0 t2 | hep j_hp) SCHj j_hp t0.
              rewrite -/(TSj t1 (t1 + d).+1) -/(TSj 0 t1).
              rewrite leq_subLR -big_cat_nat //=;
                last by apply leq_trans with (n := t1 + d); first by apply leq_addr.                 
              rewrite exchange_big /=.
              feed (EQWORKj (t1 + d).+1); first by rewrite ltn_add2l.
              apply EQWORKj.
              intros j0 ARRin0 ARR0 HEP0; specialize (ALL j0 ARRin0 HEP0 ARR0).
                by apply completion_monotonic with (t := t1 + d).
            Qed.

            (* By combining each inequality above in sequence, we complete the induction
               step for Case 1. *)
            Lemma jitter_reduction_inductive_step_case1:
                service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + d + 1) <=
                service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + d + 1).
            Proof.
              apply: (leq_trans jitter_reduction_convert_service_to_workload).
              apply: (leq_trans jitter_reduction_compare_workload).
              apply: (leq_trans jitter_reduction_compare_service).
              by apply: (leq_trans jitter_reduction_convert_workload_to_service).
            Qed.

          End NoPendingJobs.

          Section ThereArePendingJobs.

            (* Case 2. Assume that there are higher-or-equal-priority jobs (other than j) whose
                       jitter has passed by time (arr_j + d) that are still pending at time
                       (arr_j + d) in the jitter-aware schedule. *)
            Hypothesis H_there_are_pending_jobs_in_sched_jitter:
              exists j_hp,
                arrives_in arr_seq j_hp /\
                other_higher_eq_priority_job j_hp /\
                job_has_actually_arrived j_hp (arr_j + d) /\
                ~~ job_completed_in_sched_jitter j_hp (arr_j + d). 

            (* By the induction hypothesis, the higher-or-equal-priority jobs received
               as much service in the jitter-aware schedule as in the suspension-aware
               schedule in the interval [arr_j, arr_j + d). Therefore, it only remains
               to show that:

               service_of_other_hep_jobs_in_sched_susp (arr_j + d) (arr_j + d + 1) <=
               service_of_other_hep_jobs_in_sched_jitter (arr_j + d) (arr_j + d + 1). *)

            (* Because the LHS in the inequality above cannot be larger than 1 (single point),
               it suffices to show that there is a higher-or-equal-priority job (different from j)
               scheduled at time (arr_j + d) in the jitter-aware schedule. That follows
               from two facts:
               (a) The jitter-aware schedule is work-conserving and enforces priorities.
                   Therefore, even if the job j_hp in the hypothesis above is not scheduled,
                   there will always be a job with higher-or-equal-priority being scheduled. 
               (b) If there is at least one higher-or-equal-priority pending job, by the
                   additional property we embedded in the schedule construction, we avoid
                   scheduling job j (see lemma sched_jitter_does_not_pick_j). *)
            Lemma jitter_reduction_inductive_step_case2:
              service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + d + 1) <=
              service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + d + 1).
            Proof.
              have RESPj := reduction_prop.sched_jitter_respects_policy job_arrival job_task ts
                      arr_seq _ _ higher_eq_priority _ _ _ job_cost job_suspension_duration j _ R_hp.
              feed_n 6 RESPj; try (by done).
              unfold reduction_prop.jitter_aware.respects_FP_policy in RESPj.
              have NOTj := reduction_prop.sched_jitter_does_not_pick_j job_arrival job_task ts arr_seq
                                   _ _ higher_eq_priority _ _ job_cost job_suspension_duration j R_hp.
              feed_n 4 NOTj; try (by done).
              have WORKj := reduction_prop.sched_jitter_work_conserving job_arrival job_task arr_seq _
                                          higher_eq_priority job_cost job_suspension_duration j R_hp.
              feed WORKj; first by done.
              have AFTERj := reduction_prop.sched_jitter_jobs_execute_after_jitter job_arrival job_task
                      arr_seq higher_eq_priority job_cost job_suspension_duration j _ R_hp.
              feed AFTERj; try (by done).
              set sched_j := reduction_prop.reduction.sched_jitter _ _ _ _ _ _ _ _ in AFTERj NOTj
                                                                                      WORKj RESPj.
              set inf_cost := reduction_prop.reduction.inflated_job_cost _ _ _ in NOTj WORKj
                                                                                  AFTERj RESPj.
              set job_jit := reduction_prop.reduction.job_jitter _ _ _ _ _ _ in AFTERj NOTj
                                                                                WORKj RESPj.
              rename H_priority_is_transitive into TRANS, H_induction_hypothesis into IH,
                     H_there_are_pending_jobs_in_sched_jitter into HASj.
              rewrite /service_of_other_hep_jobs_in_sched_jitter
                      /actual_arrivals_before_end_of_interval /actual_arrivals_before.
              rewrite /service_of_other_hep_jobs_in_sched_susp /service_of_jobs
                      /arrivals_before_end_of_interval /jobs_arrived_before.
              set all := arrivals; set act := actual_arrivals.
              set hep := other_higher_eq_priority_job.
              set Ss := service_during sched_susp.
              set Sj := service_during sched_jitter.
              set SCHs := scheduled_at sched_susp.
              set SCHj := scheduled_at sched_jitter.
              set SUSP := job_cumulative_suspension.
              set Wj := workload_of_other_hep_jobs_in_sched_jitter.
              set Ws := workload_of_other_hep_jobs_in_sched_susp.
              set t1 := arr_j.
              set t2 := arr_j + R_j.
              rewrite exchange_big [X in _ <= X]exchange_big /=.
              rewrite addnS /service_at addn0.
              rewrite big_nat_recr ?leq_addr // big_nat_recr ?leq_addr //=.
              apply leq_add;
                first by rewrite exchange_big [X in _ <= X]exchange_big; apply IH.
              case (boolP (has (fun j0 => hep j0 && scheduled_at sched_susp j0 (t1 + d))
                               (all 0 t2))) => [HASs | ALLs]; last first.
              {
                rewrite -all_predC in ALLs; move: ALLs => /allP ALLs.
                rewrite big_seq_cond big1 //.
                move => j0 /andP [IN0 HP0]; apply/eqP; rewrite eqb0.
                by specialize (ALLs j0 IN0); rewrite /= HP0 /= in ALLs.
              }           
              move: HASs => /hasP [j0 IN0 /andP [HP0 SCHED0]].
              rewrite big_mkcond (bigD1_seq j0) /=; [| by done | by eapply arrivals_uniq; eauto 1].
              rewrite HP0 SCHED0 big1 //; last first.
              {
                intros j1 NEQ; case: (hep j1); last by done.
                apply/eqP; rewrite eqb0; apply/negP; intro SCHED1.
                apply (only_one_job_scheduled _ j1) in SCHED0; last by done.
                by rewrite SCHED0 eq_refl in NEQ.
              }
              rewrite addn0.
              move: HASj => [j1 [ARRin1 [HEP1 [IN1 NOTCOMP1]]]].
              move: (HEP1) => /andP [HP1 NEQ1].
              rewrite /act /actual_arrivals in IN1.
              case (boolP (scheduled_at sched_jitter j1 (t1+d))) => [SCHED1 | NOTSCHED1].
              {
                rewrite (big_rem j1) /=; first by rewrite /hep HEP1 SCHED1.
                apply arrived_between_implies_in_actual_arrivals; try (by done).
                rewrite /actual_arrival_between /=.
                by apply leq_ltn_trans with (n := arr_j + d); last by rewrite ltn_add2l.
              }
              have BACK1: backlogged job_arrival inflated_job_cost job_jitter sched_jitter j1 (t1+d).
                by repeat (apply/andP; split); try (by done).
              move: (BACK1) (BACK1) => SCHED2 PRIO2.
              apply WORKj in SCHED2; try (by done).
              move: SCHED2 => [j2 SCHED2].
              apply RESPj with (j_hp := j2) in PRIO2; try (by done).
              have ARRin2: arrives_in arr_seq j2.
              {
                rewrite /sched_j in SCHED2.
                by apply reduction_prop.sched_jitter_jobs_come_from_arrival_sequence with
                                                    (sched_susp0 := sched_susp) in SCHED2.
              }
              have HP2: hep j2.
              {
                apply/andP; split; first by apply (TRANS (job_task j1)).
                apply/eqP; intro SAME; subst j2.
                move: BACK1 => /andP [PEND1 _].
                by specialize (NOTj j1 (t1+d) ARRin1 NEQ1 PEND1 HP1); rewrite SCHED2 in NOTj.
              } 
              have IN2: j2 \in act 0 t2.
              {
                apply arrived_between_implies_in_actual_arrivals; try (by done).
                rewrite /actual_arrival_between /=.
                apply leq_ltn_trans with (n := t1+d); last by rewrite ltn_add2l.
                by apply AFTERj.
              }
              by rewrite (big_rem j2) //= HP2 SCHED2.
            Qed.

          End ThereArePendingJobs.

        End InductiveStep.

        (** **** Main Claim of Section (B) *)
        
        (* Using the proof by induction above, we conclude that, for any interval length
           d <= R_j, the service received by higher-or-equal-priority jobs (other than j)
           in the interval [arr_j, arr_j + d) in the jitter-aware schedule is as large as
           the corresponding service in the suspension-aware schedule. *)
        Lemma jitter_reduction_more_service_inside_the_interval:
          forall d,
            d <= R_j ->
            service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + d) <=
            service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + d).
        Proof.
          have CASE1 := jitter_reduction_inductive_step_case1.
          have CASE2 := jitter_reduction_inductive_step_case2.
          set all := arrivals; set act := actual_arrivals.
          set hep := other_higher_eq_priority_job.         
          rename H_priority_is_transitive into TRANS.
          induction d.
          {
            rewrite /service_of_other_hep_jobs_in_sched_susp /service_of_jobs.
            by intros _; rewrite exchange_big /= addn0 big_geq.
          }
          intros LTR; feed (IHd); first by apply ltnW.
          rewrite -addn1 addnA.
          case (boolP (has (fun j0 => hep j0 && job_has_actually_arrived j0 (arr_j + d)
                              && ~~ completed_by inflated_job_cost sched_jitter j0 (arr_j + d))
                           (act 0 (arr_j + R_j)))) => [HASj | ALLj]; last first.
          {
            apply CASE1; try (by done).
            rewrite -all_predC in ALLj; move: ALLj => /allP ALLj.
            intros j0 ARRin0 HEP0 ARR0.
            feed (ALLj j0).
            {
              apply arrived_between_implies_in_actual_arrivals; try (by done).
              rewrite /actual_arrival_between /=.
              by apply leq_ltn_trans with (n := arr_j + d); last by rewrite ltn_add2l.
            }
            by rewrite /= /hep HEP0 ARR0 /= negbK in ALLj.
          }
          {
            apply (CASE2 _ LTR IHd).
            move: HASj => /hasP [j0 IN0 /andP [/andP [HP0 ARR0] NOTCOMP0]].
            exists j0; repeat (split); try (by done).
            rewrite /act /actual_arrivals in IN0.
            by apply in_actual_arrivals_between_implies_arrived in IN0.
          }
        Qed.

      End MoreServiceInsideTheInterval.

    End MoreServiceAfterArrival.
    
    (** ** 6-(C) Conclusion: Comparing Response Times of Job j  *)
    
    (* In this section, we prove that the generated schedule is "worse" for job j.
       More precisely, job j receives no more service in the jitter-aware schedule
       than the cumulative service and suspension time in the original schedule. *)
    Section JitterAwareScheduleIsWorse.
      
      (* Recall the definition of job response-time bound in sched_jitter. *)
      Let job_response_time_in_sched_jitter_bounded_by :=
        is_response_time_bound_of_job job_arrival inflated_job_cost sched_jitter.

      (* From this point, we are going to analyze both schedules up to time (arr_j + R_j) and
         compare the service received by job j. At the end, we are going to prove that R_j is
         also a response-time bound for job j in the suspension-aware schedule sched_susp. *)      

      (* First, we show that the service received by job j in the interval [arr_j, arr_j + R_j)
         is always bounded by the difference between the interval length R_j and the service
         received by the other higher-or-equal-priority jobs in the same interval. *)
      Lemma jitter_reduction_service_jitter:
        service_during sched_jitter j arr_j (arr_j + R_j) <=
        R_j - service_of_other_hep_jobs_in_sched_jitter arr_j (arr_j + R_j).
      Proof.
        have ARRj := reduction_prop.sched_jitter_jobs_come_from_arrival_sequence job_arrival job_task
                     arr_seq higher_eq_priority job_cost job_suspension_duration sched_susp _ j _ R_hp.
        feed_n 2 ARRj; try done.
        have AFTERj := reduction_prop.sched_jitter_jobs_execute_after_jitter job_arrival job_task
                     arr_seq higher_eq_priority job_cost job_suspension_duration j _ R_hp.
        feed AFTERj; try done.
        set Sj := service_during sched_jitter j arr_j.
        set Shp := service_of_other_hep_jobs_in_sched_jitter arr_j.
        rewrite subh3 //.
        apply leq_trans with (n := \sum_(arr_j <= t < arr_j + R_j) 1);
          last by simpl_sum_const; rewrite addKn.
        rewrite /Sj /Shp /service_of_other_hep_jobs_in_sched_jitter /service_of_jobs
                /service_during.
        rewrite exchange_big -big_split /=.
        apply leq_sum_nat; move => i /andP [GEi LTi] _.
        destruct (sched_jitter i) as [j'|] eqn:SCHED;
          last by rewrite /service_at /scheduled_at SCHED /= add0n; simpl_sum_const.
        case (boolP ((j' == j) || ~~ higher_eq_priority (job_task j') (job_task j))).
        {
          intros OR; rewrite big1; first by rewrite addn0 leq_b1.
          intros j_hp HP; rewrite /other_higher_eq_priority_job in HP.
          apply/eqP; rewrite eqb0; apply contraT; rewrite negbK; move => /eqP SCHED'.
          rewrite SCHED in SCHED'; case: SCHED' => SAME; subst j_hp.
          move: OR => /orP [/eqP EQ | NOTHP]; subst; first by rewrite eq_refl andbF in HP.
          by apply negbTE in NOTHP; rewrite NOTHP /= in HP.
        }
        {
          rewrite negb_or negbK; move => /andP [NEQ HP].
          rewrite -[1]add0n; apply leq_add.
          {
            rewrite leqn0 eqb0; apply/negP; intro SCHED'.
            apply only_one_job_scheduled with (j1 := j') in SCHED'; [subst | by apply/eqP].
            by rewrite eq_refl in NEQ.
          }
          {
            move: SCHED => /eqP SCHED.
            have IN: arrives_in arr_seq j' by apply ARRj in SCHED.
            have ARR: actual_arrival_before job_arrival job_jitter j' (arr_j + R_j).
              by apply AFTERj in SCHED; apply: (leq_ltn_trans _ LTi).
            rewrite big_mkcond (bigD1_seq j') /=; first last.
            - by eapply actual_arrivals_uniq; eauto 1.  
            - by eapply arrived_between_implies_in_actual_arrivals.
            rewrite /other_higher_eq_priority_job HP NEQ /=.
            move: SCHED => /eqP SCHED.
            rewrite /service_at /scheduled_at SCHED eq_refl.
            rewrite big1 //; intros j_other NEQother.
            case: ifP => HPother; last by done.
            apply/eqP; rewrite eqb0; apply/eqP; case => SAME; subst j_other.
            by rewrite eq_refl in NEQother.
          }
        }
      Qed.

      (* Next, since we want to infer that job j is schedulable in the suspension-aware
         schedule if it is schedulable in the jitter-aware schedule, we can assume by
         contrapositive that job j has not completed by time (arr_j + R_j) in
         the suspension-aware schedule. *)
      Section JobNotCompleted.

        (* Assume that j has not completed by (arr_j + R_j) in the suspension-aware schedule. *)
        Hypothesis H_j_not_completed:
          ~~ job_completed_in_sched_susp j (arr_j + R_j).

        (* Then, we can prove that the difference between the interval length and
           the service received by the other higher-or-equal-priority jobs during
           [arr_j, arr_j + R_j) in the suspension-aware schedule is bounded by
           the cumulative service and suspension time of job j. *)
        Lemma jitter_reduction_service_susp:
          R_j - service_of_other_hep_jobs_in_sched_susp arr_j (arr_j + R_j) <=
          service_during sched_susp j arr_j (arr_j + R_j) +
          job_cumulative_suspension j arr_j (arr_j + R_j).
        Proof.
          move: (H_valid_schedule) => [FROM [ARRIVE [COMPs [WORK [PRIO _]]]]].
          rename H_j_not_completed into NOTCOMP.
          rewrite leq_subLR -big_split /=.
          rewrite /service_of_other_hep_jobs_in_sched_susp /service_of_jobs.
          rewrite exchange_big -big_split /=.
          apply leq_trans with (n := \sum_(arr_j <= t < arr_j + R_j) 1);
            first by simpl_sum_const; rewrite addKn.
          apply leq_sum_nat; move => i /andP [GEi LTi] _.
          rewrite -/job_suspended_at /service_at.
          case: (boolP (job_suspended_at _ _)) => [SUSP | NOTSUSP];
            [by rewrite addnA leq_addl | rewrite addn0].
          case: (boolP (scheduled_at _ _ _)) => [SCHED | NOTSCHED];
            [by rewrite leq_addl | rewrite addn0].
          have BACK: susp.backlogged job_arrival job_cost job_suspension_duration sched_susp j i.
          {
            repeat (apply/andP; split); try (by done).
            apply/negP; intro COMP.
            move: NOTCOMP => /negP NOTCOMP; apply: NOTCOMP.
            by apply completion_monotonic with (t := i); try (by done); apply ltnW.
          }
          move: (BACK) => SCHED; apply WORK in SCHED; last by done.
          move: SCHED => [j_hp SCHEDhp].
          have NEQ: j_hp != j by apply/eqP => SAME; subst; rewrite SCHEDhp in NOTSCHED.
          have HP: higher_eq_priority (job_task j_hp) (job_task j) by apply PRIO with (t := i).
          rewrite (big_rem j_hp) /other_higher_eq_priority_job /=; last first.
          {
            have IN: arrives_in arr_seq j_hp by apply FROM in SCHEDhp. 
            apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival);
              try (by done).
            by apply: (leq_trans _ LTi); apply ARRIVE.
          }
          by rewrite HP NEQ SCHEDhp /=.
        Qed.
      
        (* Since the higher-or-equal-priority jobs receive more service during
           [arr_j, arr_j + R_j) in the jitter-aware schedule and produce more
           interference, it follows that job j cannot receive as much service
           in the jitter-aware schedule as in the suspension-aware schedule. *)
        Lemma jitter_reduction_less_service_for_job_j:
          service_during sched_jitter j arr_j (arr_j + R_j) <=
          service_during sched_susp j arr_j (arr_j + R_j)
          + job_cumulative_suspension j arr_j (arr_j + R_j).
        Proof.
          apply: (leq_trans jitter_reduction_service_jitter).
          apply: (leq_trans _ jitter_reduction_service_susp).
          by apply leq_sub2l, jitter_reduction_more_service_inside_the_interval.
        Qed.

      End JobNotCompleted.

      (** **** Main Claim of Section (C) *)
        
      (* Suppose that the response time of job j is bounded by R_j in sched_jitter. *) 
      Hypothesis H_response_time_of_j_in_sched_jitter:
        job_response_time_in_sched_jitter_bounded_by j R_j.

      (* Then, using the lemmas above, we conclude that the response time of job j in sched_susp
         is also bounded by R_j. *)
      Corollary jitter_reduction_job_j_completes_no_later:
        job_response_time_in_sched_susp_bounded_by j R_j.
      Proof. 
        move: (H_valid_schedule) => [_ [MUSTARRs [COMPs [WORK [PRIO SELF]]]]].
        rename H_response_time_of_j_in_sched_jitter into COMPj.
        apply contraT; intro NOTCOMPs.
        suff NOTCOMPj: ~~ job_response_time_in_sched_jitter_bounded_by j R_j;
          [by rewrite COMPj in NOTCOMPj | clear COMPj].
        have LESS := jitter_reduction_less_service_for_job_j NOTCOMPs.
        rewrite -ltnNge. 
        rewrite /inflated_job_cost /reduction.inflated_job_cost eq_refl.
        apply leq_ltn_trans with (n := service_during sched_jitter j arr_j (arr_j + R_j)).
        { rewrite /service /service_during.
          rewrite (ignore_service_before_arrival job_arrival) ?leq_addr //.
          apply jobs_with_jitter_must_arrive_to_execute with (job_jitter0 := job_jitter).
            by apply reduction_prop.sched_jitter_jobs_execute_after_jitter.
        }
        apply: (leq_ltn_trans LESS).
        rewrite -addn1 -addnA [_ + 1]addnC addnA; apply leq_add.
        { rewrite addn1; apply contraT; rewrite -leqNgt; intro LE.
          exfalso; move: NOTCOMPs => /negP NOTCOMPs; apply: NOTCOMPs.
          rewrite /job_response_time_in_sched_susp_bounded_by /is_response_time_bound_of_job.
          rewrite /completed_by.
          apply: (leq_trans LE).
          rewrite /service /service_during.
            by rewrite [X in _ <= X](ignore_service_before_arrival job_arrival) ?leq_addr.
        }
        by apply cumulative_suspension_le_total_suspension.
      Qed.

    End JitterAwareScheduleIsWorse.

  End ProvingScheduleProperties.
  
End JitterScheduleService.