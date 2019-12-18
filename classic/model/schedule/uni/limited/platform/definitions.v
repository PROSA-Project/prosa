Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task
               prosa.classic.model.priority
               prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(** * Platform with limited preemptions *)
(** In this module we introduce the notion of whether a job can be preempted at a given time 
   (using a predicate can_be_preempted). In addition, we provide instantiations of the 
   predicate for various preemption models. *)
Module LimitedPreemptionPlatform.

  Import Job SporadicTaskset UniprocessorSchedule Priority Service.
  
  (* In this section, we define a processor platform with limited preemptions. *)
  Section Properties.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
     
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* For simplicity, let's define some local names. *)
    Let job_pending := pending job_arrival job_cost sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_scheduled_at := scheduled_at sched.

    (* First, we define the notion of a preemption time. *)
    Section PreemptionTime. 

      (* Let can_be_preempted be a function that maps a job j and the progress of j
         at some time instant t to a boolean value, i.e., true if job j can be 
         preempted at this point of execution and false otherwise. *)  
      Variable can_be_preempted: Job -> time -> bool.
      
      (* We say that a time instant t is a preemption time iff there's no job currently 
         scheduled at t that cannot be preempted (according to the predicate). *)
      Definition preemption_time (t: time) :=
        if sched t is Some j then
          can_be_preempted j (service sched j t)
        else true. 

      (* Since the notion of preemption time is based on an user-provided 
         predicate (variable can_be_preempted), it does not guarantee that 
         the scheduler will enforce correct behavior. For that, we must 
         define additional predicates. *)
      Section CorrectPreemptionModel.

        (* First, if a job j is not preemptive at some time instant t, 
           then j must be scheduled at time t. *)
        Definition not_preemptive_implies_scheduled (j: Job) :=
          forall t,
            ~~ can_be_preempted j (service sched j t) ->
            job_scheduled_at j t. 

        (* A job can start its execution only from a preemption point. *)
        Definition execution_starts_with_preemption_point (j: Job) := 
          forall prt,
            ~~ job_scheduled_at j prt ->
            job_scheduled_at j prt.+1 ->
            can_be_preempted j (service sched j prt.+1).

        (* We say that a model is a correct preemption model if both
           definitions given above are satisfied for any job. *)
        Definition correct_preemption_model :=
          forall j,
            arrives_in arr_seq j ->
            not_preemptive_implies_scheduled j
            /\ execution_starts_with_preemption_point j.
        
      End CorrectPreemptionModel.

      (* Note that for analysis purposes, it is important that the distance 
         between preemption points of a job is bounded. To ensure that, we 
         define next the model of bounded nonpreemptive segment. *)
      Section ModelWithBoundedNonpreemptiveRegions.

        (* We require that a job has to be executed at least one time instant
           in order to reach a nonpreemptive segment. *)
        Definition job_cannot_become_nonpreemptive_before_execution (j: Job) :=
          can_be_preempted j 0.
 
        (* And vice versa, a job cannot remain nonpreemptive after its completion. *)
        Definition job_cannot_be_nonpreemptive_after_completion (j: Job) := 
          can_be_preempted j (job_cost j).

        (* Consider a function that maps a job to the length of 
           its maximal nonpreemptive segment. *)
        Variable job_max_nps: Job -> time.
        
        (* And a function task_max_nps... *)
        Variable task_max_nps: Task -> time.
                  
        (* ...that gives an upper bound for values of the function job_max_nps. *)
        Definition job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (j: Job) :=
          arrives_in arr_seq j ->
          job_max_nps j <= task_max_nps (job_task j).
        
        (* Next, we say that all the segments of a job j have bounded length iff for any 
           progress progr of job j there exists a preemption point preeemption_point such that
           [progr <= preemption_point <= progr + (job_max_nps j - ε)]. That is, in any time 
           interval of length [job_max_nps j], there exists a preeemption point which     
           lies in this interval. *)
        Definition nonpreemptive_regions_have_bounded_length (j: Job) :=
          forall progr,
            0 <= progr <= job_cost j -> 
            exists preemption_point,
              progr <= preemption_point <= progr + (job_max_nps j - ε) /\
              can_be_preempted j preemption_point.
        
        (* Finally, we say that the schedule enforces bounded nonpreemptive segments 
           iff the predicate can_be_preempted satisfies the two conditions above. *)
        Definition model_with_bounded_nonpreemptive_segments :=
          forall j,
            arrives_in arr_seq j ->
            job_cannot_become_nonpreemptive_before_execution j
            /\ job_cannot_be_nonpreemptive_after_completion j
            /\ job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment j
            /\ nonpreemptive_regions_have_bounded_length j.
        
      End ModelWithBoundedNonpreemptiveRegions.

      (* In this section we prove a few basic properties of the can_be_preempted predicate. *)
      Section Lemmas.

        Variable job_max_nps: Job -> time.
        Variable task_max_nps: Task -> time.

        (* Consider the correct model with bounded nonpreemptive segments. *)
        Hypothesis H_correct_preemption_model: correct_preemption_model.
        Hypothesis H_model_with_bounded_np_segments:
          model_with_bounded_nonpreemptive_segments job_max_nps task_max_nps.

        (* Assume jobs come from some arrival sequence. *)
        Hypothesis H_jobs_come_from_arrival_sequence:
          jobs_come_from_arrival_sequence sched arr_seq.

        (* Then, we can show that time 0 is a preemption time. *)
        Lemma zero_is_pt: preemption_time 0.
        Proof.
          unfold preemption_time.
          case SCHED: (sched 0) => [j | ]; last by done.
          move: (SCHED) => /eqP ARR.
          apply H_jobs_come_from_arrival_sequence in ARR.
          rewrite /service /service_during big_geq; last by done.
            by move: (H_model_with_bounded_np_segments j ARR) => [PP _]; apply PP.
        Qed.

        (* Also, we show that the first instant of execution is a preemption time. *)
        Lemma first_moment_is_pt:
          forall j prt,
            arrives_in arr_seq j -> 
            ~~ job_scheduled_at j prt ->
            job_scheduled_at j prt.+1 ->
            preemption_time prt.+1.
        Proof.
          intros s pt ARR NSCHED SCHED.
          unfold preemption_time. 
          move: (SCHED) => /eqP SCHED2; rewrite SCHED2; clear SCHED2.
            by move: (H_correct_preemption_model s ARR) => [_ FHF]; auto.
        Qed. 
        
      End Lemmas. 
      
    End PreemptionTime.
    
    (* Next, we define properties related to execution. *)
    Section Execution.

      (* Similarly to preemptive scheduling, we say that the schedule is 
         work-conserving iff whenever a job is backlogged, the processor 
         is always busy scheduling another job. *)
      (* Imported from the preemptive schedule. *)
      Definition work_conserving := Platform.work_conserving job_cost.

    End Execution.

    (* Next, we define properties related to FP scheduling. *)
    Section FP.
      
      (* Consider any preemption model. *)
      Variable preemption_model: Job -> time -> bool.
     
      (* We say that an FP policy...*)
      Variable higher_eq_priority: FP_policy Task.

      (* ...is respected by the schedule iff, at every preemption point, 
         a scheduled task has higher (or same) priority than (as) 
         any backlogged task. *)
      Definition respects_FP_policy_at_preemption_point :=
        forall j j_hp t,
          preemption_time preemption_model t ->
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority (job_task j_hp) (job_task j).
       
    End FP.
     
    (* Next, we define properties related to JLFP policies. *)
    Section JLFP.

      (* Consider a scheduling model. *)
      Variable preemption_model: Job -> time -> bool.
      
      (* We say that a JLFP policy ...*)
      Variable higher_eq_priority: JLFP_policy Job.

      (* ...is respected by the schedule iff, at every preemption point, 
         a scheduled task has higher (or same) priority than (as) 
         any backlogged task. *)
      Definition respects_JLFP_policy_at_preemption_point :=
        forall j j_hp t,
          preemption_time preemption_model t ->
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          scheduled_at sched j_hp t ->
          higher_eq_priority j_hp j.
      
    End JLFP.

  End Properties.
  
End LimitedPreemptionPlatform.