Require Export prosa.model.task.concept.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.  

(** * Definitions for Abstract Response-Time Analysis *)
(** In this module, we propose a set of definitions for the general framework for response-time analysis (RTA) 
    of uni-processor scheduling of real-time tasks with arbitrary arrival models. *)
Section AbstractRTADefinitions. 

  (** In this section, we introduce all the abstract notions required by the analysis. *)
  Section Definitions.

    (** Consider any type of job associated with any type of tasks... *)
    Context {Job : JobType}.
    Context {Task : TaskType}.
    Context `{JobTask Job Task}.

    (** ... with arrival times and costs. *)
    Context `{JobArrival Job}.
    Context `{JobCost Job}.

    (** Consider any kind of processor state model. *)
    Context {PState : Type}.
    Context `{ProcessorState Job PState}.
    
    (** Consider any arrival sequence... *) 
    Variable arr_seq : arrival_sequence Job.

    (** ... and any schedule of this arrival sequence. *)
    Variable sched : schedule PState.

    (** Let [tsk] be any task that is to be analyzed *)
    Variable tsk : Task.
    
    (** For simplicity, let's define some local names. *)
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by sched.

    (** Recall that a job [j] is pending_earlier_and_at a time instant [t] iff job
       [j] arrived before time [t] and is still not completed by time [t]. *)
    Let job_pending_earlier_and_at := pending_earlier_and_at sched.

    (** We are going to introduce two main variables of the analysis: 
       (a) interference, and (b) interfering workload. *)

    (** a) Interference *)
    (** Execution of a job may be postponed by the environment and/or the system due to different
       factors (preemption by higher-priority jobs, jitter, black-out periods in hierarchical 
       scheduling, lack of budget, etc.), which we call interference. 

       Besides, note that even the subsequent activation of a task can suffer from interference at 
       the beginning of its busy interval (despite the fact that this job hasn’t even arrived 
       at that moment!). Thus, it makes more sense (at least for the current busy-interval 
       analysis) to think about interference of a job as any interference within the 
       corresponding busy interval, and not after release of the job.

       Based on that, assume a predicate that expresses whether a job [j] under consideration 
       incurs interference at a given time [t] (in the context of the schedule under consideration).
       This will be used later to upper-bound job [j]'s response time. Note that a concrete 
       realization of the function may depend on the schedule, but here we do not require this 
       for the sake of simplicity and generality. *)
    Variable interference : Job -> instant -> bool.

    (** b) Interfering Workload *)
    (** In addition to interference, the analysis assumes that at any time [t], we know an upper 
       bound on the potential cumulative interference that can be incurred in the future by any
       job (i.e., the total remaining potential delays). Based on that, assume a function 
       interfering_workload that indicates for any job [j], at any time [t], the amount of potential 
       interference for job [j] that is introduced into the system at time [t]. This function will be
       later used to upper-bound the length of the busy window of a job.
       One example of workload function is the "total cost of jobs that arrive at time [t] and 
       have higher-or-equal priority than job j". In some task models, this function expresses 
       the amount of the potential interference on job [j] that "arrives" in the system at time [t]. *)
    Variable interfering_workload : Job -> instant -> duration.

    (** In order to bound the response time of a job, we must to consider the cumulative 
       interference and cumulative interfering workload. *)
    Definition cumul_interference j t1 t2 := \sum_(t1 <= t < t2) interference j t.
    Definition cumul_interfering_workload j t1 t2 := \sum_(t1 <= t < t2) interfering_workload j t.

    (** Definition of Busy Interval *)
    (** Further analysis will be based on the notion of a busy interval. The overall idea of the 
       busy interval is to take into account the workload that cause a job under consideration to 
       incur interference. In this section, we provide a definition of an abstract busy interval. *)
    Section BusyInterval.

      (** We say that time instant [t] is a quiet time for job [j] iff two conditions hold. 
         First, the cumulative interference at time [t] must be equal to the cumulative
         interfering workload, to indicate that the potential interference seen so far 
         has been fully "consumed" (i.e., there is no more higher-priority work or other 
         kinds of delay pending). Second, job [j] cannot be pending at any time earlier
         than [t] _and_ at time instant [t] (i.e., either it was pending earlier but is no 
         longer pending now, or it was previously not pending and may or may not be 
         released now), to ensure that the busy window captures the execution of job [j]. *)
      Definition quiet_time (j : Job) (t : instant) :=
        cumul_interference j 0 t = cumul_interfering_workload j 0 t /\
        ~~ job_pending_earlier_and_at j t.
      
      (** Based on the definition of quiet time, we say that interval <<[t1, t2)>> is 
         a (potentially unbounded) busy-interval prefix w.r.t. job [j] iff the 
         interval (a) contains the arrival of job j, (b) starts with a quiet
         time and (c) remains non-quiet. *)
      Definition busy_interval_prefix (j : Job) (t1 t2 : instant) :=
        t1 <= job_arrival j < t2 /\
        quiet_time j t1 /\
        (forall t, t1 < t < t2 -> ~ quiet_time j t). 

      (** Next, we say that an interval <<[t1, t2)>> is a busy interval iff
         [t1, t2) is a busy-interval prefix and t2 is a quiet time. *)
      Definition busy_interval (j : Job) (t1 t2 : instant) :=
        busy_interval_prefix j t1 t2 /\
        quiet_time j t2.

      (** Note that the busy interval, if it exists, is unique. *)
      Lemma busy_interval_is_unique:
        forall j t1 t2 t1' t2',
          busy_interval j t1 t2 ->
          busy_interval j t1' t2' ->
          t1 = t1' /\ t2 = t2'.
      Proof.
        intros ? ? ? ? ? BUSY BUSY'.
        have EQ: t1 = t1'.
        { apply/eqP.
          apply/negPn/negP; intros CONTR.
          move: BUSY => [[IN [QT1 NQ]] _].
          move: BUSY' => [[IN' [QT1' NQ']] _].
          move: CONTR; rewrite neq_ltn; move => /orP [LT|GT].
          { apply NQ with t1'; try done; clear NQ.
            apply/andP; split; first by done.
            move: IN IN' => /andP [_ T1] /andP [T2 _].
              by apply leq_ltn_trans with (job_arrival j).
          }
          { apply NQ' with t1; try done; clear NQ'.
            apply/andP; split; first by done.
            move: IN IN' => /andP [T1 _] /andP [_ T2].
              by apply leq_ltn_trans with (job_arrival j).
          }
        } subst t1'.
        have EQ: t2 = t2'.
        { apply/eqP.
          apply/negPn/negP; intros CONTR.
          move: BUSY => [[IN [_ NQ]] QT2].
          move: BUSY' => [[IN' [_ NQ']] QT2'].
          move: CONTR; rewrite neq_ltn; move => /orP [LT|GT].
          { apply NQ' with t2; try done; clear NQ'.
            apply/andP; split; last by done.
            move: IN IN' => /andP [_ T1] /andP [T2 _].
              by apply leq_ltn_trans with (job_arrival j).
          }
          { apply NQ with t2'; try done; clear NQ.
            apply/andP; split; last by done.
            move: IN IN' => /andP [T1 _] /andP [_ T2].
              by apply leq_ltn_trans with (job_arrival j).
          }
        } by subst t2'.
      Qed.
      
    End BusyInterval.

    (** In this section, we introduce some assumptions about the
       busy interval that are fundamental for the analysis. *)
    Section BusyIntervalProperties.

      (** We say that a schedule is "work_conserving" iff for any job [j] from task [tsk] and 
         at any time [t] within a busy interval, there are only two options:
         either (a) interference(j, t) holds or (b) job [j] is scheduled at time [t]. *)
      Definition work_conserving :=
        forall j t1 t2 t,
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_cost j > 0 ->
          busy_interval j t1 t2 ->
          t1 <= t < t2 ->
          ~ interference j t <-> job_scheduled_at j t.

      (** Next, we say that busy intervals of task [tsk] are bounded by [L] iff, for any job [j] of task
         [tsk], there exists a busy interval with length at most L. Note that the existence of such a
         bounded busy interval is not guaranteed if the schedule is overloaded with work. 
         Therefore, in the later concrete analyses, we will have to introduce an additional 
         condition that prevents overload. *)
      Definition busy_intervals_are_bounded_by L :=
        forall j,
          arrives_in arr_seq j ->
          job_task j = tsk ->
          job_cost j > 0 -> 
          exists t1 t2,
            t1 <= job_arrival j < t2 /\
            t2 <= t1 + L /\
            busy_interval j t1 t2.

      (** Although we have defined the notion of cumulative interference of a job, it cannot be used in 
         a response-time analysis because of the variability of job parameters. To address this 
         issue, we define the notion of an interference bound. Note that according to the definition of
         a work conserving schedule, interference does _not_ include execution of a job itself. Therefore,
         an interference bound is not obliged to take into account the execution of this job. We say that 
         the job interference is bounded by an interference_bound_function ([IBF]) iff for any job [j] of 
         task [tsk] the cumulative interference incurred by [j] in the sub-interval [t1, t1 + delta) of busy
         interval [t1, t2) does not exceed [interference_bound_function(tsk, A, delta)], where [A] is a 
         relative arrival time of job [j] (with respect to time [t1]). *)
      Definition job_interference_is_bounded_by (interference_bound_function: Task -> duration -> duration -> duration) :=
        (** Let's examine this definition in more detail. *)
        forall t1 t2 delta j,
          (** First, we require [j] to be a job of task [tsk]. *)
          arrives_in arr_seq j ->
          job_task j = tsk ->
          (** Next, we require the IBF to bound the interference only within the interval <<[t1, t1 + delta)>>. *)
          busy_interval j t1 t2 ->
          t1 + delta < t2 ->
          (** Next, we require the IBF to bound the interference only until the job is 
             completed, after which the function can behave arbitrarily. *)
          ~~ job_completed_by j (t1 + delta) ->
          (** And finally, the IBF function might depend not only on the length 
             of the interval, but also on the relative arrival time of job [j] (offset). *)
          (** While the first three conditions are needed for discarding excessive cases, offset adds 
             flexibility to the IBF, which is important, for instance, when analyzing EDF scheduling. *)
          let offset := job_arrival j - t1 in 
          cumul_interference j t1 (t1 + delta) <= interference_bound_function tsk offset delta.

    End BusyIntervalProperties.

  End Definitions.

End AbstractRTADefinitions.
