Require Export prosa.model.task.concept.

(** * Definitions for Abstract Response-Time Analysis *)

(** In the following, we propose a set of definitions for the general
    framework for response-time analysis (RTA) of uni-processor
    scheduling of real-time tasks with arbitrary arrival models. *)

(** We are going to introduce two main variables of the analysis:
    (a) interference, and (b) interfering workload. *)

(** ** a) Interference *)
(** Execution of a job may be postponed by the environment and/or the
    system due to different factors (preemption by higher-priority
    jobs, jitter, black-out periods in hierarchical scheduling, lack
    of budget, etc.), which we call interference.

    Besides, note that even the subsequent activation of a task can
    suffer from interference at the beginning of its busy interval
    (despite the fact that this job hasn’t even arrived at that
    moment!). Thus, it makes more sense (at least for the current
    busy-interval analysis) to think about interference of a job as
    any interference within the corresponding busy interval, and not
    just after the release of the job.

    Based on that rationale, assume a predicate that expresses whether a job [j]
    under consideration incurs interference at a given time [t] (in
    the context of the schedule under consideration).  This will be
    used later to upper-bound job [j]'s response time. Note that a
    concrete realization of the function may depend on the schedule,
    but here we do not require this for the sake of simplicity and
    generality. *)
Class Interference (Job : JobType) :=
  interference : Job -> instant -> bool.

(** ** b) Interfering Workload *)
(** In addition to interference, the analysis assumes that at any time
    [t], we know an upper bound on the potential cumulative
    interference that can be incurred in the future by any job (i.e.,
    the total remaining potential delays). Based on that, assume a
    function [interfering_workload] that indicates for any job [j], at
    any time [t], the amount of potential interference for job [j]
    that is introduced into the system at time [t]. This function will
    be later used to upper-bound the length of the busy window of a
    job.  One example of workload function is the "total cost of jobs
    that arrive at time [t] and have higher-or-equal priority than job
    [j]". In some task models, this function expresses the amount of the
    potential interference on job [j] that "arrives" in the system at
    time [t]. *)
Class InterferingWorkload (Job : JobType) :=
  interfering_workload : Job -> instant -> duration.

(** Next we introduce all the abstract notions required by the analysis. *)
Section AbstractRTADefinitions.

  (** Consider any type of job associated with any type of tasks... *)
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.

  (** ... with arrival times and costs. *)
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any kind of processor state model. *)
  Context {PState : ProcessorState Job}.

  (** Consider any arrival sequence ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any schedule of this arrival sequence. *)
  Variable sched : schedule PState.

  (** Let [tsk] be any task that is to be analyzed *)
  Variable tsk : Task.

  (** Assume we are provided with abstract functions for interference
      and interfering workload. *)
  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  (** In order to bound the response time of a job, we must
      consider the cumulative interference and cumulative interfering
      workload. *)
  Definition cumulative_interference j t1 t2 := \sum_(t1 <= t < t2) interference j t.
  Definition cumulative_interfering_workload j t1 t2 := \sum_(t1 <= t < t2) interfering_workload j t.

  (** Definition of Busy Interval *)
  (** Further analysis will be based on the notion of a busy
      interval. The overall idea of the busy interval is to take into
      account the workload that cause a job under consideration to
      incur interference. In this section, we provide a definition of
      an abstract busy interval. *)
  Section BusyInterval.

    (** We say that time instant [t] is a quiet time for job [j] iff
        two conditions hold. First, the cumulative interference at
        time [t] must be equal to the cumulative interfering
        workload. Intuitively, this condition indicates that the
        potential interference seen so far has been fully "consumed"
        (i.e., there is no more higher-priority work or other kinds of
        delay pending). Second, job [j] cannot be pending at any time
        earlier than [t] _and_ at time instant [t] (i.e., either it
        was pending earlier but is no longer pending now, or it was
        previously not pending and may or may not be released
        now). The second condition ensures that the busy window
        captures the execution of job [j]. *)
    Definition quiet_time (j : Job) (t : instant) :=
      cumulative_interference j 0 t = cumulative_interfering_workload j 0 t /\
      ~~ pending_earlier_and_at sched j t.

    (** Based on the definition of quiet time, we say that an interval
        <<[t1, t2)>> is a (potentially unbounded) busy-interval prefix
        w.r.t. job [j] iff the interval (a) contains the arrival of
        job j, (b) starts with a quiet time and (c) remains
        non-quiet. *)
    Definition busy_interval_prefix (j : Job) (t1 t2 : instant) :=
      t1 <= job_arrival j < t2 /\
      quiet_time j t1 /\
      (forall t, t1 < t < t2 -> ~ quiet_time j t).

    (** Next, we say that an interval <<[t1, t2)>> is a busy interval
        iff <<[t1, t2)>> is a busy-interval prefix and [t2] is a quiet
        time. *)
    Definition busy_interval (j : Job) (t1 t2 : instant) :=
      busy_interval_prefix j t1 t2 /\
      quiet_time j t2.

    (** Note that the busy interval, if it exists, is unique. *)
    Fact busy_interval_is_unique :
      forall j t1 t2 t1' t2',
        busy_interval j t1 t2 ->
        busy_interval j t1' t2' ->
        t1 = t1' /\ t2 = t2'.
    Proof.
      move=> j t1 t2 t1' t2' BUSY BUSY'.
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
      }
      subst t1'.
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
      }
      by subst t2'.
    Qed.

  End BusyInterval.

  (** In this section, we introduce some assumptions about the busy
      interval that are fundamental to the analysis. *)
  Section BusyIntervalProperties.

    (** We say that a schedule is "work-conserving" (in the abstract
        sense) iff, for any job [j] from task [tsk] and at any time [t]
        within a busy interval, there are only two options: either (a)
        [interference(j, t)] holds or (b) job [j] is scheduled at time
        [t]. *)
    Definition work_conserving :=
      forall j t1 t2 t,
        arrives_in arr_seq j ->
        job_cost j > 0 ->
        busy_interval_prefix j t1 t2 ->
        t1 <= t < t2 ->
        ~ interference j t <-> receives_service_at sched j t.

    (** Next, we say that busy intervals of task [tsk] are bounded by
        [L] iff, for any job [j] of task [tsk], there exists a busy
        interval with length at most [L]. Note that the existence of
        such a bounded busy interval is not guaranteed if the schedule
        is overloaded with work.  Therefore, in the later concrete
        analyses, we will have to introduce an additional condition
        that prevents overload. *)
    Definition busy_intervals_are_bounded_by L :=
      forall j,
        arrives_in arr_seq j ->
        job_of_task tsk j ->
        job_cost j > 0 ->
        exists t1 t2,
          t1 <= job_arrival j < t2 /\
          t2 <= t1 + L /\
          busy_interval j t1 t2.


    (** Although we have defined the notion of cumulative interference
        of a job, it cannot be used in a (static) response-time
        analysis because of the dynamic variability of job parameters.
        To address this issue, we define the notion of an interference
        bound. *)

    (** As a first step, we introduce a notion of an "interference
        bound function" [IBF]. An interference bound function is any
        function with a type [Task -> duration -> duration -> work] that
        bounds cumulative interference of a job of a task under
        analysis (a precise definition will be presented below).

        Note that the function has three parameters. The first and the
        last parameters are a task under analysis and the length of an
        interval in which the interference is supposed to be bounded,
        respectively. These are quite intuitive; so, we will not
        explain them in more detail. However, the second parameter
        deserves more thoughtful explanation.

        The second parameter of [IBF] allows one to organize a case
        analysis over a set of values that are known only during the
        computation. For example, the most common parameter is the
        relative arrival time [A] of a job (of a task under
        analysis). Strictly speaking, [A] is now known at a time of
        computing a fixpoint; however, one can consider a set of [A]
        that covers all the relevant cases There can be other valid
        properties such as "a time instant when a job under analysis
        has received enough service to become non-preemptive." *)
    Variable IBF : Task -> duration -> duration -> work.

    (** To make the second parameter customizable, we introduce a
        predicate [P : Job -> instant -> Prop] that connects the second
        parameter to its semantics. More precisely, consider an
        expression [IBF(tsk, X, delta)], and assume that we
        instantiated [P] as some predicate [P0]. Then, it is assumed
        that [IBF(tsk, X, delta)] bounds interference of a job under
        analysis [j ∈ tsk] if [P0 j X] holds. *)
    Variable P : Job -> nat -> Prop.

    (** Next, let us define this reasoning formally.
        We say that the job interference is bounded by an
        "interference bound function" [IBF] iff for any job [j] of
        task [tsk] the cumulative interference incurred by [j] in the
        sub-interval <<[t1, t1 + delta)>> of busy interval <<[t1,
        t2)>> does not exceed [IBF(tsk, X, delta)], where [X] is a
        constant that satisfies a predefined predicate [P]. *)
    (** Note that according to the definition of an abstract work
        conservation, interference does _not_ include execution of a
        job under analysis itself. Therefore, an interference bound is
        not obliged to take into account the execution of this job. *)
    Definition job_interference_is_bounded_by :=
      (** Consider a job [j] of task [tsk], a busy interval
          <<[t1,t2)>> of [j], and an arbitrary interval <<[t1, t1 + Δ)
          ⊆ [t1, t2)>>.  *)
      forall t1 t2 Δ j,
        arrives_in arr_seq j ->
        job_of_task tsk j ->
        busy_interval j t1 t2 ->
        (** We require the IBF to bound the interference only within
           the interval [t1, t1 + Δ). *)
        t1 + Δ < t2 ->
        (** Next, we require the [IBF] to bound the interference only
            until the job is completed, after which the function can
            behave arbitrarily. *)
        ~~ completed_by sched j (t1 + Δ) ->
        (** And finally, the IBF function might depend not only on the
            length of the interval, but also on a constant [X]
            satisfying predicate [P]. *)
        forall X, P j X -> cumulative_interference j t1 (t1 + Δ) <= IBF tsk X Δ.

  End BusyIntervalProperties.

End AbstractRTADefinitions.
