Require Export rt.analysis.facts.behavior.completion.
Require Import rt.model.task.absolute_deadline.

Section Task.
  Context {Task : TaskType}.
  Context {Job: JobType}.

  Context `{JobArrival Job} `{JobCost Job} `{JobTask Job Task}.
  Context `{JobDeadline Job}.

  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any job arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.

  (** ...and any schedule of these jobs. *)
  Variable sched: schedule PState.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk: Task.

  (** Then, we say that R is a response-time bound of [tsk] in this schedule ... *)
  Variable R: duration.

  (** ... iff any job [j] of [tsk] in this arrival sequence has
         completed by [job_arrival j + R]. *)
  Definition task_response_time_bound :=
    forall j,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_response_time_bound sched j R.

  (** We say that a task is schedulable if all its jobs meet their deadline *)
  Definition schedulable_task :=
    forall j,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_meets_deadline sched j.
End Task.

Section TaskSet.
  Context {Task : TaskType}.
  Context {Job: JobType}.

  Context `{JobArrival Job} `{JobCost Job} `{JobTask Job Task}.
  Context `{JobDeadline Job}.

  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  Variable ts : {set Task}.

  (** Consider any job arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.

  (** ...and any schedule of these jobs. *)
  Variable sched: schedule PState.

  (** We say that a task set is schedulable if all its tasks are schedulable *)
  Definition schedulable_taskset :=
    forall tsk, tsk \in ts -> schedulable_task arr_seq sched tsk.
End TaskSet.

Section Schedulability.
  (** We can infer schedulability from a response-time bound of a task. *)

  Context {Task : TaskType}.
  Context {Job: JobType}.

  Context `{TaskDeadline Task}.
  Context `{JobArrival Job} `{JobCost Job} `{JobTask Job Task}.

  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (** Consider any job arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.

  (** ...and any schedule of these jobs. *)
  Variable sched: schedule PState.

  (** Assume that jobs don't execute after completion. *)
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (** Let [tsk] be any task that is to be analyzed. *)
  Variable tsk: Task.

  (** Given  a response-time bound of [tsk] in this schedule no larger than its deadline, ... *)
  Variable R: duration.

  Hypothesis H_R_le_deadline: R <= task_deadline tsk.
  Hypothesis H_response_time_bounded: task_response_time_bound arr_seq sched tsk R.

  (** ...then [tsk] is schedulable. *)
  Lemma schedulability_from_response_time_bound:
    schedulable_task arr_seq sched tsk.
  Proof.
    intros j ARRj JOBtsk.
    rewrite /job_meets_deadline.
    apply completion_monotonic with (t := job_arrival j + R);
      [ | by apply H_response_time_bounded].
    rewrite /job_deadline leq_add2l JOBtsk.
      by erewrite leq_trans; eauto.
  Qed.

End Schedulability.


(** We further define two notions of "all deadlines met" that do not
    depend on a task abstraction: one w.r.t. all scheduled jobs in a
    given schedule and one w.r.t. all jobs that arrive in a given
    arrival sequence. *)
Section AllDeadlinesMet.

  (** Consider any given type of jobs... *)
  Context {Job : JobType} `{JobCost Job} `{JobDeadline Job} `{JobArrival Job}.

  (** ... any given type of processor states. *)
  Context {PState: eqType}.
  Context `{ProcessorState Job PState}.

  (** We say that all deadlines are met if every job scheduled at some
     point in the schedule meets its deadline. Note that this is a
     relatively weak definition since an "empty" schedule that is idle
     at all times trivially satisfies it (since the definition does
     not require any kind of work conservation). *)
  Definition all_deadlines_met (sched: schedule PState) :=
    forall j t,
      scheduled_at sched j t ->
      job_meets_deadline sched j.

  (** To augment the preceding definition, we also define an alternate
     notion of "all deadlines met" based on all jobs included in a
     given arrival sequence.  *)
  Section DeadlinesOfArrivals.

    (** Given an arbitrary job arrival sequence ... *)
    Variable arr_seq: arrival_sequence Job.  

    (** ... we say that all arrivals meet their deadline if every job
       that arrives at some point in time meets its deadline. Note
       that this definition does not preclude the existence of jobs in
       a schedule that miss their deadline (e.g., if they stem from
       another arrival sequence). *)
    Definition all_deadlines_of_arrivals_met (sched: schedule PState) :=
      forall j,
        arrives_in arr_seq j ->
        job_meets_deadline sched j.

  End DeadlinesOfArrivals.

  (** We observe that the latter definition, assuming a schedule in
     which all jobs come from the arrival sequence, implies the former
     definition. *)
  Lemma all_deadlines_met_in_valid_schedule:
    forall arr_seq sched,
      jobs_come_from_arrival_sequence sched arr_seq ->
      all_deadlines_of_arrivals_met arr_seq sched ->
      all_deadlines_met sched.
  Proof.
    move=> arr_seq sched FROM_ARR DL_ARR_MET j t SCHED.
    apply DL_ARR_MET.
    by apply (FROM_ARR _ t).
  Qed.
    
End AllDeadlinesMet.
