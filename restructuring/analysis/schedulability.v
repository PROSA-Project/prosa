From rt.restructuring.behavior Require Export schedule facts.completion.
From rt.restructuring.model Require Export task.
From rt.util Require Export seqset.

Section Task.
  Context {Task : TaskType}.
  Context {Job: JobType}.

  Context `{JobArrival Job} `{JobCost Job} `{JobTask Job Task}.
  Context `{JobDeadline Job}.

  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (* Consider any job arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.

  (* ...and any schedule of these jobs. *)
  Variable sched: schedule PState.

  (* Let tsk be any task that is to be analyzed. *)
  Variable tsk: Task.

  (* Then, we say that R is a response-time bound of tsk in this schedule ... *)
  Variable R: duration.

  (* ... iff any job j of tsk in this arrival sequence has
         completed by (job_arrival j + R). *)
  Definition task_response_time_bound :=
    forall j,
      arrives_in arr_seq j ->
      job_task j = tsk ->
      job_response_time_bound sched j R.

  (* We say that a task is schedulable if all its jobs meet their deadline *)
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

  (* Consider any job arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.

  (* ...and any schedule of these jobs. *)
  Variable sched: schedule PState.

  (* We say that a task set is schedulable if all its tasks are schedulable *)
  Definition schedulable_taskset :=
    forall tsk, tsk \in ts -> schedulable_task arr_seq sched tsk.
End TaskSet.

Section Schedulability.
  (* We can infer schedulability from a response-time bound of a task. *)

  Context {Task : TaskType}.
  Context {Job: JobType}.

  Context `{TaskDeadline Task}.
  Context `{JobArrival Job} `{JobCost Job} `{JobTask Job Task}.

  Context {PState : Type}.
  Context `{ProcessorState Job PState}.

  (* Consider any job arrival sequence... *)
  Variable arr_seq: arrival_sequence Job.

  (* ...and any schedule of these jobs. *)
  Variable sched: schedule PState.

  (* Assume that jobs don't execute after completion. *)
  Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.

  (* Let tsk be any task that is to be analyzed. *)
  Variable tsk: Task.

  (* Given  a response-time bound of tsk in this schedule no larger than its deadline, ... *)
  Variable R: duration.

  Hypothesis H_R_le_deadline: R <= task_deadline tsk.
  Hypothesis H_response_time_bounded: task_response_time_bound arr_seq sched tsk R.

  (* ...then tsk is schedulable. *)
  Lemma schedulability_from_response_time_bound:
    schedulable_task arr_seq sched tsk.
  Proof.
    intros j ARRj JOBtsk.
    rewrite /job_meets_deadline.
    apply completion_monotonic with (t := job_arrival j + R);
    [ | by apply H_response_time_bounded].
    rewrite /job_deadline leq_add2l JOBtsk.
    by rewrite (leq_trans H_R_le_deadline).
  Qed.

End Schedulability.
