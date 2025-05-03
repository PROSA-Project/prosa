Require Export prosa.model.priority.definitions.
Require Export prosa.analysis.abstract.definitions.

Section Definitions.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  Context `{PState : ProcessorState Job}.

  Context `{!JobReady Job PState}.

  Variable arr_seq : arrival_sequence Job.

  Variable sched : schedule PState.

  Context {JLFP : JLFP_policy Job}.

  Variable j : Job.

  Definition no_hep_ready (t : instant) :=
    all (fun j' => ~~ job_ready sched j' t) 
      [seq j' <- arrivals_up_to arr_seq t | pending sched j' t && hep_job j' j].

  Definition cumulative_readiness_interference (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) no_hep_ready t.

End Definitions.

Section Bound.
  Context {Task : TaskType}.

  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobTask Job Task}.

  Context `{PState : ProcessorState Job}.

  Context `{!JobReady Job PState}.

  Variable arr_seq : arrival_sequence Job.

  Variable sched : schedule PState.

  Context {JLFP : JLFP_policy Job}.

  Context `{Interference Job}.
  Context `{InterferingWorkload Job}.

  Variable tsk : Task.

  Let quiet_time_ab := quiet_time sched.

  Definition readiness_interference_is_bounded (B : duration) :=
    forall j t1 Δ,
      arrives_in arr_seq j ->
      job_of_task tsk j ->
      quiet_time_ab j t1  ->
      cumulative_readiness_interference arr_seq sched j t1 (t1 + Δ) <= B.

End Bound.
