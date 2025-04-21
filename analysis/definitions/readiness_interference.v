Require Export prosa.model.priority.definitions.

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

End Definitions.
