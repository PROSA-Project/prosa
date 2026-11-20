Require Export prosa.behavior.execution.
Require Export prosa.util.all.

(** * Properties of Valid Schedules of an Arrival Sequence *)

Section ValidScheduleOfArrivals.

  (** Consider jobs with arrival times and costs on any processor model. *)
  Context {Job : JobType} `{JobArrival Job} `{JobCost Job}.
  Context {PState : ProcessorState Job}.

  (** Consider a schedule of an arrival sequence. *)
  Variable sched : schedule PState.
  Variable arr_seq : arrival_sequence Job.

  (** Schedule validity requires scheduled jobs to belong to the arrival sequence. *)
  Lemma valid_schedule_of_arrivals_jobs_come_from_arrival_sequence :
    valid_schedule_of_arrivals sched arr_seq ->
    jobs_come_from_arrival_sequence sched arr_seq.
  Proof. by move=> []. Qed.

  (** Schedule validity excludes execution before arrival. *)
  Lemma valid_schedule_of_arrivals_implies_jobs_must_arrive_to_execute :
    valid_schedule_of_arrivals sched arr_seq -> jobs_must_arrive_to_execute sched.
  Proof. by move=> [_ []]. Qed.

  (** Schedule validity excludes execution after completion. *)
  Lemma valid_schedule_of_arrivals_implies_completed_jobs_dont_execute :
    valid_schedule_of_arrivals sched arr_seq -> completed_jobs_dont_execute sched.
  Proof. by move=> [_ []]. Qed.

  (** In particular, any job that executes is pending. *)
  Lemma valid_schedule_of_arrivals_implies_scheduled_jobs_pending :
    valid_schedule_of_arrivals sched arr_seq ->
    forall j t,
      scheduled_at sched j t ->
      pending sched j t.
  Proof.
    move=> [_ [ARR COMP]] j t SCHED.
    apply/andP; split; first exact: ARR.
    by rewrite /completed_by -ltnNge; apply: COMP.
  Qed.

End ValidScheduleOfArrivals.

(** Make the execution constraints available to basic proof automation. *)
Global Hint Resolve
       valid_schedule_of_arrivals_jobs_come_from_arrival_sequence
       valid_schedule_of_arrivals_implies_jobs_must_arrive_to_execute
       valid_schedule_of_arrivals_implies_completed_jobs_dont_execute
       valid_schedule_of_arrivals_implies_scheduled_jobs_pending
  : basic_rt_facts.
