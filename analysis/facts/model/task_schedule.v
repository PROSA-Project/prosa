Require Export prosa.model.task.concept.
Require Export prosa.analysis.definitions.task_schedule.
Require Export prosa.analysis.facts.behavior.service.
Require Export prosa.analysis.facts.model.scheduled.

(** In this file we provide basic properties related to schedule of a task. *)
Section TaskSchedule.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** Consider any valid arrival sequence of such jobs ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.

  (** ... and let [sched] be any corresponding uni-processor schedule. *)
  Context {PState : ProcessorState Job}.
  Hypothesis H_uniproc : uniprocessor_model PState.
  Variable sched : schedule PState.

  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

  (** Let [tsk] be any task. *)
  Variable tsk : Task.

  (** First, we show that a task is served at time [t], then the task
      is scheduled at time [t]. *)
  Lemma task_served_task_scheduled :
    forall t,
      task_served_at arr_seq sched tsk t ->
      task_scheduled_at arr_seq sched tsk t.
  Proof.
    move => t; apply contra => /eqP SCHED.
    by rewrite /served_jobs_of_task_at SCHED.
  Qed.

  (** Next, we show that, under ideal-progress assumption, the notion
      of task served coincides with the notion of task scheduled. *)
  Lemma task_served_eq_task_scheduled :
    ideal_progress_proc_model PState ->
    forall t,
      task_served_at arr_seq sched tsk t = task_scheduled_at arr_seq sched tsk t.
  Proof.
    move=> IDEAL t; apply/idP/idP; first by move => SERV; apply task_served_task_scheduled.
    rewrite /task_scheduled_at -has_filter => /hasP [j SCHED TSK].
    rewrite -[task_served_at _ _ _ _]has_filter; apply/hasP; exists j.
    - by rewrite mem_filter; apply/andP; split.
    - by apply IDEAL; rewrite scheduled_jobs_at_iff in SCHED.
  Qed.

  (** We note that if the processor is idle at time [t], then no task
      is scheduled. *)
  Lemma no_task_scheduled_when_idle :
    forall t,
      is_idle arr_seq sched t ->
      ~~ task_scheduled_at arr_seq sched tsk t.
  Proof.
    move=> t IDLE.
    rewrite -[task_scheduled_at _ _ _ _]has_filter.
    rewrite -all_predC.
    apply/allP => j SCHED; exfalso.
    rewrite scheduled_jobs_at_iff in SCHED => //.
    eapply not_scheduled_when_idle in IDLE => //.
    exact: (negP IDLE).
  Qed.

  (** Similarly, if the processor is idle at time [t], then no task is
      served. *)
  Lemma no_task_served_when_idle :
    forall t,
      is_idle arr_seq sched t ->
      ~~ task_served_at arr_seq sched tsk t.
  Proof.
    move=> t IDLE.
    apply no_task_scheduled_when_idle in IDLE.
    by move: IDLE; apply contra, task_served_task_scheduled.
  Qed.

  (** We show that if a job is scheduled at time [t], then
      [task_scheduled_at tsk t] is equal to [job_of_task tsk j]. In
      other words, any occurrence of [task_scheduled_at] can be
      replaced with [job_of_task]. *)
  Lemma job_of_scheduled_task :
    forall j t,
      scheduled_at sched j t ->
      task_scheduled_at arr_seq sched tsk t = job_of_task tsk j.
  Proof.
    move=> j t.
    rewrite -(scheduled_jobs_at_scheduled_at arr_seq) //.
    rewrite /task_scheduled_at /scheduled_jobs_of_task_at => /eqP -> //=.
    by case: (job_of_task _ _).
  Qed.

  (** As a corollary, we show that if a job of task [tsk] is scheduled
      at time [t], then task [tsk] is scheduled at time [t]. *)
  Corollary job_of_task_scheduled :
    forall j t,
      job_of_task tsk j ->
      scheduled_at sched j t ->
      task_scheduled_at arr_seq sched tsk t.
  Proof.
    by move=> j t TSK SCHED; rewrite (job_of_scheduled_task j) => //.
  Qed.

  (** And vice versa, if no job of task [tsk] is scheduled at time
      [t], then task [tsk] is not scheduled at time [t]. *)
  Corollary job_of_other_task_scheduled :
    forall j t,
      ~~ job_of_task tsk j ->
      scheduled_at sched j t ->
      ~~ task_scheduled_at arr_seq sched tsk t.
  Proof.
    by move=> j t TSK SCHED; rewrite (job_of_scheduled_task j) => //.
  Qed.

  (** Similarly, we show that if no job of task [tsk] is scheduled at
      time [t], then task [tsk] is not served at time [t]. *)
  Corollary job_of_other_task_scheduled' :
    forall j t,
      ~~ job_of_task tsk j ->
      scheduled_at sched j t ->
      ~~ task_served_at arr_seq sched tsk t.
  Proof.
    move=> j t TSK SCHED.
    apply: (contra (task_served_task_scheduled _)).
    exact: job_of_other_task_scheduled.
  Qed.

  (** Lastly, if a job of task [tsk] is scheduled at time [t] but
      receives no service, then task [tsk] is not served at time
      [t]. *)
  Corollary job_of_task_not_served :
    forall j t,
      scheduled_at sched j t ->
      job_of_task tsk j ->
      service_at sched j t = 0 ->
      ~~ task_served_at arr_seq sched tsk t.
  Proof.
    move=> j t.
    rewrite -(scheduled_jobs_at_scheduled_at arr_seq) //.
    rewrite /task_scheduled_at /task_served_at /served_jobs_of_task_at /scheduled_jobs_of_task_at => /eqP -> //= -> //=.
    by rewrite /receives_service_at => ->.
  Qed.

  (** In the following section, we prove a rewriting rule between the
      predicate [task_served_at] and [job_of_task]. *)
  Section SomeJobIsScheduled.

    (** Assume that the processor is fully supply-consuming. *)
    Hypothesis H_consumed_supply_proc_model : fully_consuming_proc_model PState.

    (** Consider a time instant [t] ... *)
    Variable t : instant.

    (** ... and assume that there is supply at [t]. *)
    Hypothesis H_supply : has_supply sched t.

    (** Consider jobs [j] and [j'] ([j'] is not necessarily distinct
        from job [j]). Assume that [j] is scheduled at time [t]. *)
    Variable j : Job.
    Hypothesis H_sched : scheduled_at sched j t.

    (** Then the predicate [task_served_at] is equal to the predicate
        [job_of_task]. *)
    Lemma task_served_at_eq_job_of_task :
      task_served_at arr_seq sched tsk t = job_of_task tsk j.
    Proof.
      have SERV : receives_service_at sched j t by apply ideal_progress_inside_supplies.
      rewrite /task_served_at /served_jobs_of_task_at /scheduled_jobs_of_task_at.
      move: (H_sched) => SCHED.
      erewrite <-scheduled_jobs_at_scheduled_at in SCHED => //.
      move: SCHED => /eqP ->.
      have [TSK|/negPf NTSK] := boolP (job_of_task tsk j).
      { by rewrite //= TSK //= SERV. }
      by rewrite //= NTSK //=.
    Qed.

  End SomeJobIsScheduled.

End TaskSchedule.
