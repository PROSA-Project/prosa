Require Export prosa.model.task.arrival.curves.

(** * Arrival Curve Propagation *)

Section ArrivalCurvePropagation.

  (** In the following, consider two kinds of tasks, [Task1] and [Task2]. We
      seek to relate the arrivals of jobs of the [Task1] kind to the arrivals of
      jobs of the [Task2] kind. In particular, we will derive an arrival curve
      for the second kind from an arrival curve for the first kind under the
      assumption that job arrivals are related in time within some known delay
      bound. *)
  Context {Task1 Task2 : TaskType}.

  (** Consider the corresponding jobs and their arrival times. *)
  Context {Job1 Job2 : JobType}
          `{JobTask Job1 Task1} `{JobTask Job2 Task2}
          `(JobArrival Job1) `(JobArrival Job2).

  (** Suppose there is a mapping of jobs (respectively, tasks) of the second
      kind to jobs (respectively, tasks) of the first kind. For example, this
      could be a "predecessor" or "triggered by" relationship. *)
  Variable job1_of : Job2 -> Job1.
  Variable task1_of : Task2 -> Task1.

 (** Furthermore, suppose that the arrival time of any job of the second kind
     occurs within a bounded time of the arrival of the corresponding job of the
     first kind. *)
  Variable delay_bound : Task2 -> duration.

  (** ** Propagation Validity *)

  (** Before we continue, let us note under which assumptions delay propagation
      works. *)

  (** First, the task- and job-level mappings of course need to agree. *)
  Let consistent_task_job_mapping :=
    forall j2 : Job2,
      job_task (job1_of j2) = task1_of (job_task j2).

  (** Second, the delay bound must indeed bound the separation between any two
      jobs (for a given task set). *)
  Let bounded_arrival_delay (ts : seq Task2) :=
    forall (j2 : Job2),
      (job_task j2) \in ts ->
      job_arrival j2 <= job_arrival (job1_of j2) + delay_bound (job_task j2).

  (** In summary, a delay propagation mapping is valid for a given task set [ts]
      if it both is structurally consistent ([consistent_task_job_mapping]) and
      ensures bounded arrival delay ([bounded_arrival_delay]). *)
  Definition valid_delay_propagation_mapping (ts : seq Task2) :=
    consistent_task_job_mapping /\ bounded_arrival_delay ts.

  (** ** Derived Arrival Curve *)

  (** Under the above assumptions, given an arrival curve for the first kind of
      tasks ... *)
  Context `{MaxArrivals Task1}.

  (** ... we define an arrival curve for the second kind of tasks by "enlarging"
      the analysis window by [delay_bound] ... *)
  Let propagated_max_arrivals (tsk2 : Task2) (delta : duration) :=
    if delta is 0 then 0
    else max_arrivals (task1_of tsk2) (delta + delay_bound tsk2).

  (** .. and register this definition with Coq as a type class instance. *)
  #[local]
  Instance propagated_arrival_curve : MaxArrivals Task2 := propagated_max_arrivals.

  (** ** Derived Arrival Sequence *)

  (** In a similar fashion, we next derive an arrival sequence of
      jobs of the second kind. *)

  (** To this end, suppose we are given an arrival sequence for jobs of the
      first kind. *)
  Variable arr_seq1 : arrival_sequence Job1.

  (** Furthermore, suppose we are given the inverse mapping of jobs, i.e., a
      function that maps each job in the arrival sequence to the corresponding
      job(s) of the second kind, ...  *)
  Variable job2_of : Job1 -> seq Job2.

  (** ... and a function mapping each job of the second kind to the _exact_
      delay that it incurs (relative to the arrival of its corresponding job of
      the first kind). *)
  Variable arrival_delay : Job2 -> duration.

  (** Based on this information, we define the resulting arrival sequence of
      jobs of the second kind. *)
  Definition propagated_arrival_sequence t :=
    let all := [seq job2_of j | j <- arrivals_up_to arr_seq1 t] in
    [seq j2 <- flatten all | job_arrival (job1_of j2) +  arrival_delay j2 == t].

  (** The derived arrival sequence makes sense under the following assumptions: *)

  (** First, [job1_of] and [job2_of] must agree. *)
  Let consistent_job_mapping :=
    forall j1 j2,
      j2 \in job2_of j1 <-> job1_of j2 = j1.

  (** Second, the inverse mapping must be a proper set for each job in [arr_seq1]. *)
  Definition job_mapping_uniq :=
    forall j1,
      arrives_in arr_seq1 j1 -> uniq (job2_of j1).

  (** Third, the claimed bound on arrival delay must indeed bound all delays
      encountered. *)
  Let valid_arrival_delay (ts : seq Task2) :=
    forall j2,
      (job_task j2) \in ts ->
      arrives_in arr_seq1 (job1_of j2) ->
      arrival_delay j2 <= delay_bound (job_task j2).

  (** Fourth, the arrival delay must indeed be the difference between the arrival
      times of related jobs. *)
  Let valid_job_arrival_def :=
    forall j2,
      job_arrival j2 = job_arrival (job1_of j2) + arrival_delay j2.

  (** In summary, the derived arrival sequence is valid for a given task set
      [ts] if all four above conditions are met. *)
  Definition valid_arr_seq_propagation_mapping (ts : seq Task2) :=
    [/\ consistent_job_mapping,job_mapping_uniq, valid_arrival_delay ts
                                                & valid_job_arrival_def].

End ArrivalCurvePropagation.

(** * Release Jitter Propagation *)

(** Under some scheduling policies, notably fixed-priority scheduling, it can be
    useful to "fold" release jitter into the arrival curve. This can be achieved
    in terms of the above-defined propagation operation. *)

(** To this end, recall the definition of release jitter. *)
Require Export prosa.model.task.jitter.

(** In the following, we instantiate the above-defined delay propagation for
    release jitter. *)

Section ReleaseJitterPropagation.

  (** Consider any type of tasks described by arrival curves ... *)
  Context {Task : TaskType} `{MaxArrivals Task}.

  (** ... and the corresponding jobs. *)
  Context {Job : JobType} `{JobTask Job Task}.

  (** Let [original_arrival] denote each job's _actual_ arrival time. *)
  Context {original_arrival : JobArrival Job}.

  (** Suppose the jobs are affected by bounded release jitter. *)
  Context `{TaskJitter Task} `{JobJitter Job}.

  (** Recall that a job's _release time_ is the first time after its arrival
      when it becomes ready for execution. *)
  Let job_release j := job_arrival j + job_jitter j.

  (** If we _reinterpret_ release times as the _effective_ arrival times ... *)
  #[local]
  Instance release_as_arrival : JobArrival Job := job_release.

  (** ... then we obtain a valid "arrival" (= release) curve for this
      reinterpretation by propagating the original arrival curve while
      accounting for the jitter bounds. *)
  #[local]
  Instance release_curve : MaxArrivals Task :=
    propagated_arrival_curve id task_jitter.

  (** By construction, this meets the delay-propagation validity
      requirement. *)
  Remark jitter_delay_mapping_valid :
    forall ts,
      valid_jitter_bounds ts ->
      valid_delay_propagation_mapping
        original_arrival release_as_arrival
        id id task_jitter ts.
  Proof.
    move=> ts VALJIT; split => j // IN.
    rewrite {1}/job_arrival /release_as_arrival /job_release.
    exact/leq_add/VALJIT.
  Qed.

  (** Similarly, the induced "arrival" (= release) sequence ... *)
  Definition release_sequence (arr_seq : arrival_sequence Job) :=
    propagated_arrival_sequence original_arrival id arr_seq (fun j => [:: j]) job_jitter.

  (** ... meets all requirements of the generic delay-propagation
      construction. *)
  Remark jitter_arr_seq_mapping_valid :
    forall ts arr_seq,
      valid_jitter_bounds ts ->
      valid_arr_seq_propagation_mapping
        original_arrival release_as_arrival
        id task_jitter arr_seq (fun j => [:: j]) job_jitter ts.
  Proof.
    move=> ts arr_seq VALJIT; split => //.
    - by move=> j1 j2; split => [|->]; rewrite mem_seq1 // => /eqP.
    - by move=> j2 IN ARR; exact/VALJIT.
  Qed.

End ReleaseJitterPropagation.
