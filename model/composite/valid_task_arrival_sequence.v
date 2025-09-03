Require Export prosa.model.task.arrivals.
Require Export prosa.model.task.arrival.curves.

(** * Valid Task Arrival Sequences *)

(** In this section, we define what it means for an arrival sequence
    to be valid with respect to a given task set. *)
Section ValidTaskArrivalSequence.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.
  Context `{MaxArrivals Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.

  (** Let [ts] be an arbitrary task set... *)
  Variable ts : seq Task.

  (** ... and consider any job arrival sequence. *)
  Variable arr_seq : arrival_sequence Job.

  (** We say that an arrival sequence is a "valid task arrival sequence"
      if the following conditions hold:
        - it is a valid arrival sequence,
        - all jobs have valid costs,
        - all jobs come from the given task set [ts],
        - the number of arrivals respects each task’s maximum-arrival bound,
        - and the task set admits a valid arrival curve [max_arrivals]. *)
  Definition valid_task_arrival_sequence :=
    valid_arrival_sequence arr_seq
    /\ arrivals_have_valid_job_costs arr_seq
    /\ all_jobs_from_taskset arr_seq ts
    /\ taskset_respects_max_arrivals arr_seq ts
    /\ valid_taskset_arrival_curve ts max_arrivals.

  (** Next, we prove several trivial lemmas to use in automation. *)

  Lemma valid_task_arrival_sequence_valid_arrivals :
    valid_task_arrival_sequence -> valid_arrival_sequence arr_seq.
  Proof. by move=> //= []. Qed.

  Lemma valid_task_arrival_sequence_valid_costs :
    valid_task_arrival_sequence -> arrivals_have_valid_job_costs arr_seq.
  Proof. by move=> [_ []]. Qed.

  Lemma valid_task_arrival_sequence_from_taskset :
    valid_task_arrival_sequence -> all_jobs_from_taskset arr_seq ts.
  Proof. by move=> [_ [_ []]]. Qed.

  Lemma valid_task_arrival_sequence_respects_max :
    valid_task_arrival_sequence -> taskset_respects_max_arrivals arr_seq ts.
  Proof. by move=> [_ [_ [_ []]]]. Qed.

  Lemma valid_task_arrival_sequence_valid_curve :
    valid_task_arrival_sequence -> valid_taskset_arrival_curve ts max_arrivals.
  Proof. by move=> [_ [_ [_ []]]]. Qed.

End ValidTaskArrivalSequence.

(** We add the above lemmas into a "Hint Database" basic_rt_facts, so Coq
    will be able to apply them automatically. *)
Hint Resolve
     valid_task_arrival_sequence_valid_arrivals
     valid_task_arrival_sequence_valid_costs
     valid_task_arrival_sequence_from_taskset
     valid_task_arrival_sequence_respects_max
     valid_task_arrival_sequence_valid_curve
  : basic_rt_facts.
