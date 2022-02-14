Require Export prosa.analysis.facts.periodic.arrival_times.
Require Export prosa.analysis.facts.periodic.task_arrivals_size.
Require Export prosa.model.task.concept.
Require Export prosa.analysis.facts.hyperperiod.

(** In this file we define a new function for job costs 
    in an observation interval and prove its validity. *)
Section ValidJobCostsShifted.

  (** Consider any type of periodic tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskOffset Task}.
  Context `{PeriodicModel Task}.
  Context `{TaskCost Task}.

  (** ... and any type of jobs. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  Context `{JobDeadline Job}.
  
  (** Consider a consistent arrival sequence with non-duplicate arrivals. *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
  Hypothesis H_uniq_arr_seq: arrival_sequence_uniq arr_seq.

  (** Furthermore, assume that arrivals have valid job costs. *) 
  Hypothesis H_arrivals_have_valid_job_costs: arrivals_have_valid_job_costs arr_seq.
  
  (** Consider a periodic task set [ts] such that all tasks in
      [ts] have valid periods and offsets. *)
  Variable ts : TaskSet Task.
  Hypothesis H_periodic_taskset: taskset_respects_periodic_task_model arr_seq ts.
  Hypothesis H_valid_periods_in_taskset: valid_periods ts. 
  Hypothesis H_valid_offsets_in_taskset: valid_offsets arr_seq ts.
  
  (** Consider a job [j] that stems from the arrival sequence. *)
  Variable j : Job.
  Hypothesis H_j_from_arrival_sequence: arrives_in arr_seq j.

  (** Let [O_max] denote the maximum task offset of all tasks in [ts] ... *)
  Let O_max := max_task_offset ts.
  (** ... and let [HP] denote the hyperperiod of all tasks in [ts]. *)
  Let HP := hyperperiod ts.

  (** We now define a new function for job costs in the observation interval. *)

  (** Given that job [j] arrives after [O_max], the cost of a job [j'] 
   that arrives in the interval <<[O_max + HP, O_max + 2HP)>> is defined to 
   be the same as the job cost of its corresponding job in [j]'s hyperperiod. *)
  Definition job_costs_shifted (j' : Job) :=
    if (job_arrival j >= O_max) && (O_max + HP <= job_arrival j' < O_max + 2 * HP) then
      job_cost (corresponding_job_in_hyperperiod ts arr_seq j' (starting_instant_of_corresponding_hyperperiod ts j) (job_task j'))
    else job_cost j'.
  
  (** Assume that we have an infinite sequence of jobs. *)
  Hypothesis H_infinite_jobs: infinite_jobs arr_seq. 

  (** Assume all jobs in the arrival sequence [arr_seq] belong to some task 
   in [ts]. *)
  Hypothesis H_jobs_from_taskset: all_jobs_from_taskset arr_seq ts.

  (** We assign the job costs as defined by the [job_costs_shifted] function. *)
  Instance job_costs_in_oi : JobCost Job :=
    job_costs_shifted.

  (** We show that the [job_costs_shifted] function is valid. *)
  Lemma job_costs_shifted_valid: arrivals_have_valid_job_costs arr_seq.
  Proof.
    rewrite /arrivals_have_valid_job_costs /valid_job_cost.
    intros j' ARR.
    unfold job_cost; rewrite /job_costs_in_oi /job_costs_shifted.
    destruct (leqP O_max (job_arrival j)) as [A | B].
    destruct (leqP (O_max + HP) (job_arrival j')) as [NEQ | NEQ].
    destruct (leqP (O_max + 2 * HP) (job_arrival j')) as [LT | LT].
    all : try by apply H_arrivals_have_valid_job_costs => //.
    simpl.
    specialize (corresponding_jobs_have_same_task arr_seq ts j' j) => TSK.
    rewrite -[in X in _ <= task_cost X]TSK.
    have IN : job_task j' \in ts by apply H_jobs_from_taskset.
    apply H_arrivals_have_valid_job_costs, corresponding_job_arrives => //.
    + now apply H_valid_offsets_in_taskset.
    + now apply H_valid_periods_in_taskset.  
    + now apply H_periodic_taskset.
    + now lia.
  Qed.

End ValidJobCostsShifted.
